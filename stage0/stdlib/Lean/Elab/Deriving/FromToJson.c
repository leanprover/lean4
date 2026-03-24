// Lean compiler output
// Module: Lean.Elab.Deriving.FromToJson
// Imports: public import Lean.Elab.Deriving.Basic public import Lean.Elab.Deriving.Util
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInductiveApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ToJson"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__1_value),LEAN_SCALAR_PTR_LITERAL(59, 61, 164, 230, 181, 158, 5, 186)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "FromJson"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 129, 161, 88, 112, 64, 72, 138)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__5_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "json"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__9_value),LEAN_SCALAR_PTR_LITERAL(69, 242, 190, 241, 110, 39, 195, 20)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__11_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Json"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__9_value),LEAN_SCALAR_PTR_LITERAL(97, 53, 111, 111, 136, 165, 95, 9)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__13_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__15 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__15_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__16 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value),LEAN_SCALAR_PTR_LITERAL(190, 18, 71, 130, 82, 255, 111, 18)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__18 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__19 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__20 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__19_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__21 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__22 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__20_value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__22_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__23 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__23_value;
static lean_once_cell_t l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkJsonField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid json field name "};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkJsonField___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkJsonField___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Deriving_FromToJson_mkJsonField___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_FromToJson_mkJsonField___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkJsonField(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkJsonField___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term[_]"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 147, 168, 74, 195, 98, 232, 161)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FromToJson"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__14_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__14_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__14_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(62, 248, 136, 255, 117, 192, 201, 101)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__14_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__16_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__17_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__17_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__19_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__20_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__22_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__22_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__22_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__23_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__21_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__24_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__25_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__20_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__25_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__26_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__18_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__26_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__27_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__15_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__27_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__28_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__30_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__30_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toJson"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__32_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(112, 200, 227, 76, 90, 242, 6, 135)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__1_value),LEAN_SCALAR_PTR_LITERAL(59, 61, 164, 230, 181, 158, 5, 186)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__35_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(240, 112, 235, 135, 88, 35, 83, 81)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__35_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__36_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__37_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__38_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__38_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__40 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__40_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__40_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__42 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__42_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "opt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__44 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__44_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__45;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__44_value),LEAN_SCALAR_PTR_LITERAL(90, 237, 191, 26, 214, 234, 184, 145)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__46 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__46_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__47_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__44_value),LEAN_SCALAR_PTR_LITERAL(118, 32, 40, 211, 171, 119, 108, 21)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__47 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__47_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__48 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__48_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__49 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__49_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_<|_"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 38, 96, 140, 215, 46, 31, 82)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mkObj"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__2_value),LEAN_SCALAR_PTR_LITERAL(173, 3, 159, 142, 30, 42, 60, 15)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__2_value),LEAN_SCALAR_PTR_LITERAL(249, 119, 229, 103, 93, 90, 238, 17)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__7_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "<|"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__8_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "List.flatten"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__10;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__11_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "flatten"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__11_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__12_value),LEAN_SCALAR_PTR_LITERAL(237, 107, 55, 162, 201, 219, 91, 244)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__13_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__15 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__16 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__14_value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__16_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__17 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__1_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__2_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__5_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__21_value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__20_value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__1_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__18_value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__15_value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__3_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Json.arr"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__6;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arr"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value),LEAN_SCALAR_PTR_LITERAL(190, 18, 71, 130, 82, 255, 111, 18)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(138, 3, 113, 92, 128, 159, 5, 71)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(231, 213, 164, 217, 10, 137, 183, 122)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__9_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__10_value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__12_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__13_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term#[_,]"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(69, 119, 178, 128, 145, 112, 206, 247)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__15 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__15_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "getObjValAs\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__1;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 254, 156, 248, 14, 254, 53, 146)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 146, 203, 111, 146, 194, 174, 77)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Except.mapError"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__10;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Except"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mapError"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(238, 113, 136, 33, 237, 151, 233, 210)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(78, 82, 246, 42, 96, 35, 111, 130)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__16_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__20_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__21;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(203, 235, 49, 11, 232, 138, 137, 74)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__22_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_++_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__23_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(90, 69, 86, 178, 149, 48, 216, 23)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__24_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toString"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__25_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__26;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(47, 79, 177, 134, 210, 33, 7, 227)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__27_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToString"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__28_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__28_value),LEAN_SCALAR_PTR_LITERAL(30, 202, 174, 203, 16, 186, 159, 168)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__29_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(206, 210, 39, 124, 69, 192, 37, 107)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__29 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__29_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__30_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__31_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "++"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__32_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__33_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__33_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__34_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\".\""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__35_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\": \""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__36_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__2_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__4_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "return"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__6_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__7_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__8_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__9_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__10 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__10_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__11_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__12_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__13_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fromJson\?"};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__1;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 54, 193, 250, 66, 68, 188, 53)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 129, 161, 88, 112, 64, 72, 138)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 88, 105, 59, 236, 221, 213, 61)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__3 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__3_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__5 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__5_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term__[_]_!"};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__6 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__6_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(20, 145, 92, 47, 59, 8, 18, 13)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__7 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__7_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "jsons"};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__8 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__8_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(60, 31, 226, 89, 73, 25, 74, 85)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__10 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__10_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__11 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__11_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__12 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__12_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__13 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Json.parseCtorFields"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__3;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "parseCtorFields"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value),LEAN_SCALAR_PTR_LITERAL(190, 18, 71, 130, 82, 255, 111, 18)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__5_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(125, 67, 110, 155, 4, 21, 244, 27)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__5_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__6_value_aux_1),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(160, 102, 205, 99, 97, 75, 110, 119)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__6_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__7_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__8_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bind"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__9_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__10;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(210, 152, 52, 15, 180, 2, 50, 1)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__11 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__11_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bind"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__12_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(222, 192, 22, 179, 212, 181, 141, 219)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__13_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(155, 214, 105, 100, 54, 209, 36, 192)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__13_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__14 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__14_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__15 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__15_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termReturn"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__16 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__16_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__17_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(199, 245, 184, 22, 191, 152, 219, 48)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__17 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__17_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__18 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__18_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(73, 239, 30, 105, 8, 60, 178, 241)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__20 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__20_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__21 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__21_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__22_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__22 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__22_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__23 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__23_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__24 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__24_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__25 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__25_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(37, 202, 7, 33, 103, 74, 114, 212)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__27 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__27_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__28_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__28 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__28_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__29 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__29_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__30 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__30_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Json.getTag\?"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__3;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getTag\?"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value),LEAN_SCALAR_PTR_LITERAL(190, 18, 71, 130, 82, 255, 111, 18)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 237, 110, 57, 79, 163, 143, 153)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__4_value),LEAN_SCALAR_PTR_LITERAL(26, 233, 182, 93, 166, 19, 81, 50)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__8_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__10;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__9_value),LEAN_SCALAR_PTR_LITERAL(242, 132, 79, 115, 245, 174, 114, 146)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__11_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Except.error"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__13;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(238, 113, 136, 33, 237, 151, 233, 210)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__14_value),LEAN_SCALAR_PTR_LITERAL(132, 223, 190, 30, 132, 210, 24, 71)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__15 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__16 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__15_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__17 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__18 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__16_value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__18_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__19 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__19_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "\"no inductive constructor matched\""};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__20 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__20_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "\"no inductive tag found\""};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__21 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__6_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__8_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__9_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(238, 113, 136, 33, 237, 151, 233, 210)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__1_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__2_value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__4_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__8_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__9_value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__11_value)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__1(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__0_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__0_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(104, 196, 195, 210, 249, 49, 41, 151)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fromJson"};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 186, 66, 232, 156, 87, 3, 205)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__0_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__0_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__0_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__1_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__1_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__1_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__2_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__2_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__2_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__3_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__2_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__3_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__3_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__4_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__3_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__4_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__4_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__5_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__4_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__5_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__5_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__6_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__5_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__6_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__6_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__7_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__6_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(50, 189, 2, 165, 47, 51, 78, 0)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__7_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__7_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__8_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__7_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(51, 68, 99, 34, 115, 76, 88, 121)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__8_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__8_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__9_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__8_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 192, 130, 50, 180, 113, 236, 80)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__9_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__9_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__10_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__9_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(236, 226, 103, 203, 38, 155, 77, 185)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__10_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__10_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__11_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__10_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(206, 106, 162, 80, 250, 232, 85, 229)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__11_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__11_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__12_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__11_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(134, 243, 189, 201, 94, 158, 134, 121)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__12_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__12_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__13_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__13_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__13_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__14_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__12_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__13_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(203, 157, 20, 14, 91, 116, 229, 84)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__14_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__14_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__15_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__15_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__15_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__16_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__14_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__15_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(142, 166, 56, 153, 109, 155, 101, 207)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__16_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__16_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__17_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__16_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 139, 31, 31, 134, 44, 148, 170)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__17_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__17_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__18_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__17_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(57, 244, 122, 20, 148, 37, 25, 147)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__18_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__18_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__19_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__18_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(127, 114, 158, 70, 153, 110, 255, 193)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__19_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__19_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__20_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__19_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 129, 154, 176, 112, 107, 146, 211)}};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__20_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__20_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__21_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__21_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__22_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__22_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__22_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__23_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__23_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__24_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__24_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__24_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__25_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__25_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__26_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__26_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader(lean_object* v_indVal_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__2));
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = l_Lean_Elab_Deriving_mkHeader(v___x_14_, v___x_15_, v_indVal_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___boxed(lean_object* v_indVal_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader(v_indVal_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
return v_res_25_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__9));
v___x_44_ = l_String_toRawSubstring_x27(v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12));
v___x_59_ = l_String_toRawSubstring_x27(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24(void){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Array_mkArray0(lean_box(0));
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader(lean_object* v_indVal_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__1));
v___x_87_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_83_);
v___x_88_ = l_Lean_Elab_Deriving_mkHeader(v___x_86_, v___x_87_, v_indVal_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_136_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_136_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_136_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_136_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v_ref_93_; lean_object* v_quotContext_94_; lean_object* v_currMacroScope_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_binders_118_; lean_object* v_argNames_119_; lean_object* v_targetNames_120_; lean_object* v_targetType_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_135_; 
v_ref_93_ = lean_ctor_get(v_a_83_, 5);
lean_inc(v_ref_93_);
v_quotContext_94_ = lean_ctor_get(v_a_83_, 10);
lean_inc(v_quotContext_94_);
v_currMacroScope_95_ = lean_ctor_get(v_a_83_, 11);
lean_inc(v_currMacroScope_95_);
lean_dec_ref(v_a_83_);
v___x_96_ = 0;
v___x_97_ = l_Lean_SourceInfo_fromRef(v_ref_93_, v___x_96_);
lean_dec(v_ref_93_);
v___x_98_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__5));
v___x_99_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_97_);
v___x_100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_97_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_102_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10);
v___x_103_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__11));
lean_inc(v_currMacroScope_95_);
lean_inc(v_quotContext_94_);
v___x_104_ = l_Lean_addMacroScope(v_quotContext_94_, v___x_103_, v_currMacroScope_95_);
v___x_105_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__15));
lean_inc(v___x_97_);
v___x_106_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_106_, 0, v___x_97_);
lean_ctor_set(v___x_106_, 1, v___x_102_);
lean_ctor_set(v___x_106_, 2, v___x_104_);
lean_ctor_set(v___x_106_, 3, v___x_105_);
lean_inc(v___x_97_);
v___x_107_ = l_Lean_Syntax_node1(v___x_97_, v___x_101_, v___x_106_);
v___x_108_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__16));
lean_inc(v___x_97_);
v___x_109_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_97_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17);
v___x_111_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__18));
v___x_112_ = l_Lean_addMacroScope(v_quotContext_94_, v___x_111_, v_currMacroScope_95_);
v___x_113_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__23));
lean_inc(v___x_97_);
v___x_114_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_114_, 0, v___x_97_);
lean_ctor_set(v___x_114_, 1, v___x_110_);
lean_ctor_set(v___x_114_, 2, v___x_112_);
lean_ctor_set(v___x_114_, 3, v___x_113_);
lean_inc(v___x_97_);
v___x_115_ = l_Lean_Syntax_node2(v___x_97_, v___x_101_, v___x_109_, v___x_114_);
v___x_116_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_97_);
v___x_117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_117_, 0, v___x_97_);
lean_ctor_set(v___x_117_, 1, v___x_101_);
lean_ctor_set(v___x_117_, 2, v___x_116_);
v_binders_118_ = lean_ctor_get(v_a_89_, 0);
v_argNames_119_ = lean_ctor_get(v_a_89_, 1);
v_targetNames_120_ = lean_ctor_get(v_a_89_, 2);
v_targetType_121_ = lean_ctor_get(v_a_89_, 3);
v_isSharedCheck_135_ = !lean_is_exclusive(v_a_89_);
if (v_isSharedCheck_135_ == 0)
{
v___x_123_ = v_a_89_;
v_isShared_124_ = v_isSharedCheck_135_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_targetType_121_);
lean_inc(v_targetNames_120_);
lean_inc(v_argNames_119_);
lean_inc(v_binders_118_);
lean_dec(v_a_89_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_135_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_125_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_97_);
v___x_126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_97_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = l_Lean_Syntax_node5(v___x_97_, v___x_98_, v___x_100_, v___x_107_, v___x_115_, v___x_117_, v___x_126_);
v___x_128_ = lean_array_push(v_binders_118_, v___x_127_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_128_);
v___x_130_ = v___x_123_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_argNames_119_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_targetNames_120_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_targetType_121_);
v___x_130_ = v_reuseFailAlloc_134_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_130_);
v___x_132_ = v___x_91_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_83_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___boxed(lean_object* v_indVal_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader(v_indVal_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
return v_res_145_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_146_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__0);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__1);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
lean_ctor_set(v___x_151_, 2, v___x_150_);
lean_ctor_set(v___x_151_, 3, v___x_149_);
lean_ctor_set(v___x_151_, 4, v___x_149_);
lean_ctor_set(v___x_151_, 5, v___x_149_);
lean_ctor_set(v___x_151_, 6, v___x_149_);
lean_ctor_set(v___x_151_, 7, v___x_149_);
lean_ctor_set(v___x_151_, 8, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_unsigned_to_nat(32u);
v___x_153_ = lean_mk_empty_array_with_capacity(v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_155_ = ((size_t)5ULL);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_unsigned_to_nat(32u);
v___x_158_ = lean_mk_empty_array_with_capacity(v___x_157_);
v___x_159_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__3);
v___x_160_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
lean_ctor_set(v___x_160_, 2, v___x_156_);
lean_ctor_set(v___x_160_, 3, v___x_156_);
lean_ctor_set_usize(v___x_160_, 4, v___x_155_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_box(1);
v___x_162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__4);
v___x_163_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__1);
v___x_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
lean_ctor_set(v___x_164_, 2, v___x_161_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0(lean_object* v_msgData_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; lean_object* v_env_170_; lean_object* v_options_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_169_ = lean_st_ref_get(v___y_167_);
v_env_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc_ref(v_env_170_);
lean_dec(v___x_169_);
v_options_171_ = lean_ctor_get(v___y_166_, 2);
v___x_172_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__2);
v___x_173_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_171_);
v___x_174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_174_, 0, v_env_170_);
lean_ctor_set(v___x_174_, 1, v___x_172_);
lean_ctor_set(v___x_174_, 2, v___x_173_);
lean_ctor_set(v___x_174_, 3, v_options_171_);
v___x_175_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v_msgData_165_);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0___boxed(lean_object* v_msgData_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0(v_msgData_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0___redArg(lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_ref_186_; lean_object* v___x_187_; lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_196_; 
v_ref_186_ = lean_ctor_get(v___y_183_, 5);
v___x_187_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0_spec__0(v_msg_182_, v___y_183_, v___y_184_);
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_196_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_194_; 
lean_inc(v_ref_186_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v_ref_186_);
lean_ctor_set(v___x_192_, 1, v_a_188_);
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 1);
lean_ctor_set(v___x_190_, 0, v___x_192_);
v___x_194_ = v___x_190_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0___redArg___boxed(lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0___redArg(v_msg_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__1(lean_object* v_s_202_, lean_object* v_curr_203_){
_start:
{
lean_object* v_str_204_; lean_object* v_startInclusive_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_str_204_ = lean_ctor_get(v_s_202_, 0);
v_startInclusive_205_ = lean_ctor_get(v_s_202_, 1);
v___x_206_ = lean_nat_add(v_startInclusive_205_, v_curr_203_);
lean_inc(v___x_206_);
lean_inc(v_startInclusive_205_);
lean_inc_ref(v_str_204_);
v___x_207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_207_, 0, v_str_204_);
lean_ctor_set(v___x_207_, 1, v_startInclusive_205_);
lean_ctor_set(v___x_207_, 2, v___x_206_);
v___x_208_ = lean_nat_sub(v___x_206_, v_startInclusive_205_);
lean_dec(v___x_206_);
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_nat_dec_eq(v___x_208_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint32_t v___x_215_; uint32_t v___x_216_; uint8_t v___x_217_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_sub(v___x_208_, v___x_211_);
lean_dec(v___x_208_);
v___x_213_ = l_String_Slice_posLE(v___x_207_, v___x_212_);
v___x_214_ = lean_nat_add(v_startInclusive_205_, v___x_213_);
v___x_215_ = lean_string_utf8_get_fast(v_str_204_, v___x_214_);
lean_dec(v___x_214_);
v___x_216_ = 63;
v___x_217_ = lean_uint32_dec_eq(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v___x_213_);
lean_dec(v_curr_203_);
return v___x_207_;
}
else
{
uint8_t v___x_218_; 
v___x_218_ = lean_nat_dec_lt(v___x_213_, v_curr_203_);
lean_dec(v_curr_203_);
if (v___x_218_ == 0)
{
lean_dec(v___x_213_);
return v___x_207_;
}
else
{
lean_dec_ref(v___x_207_);
v_curr_203_ = v___x_213_;
goto _start;
}
}
}
else
{
lean_dec(v___x_208_);
lean_dec(v_curr_203_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__1___boxed(lean_object* v_s_220_, lean_object* v_curr_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__1(v_s_220_, v_curr_221_);
lean_dec_ref(v_s_220_);
return v_res_222_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkJsonField___closed__1(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkJsonField___closed__0));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkJsonField(lean_object* v_n_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___y_231_; lean_object* v___y_232_; 
if (lean_obj_tag(v_n_226_) == 1)
{
lean_object* v_pre_237_; 
v_pre_237_ = lean_ctor_get(v_n_226_, 0);
if (lean_obj_tag(v_pre_237_) == 0)
{
lean_object* v_str_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v_str_243_; lean_object* v_startInclusive_244_; lean_object* v_endExclusive_245_; lean_object* v_s_u2081_246_; uint8_t v___y_248_; uint8_t v___x_254_; 
v_str_238_ = lean_ctor_get(v_n_226_, 1);
lean_inc_ref(v_str_238_);
lean_dec_ref(v_n_226_);
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_string_utf8_byte_size(v_str_238_);
lean_inc_ref(v_str_238_);
v___x_241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_241_, 0, v_str_238_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_240_);
v___x_242_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__1(v___x_241_, v___x_240_);
lean_dec_ref(v___x_241_);
v_str_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc_ref(v_str_243_);
v_startInclusive_244_ = lean_ctor_get(v___x_242_, 1);
lean_inc(v_startInclusive_244_);
v_endExclusive_245_ = lean_ctor_get(v___x_242_, 2);
lean_inc(v_endExclusive_245_);
lean_dec_ref(v___x_242_);
v_s_u2081_246_ = lean_string_utf8_extract(v_str_243_, v_startInclusive_244_, v_endExclusive_245_);
lean_dec(v_endExclusive_245_);
lean_dec(v_startInclusive_244_);
lean_dec_ref(v_str_243_);
v___x_254_ = lean_string_dec_eq(v_str_238_, v_s_u2081_246_);
lean_dec_ref(v_str_238_);
if (v___x_254_ == 0)
{
uint8_t v___x_255_; 
v___x_255_ = 1;
v___y_248_ = v___x_255_;
goto v___jp_247_;
}
else
{
uint8_t v___x_256_; 
v___x_256_ = 0;
v___y_248_ = v___x_256_;
goto v___jp_247_;
}
v___jp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_249_ = lean_box(2);
v___x_250_ = l_Lean_Syntax_mkStrLit(v_s_u2081_246_, v___x_249_);
v___x_251_ = lean_box(v___y_248_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_250_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
else
{
v___y_231_ = v_a_227_;
v___y_232_ = v_a_228_;
goto v___jp_230_;
}
}
else
{
v___y_231_ = v_a_227_;
v___y_232_ = v_a_228_;
goto v___jp_230_;
}
v___jp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_233_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkJsonField___closed__1, &l_Lean_Elab_Deriving_FromToJson_mkJsonField___closed__1_once, _init_l_Lean_Elab_Deriving_FromToJson_mkJsonField___closed__1);
v___x_234_ = l_Lean_MessageData_ofName(v_n_226_);
v___x_235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0___redArg(v___x_235_, v___y_231_, v___y_232_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkJsonField___boxed(lean_object* v_n_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Elab_Deriving_FromToJson_mkJsonField(v_n_257_, v_a_258_, v_a_259_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0(lean_object* v_00_u03b1_262_, lean_object* v_msg_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0___redArg(v_msg_263_, v___y_264_, v___y_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0___boxed(lean_object* v_00_u03b1_268_, lean_object* v_msg_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0(v_00_u03b1_268_, v_msg_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_273_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__9));
v___x_295_ = l_String_toRawSubstring_x27(v___x_294_);
return v___x_295_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__32));
v___x_349_ = l_String_toRawSubstring_x27(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__45(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__44));
v___x_378_ = l_String_toRawSubstring_x27(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg(lean_object* v_header_391_, size_t v_sz_392_, size_t v_i_393_, lean_object* v_bs_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
uint8_t v___x_398_; 
v___x_398_ = lean_usize_dec_lt(v_i_393_, v_sz_392_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec_ref(v___y_395_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v_bs_394_);
return v___x_399_;
}
else
{
lean_object* v_v_400_; lean_object* v___x_401_; 
v_v_400_ = lean_array_uget(v_bs_394_, v_i_393_);
lean_inc(v_v_400_);
v___x_401_ = l_Lean_Elab_Deriving_FromToJson_mkJsonField(v_v_400_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v_fst_403_; lean_object* v_snd_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_490_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref(v___x_401_);
v_fst_403_ = lean_ctor_get(v_a_402_, 0);
v_snd_404_ = lean_ctor_get(v_a_402_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v_a_402_);
if (v_isSharedCheck_490_ == 0)
{
v___x_406_ = v_a_402_;
v_isShared_407_ = v_isSharedCheck_490_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_snd_404_);
lean_inc(v_fst_403_);
lean_dec(v_a_402_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_490_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_targetNames_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v_bs_x27_411_; lean_object* v_a_413_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_targetNames_408_ = lean_ctor_get(v_header_391_, 2);
v___x_409_ = lean_box(0);
v___x_410_ = lean_unsigned_to_nat(0u);
v_bs_x27_411_ = lean_array_uset(v_bs_394_, v_i_393_, v___x_410_);
v___x_418_ = lean_array_get_borrowed(v___x_409_, v_targetNames_408_, v___x_410_);
lean_inc(v___x_418_);
v___x_419_ = lean_mk_syntax_ident(v___x_418_);
v___x_420_ = lean_unbox(v_fst_403_);
if (v___x_420_ == 0)
{
lean_object* v_ref_421_; lean_object* v_quotContext_422_; lean_object* v_currMacroScope_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v_ref_421_ = lean_ctor_get(v___y_395_, 5);
v_quotContext_422_ = lean_ctor_get(v___y_395_, 10);
v_currMacroScope_423_ = lean_ctor_get(v___y_395_, 11);
v___x_424_ = lean_unbox(v_fst_403_);
lean_dec(v_fst_403_);
v___x_425_ = l_Lean_SourceInfo_fromRef(v_ref_421_, v___x_424_);
v___x_426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1));
v___x_427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_425_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 2);
lean_ctor_set(v___x_406_, 1, v___x_427_);
lean_ctor_set(v___x_406_, 0, v___x_425_);
v___x_429_ = v___x_406_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_427_);
v___x_429_ = v_reuseFailAlloc_468_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_430_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_431_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4));
v___x_432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_433_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_425_);
v___x_434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_425_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_436_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
lean_inc(v_currMacroScope_423_);
lean_inc(v_quotContext_422_);
v___x_437_ = l_Lean_addMacroScope(v_quotContext_422_, v___x_409_, v_currMacroScope_423_);
v___x_438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__28));
lean_inc(v___x_425_);
v___x_439_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_439_, 0, v___x_425_);
lean_ctor_set(v___x_439_, 1, v___x_436_);
lean_ctor_set(v___x_439_, 2, v___x_437_);
lean_ctor_set(v___x_439_, 3, v___x_438_);
lean_inc(v___x_425_);
v___x_440_ = l_Lean_Syntax_node1(v___x_425_, v___x_435_, v___x_439_);
lean_inc(v___x_425_);
v___x_441_ = l_Lean_Syntax_node2(v___x_425_, v___x_432_, v___x_434_, v___x_440_);
v___x_442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
lean_inc(v___x_425_);
v___x_443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_425_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_445_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
lean_inc(v_currMacroScope_423_);
lean_inc(v_quotContext_422_);
v___x_447_ = l_Lean_addMacroScope(v_quotContext_422_, v___x_446_, v_currMacroScope_423_);
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__37));
lean_inc(v___x_425_);
v___x_449_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_449_, 0, v___x_425_);
lean_ctor_set(v___x_449_, 1, v___x_445_);
lean_ctor_set(v___x_449_, 2, v___x_447_);
lean_ctor_set(v___x_449_, 3, v___x_448_);
v___x_450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39));
v___x_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41));
v___x_452_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_425_);
v___x_453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_425_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
lean_inc_ref(v___x_453_);
lean_inc(v___x_441_);
lean_inc(v___x_425_);
v___x_454_ = l_Lean_Syntax_node3(v___x_425_, v___x_451_, v___x_441_, v___x_419_, v___x_453_);
v___x_455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__42));
lean_inc(v___x_425_);
v___x_456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_425_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = lean_mk_syntax_ident(v_v_400_);
lean_inc(v___x_425_);
v___x_458_ = l_Lean_Syntax_node3(v___x_425_, v___x_450_, v___x_454_, v___x_456_, v___x_457_);
lean_inc(v___x_425_);
v___x_459_ = l_Lean_Syntax_node1(v___x_425_, v___x_430_, v___x_458_);
lean_inc(v___x_425_);
v___x_460_ = l_Lean_Syntax_node2(v___x_425_, v___x_444_, v___x_449_, v___x_459_);
lean_inc(v___x_425_);
v___x_461_ = l_Lean_Syntax_node1(v___x_425_, v___x_430_, v___x_460_);
lean_inc(v___x_425_);
v___x_462_ = l_Lean_Syntax_node3(v___x_425_, v___x_430_, v_snd_404_, v___x_443_, v___x_461_);
lean_inc(v___x_425_);
v___x_463_ = l_Lean_Syntax_node3(v___x_425_, v___x_431_, v___x_441_, v___x_462_, v___x_453_);
lean_inc(v___x_425_);
v___x_464_ = l_Lean_Syntax_node1(v___x_425_, v___x_430_, v___x_463_);
v___x_465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_425_);
v___x_466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_425_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = l_Lean_Syntax_node3(v___x_425_, v___x_426_, v___x_429_, v___x_464_, v___x_466_);
v_a_413_ = v___x_467_;
goto v___jp_412_;
}
}
else
{
lean_object* v_ref_469_; lean_object* v_quotContext_470_; lean_object* v_currMacroScope_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
lean_dec(v_fst_403_);
v_ref_469_ = lean_ctor_get(v___y_395_, 5);
v_quotContext_470_ = lean_ctor_get(v___y_395_, 10);
v_currMacroScope_471_ = lean_ctor_get(v___y_395_, 11);
v___x_472_ = 0;
v___x_473_ = l_Lean_SourceInfo_fromRef(v_ref_469_, v___x_472_);
v___x_474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_475_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__45, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__45_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__45);
v___x_476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__46));
lean_inc(v_currMacroScope_471_);
lean_inc(v_quotContext_470_);
v___x_477_ = l_Lean_addMacroScope(v_quotContext_470_, v___x_476_, v_currMacroScope_471_);
v___x_478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__49));
lean_inc(v___x_473_);
v___x_479_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_479_, 0, v___x_473_);
lean_ctor_set(v___x_479_, 1, v___x_475_);
lean_ctor_set(v___x_479_, 2, v___x_477_);
lean_ctor_set(v___x_479_, 3, v___x_478_);
v___x_480_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39));
v___x_482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__42));
lean_inc(v___x_473_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 2);
lean_ctor_set(v___x_406_, 1, v___x_482_);
lean_ctor_set(v___x_406_, 0, v___x_473_);
v___x_484_ = v___x_406_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v___x_482_);
v___x_484_ = v_reuseFailAlloc_489_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_485_ = lean_mk_syntax_ident(v_v_400_);
lean_inc(v___x_473_);
v___x_486_ = l_Lean_Syntax_node3(v___x_473_, v___x_481_, v___x_419_, v___x_484_, v___x_485_);
lean_inc(v___x_473_);
v___x_487_ = l_Lean_Syntax_node2(v___x_473_, v___x_480_, v_snd_404_, v___x_486_);
v___x_488_ = l_Lean_Syntax_node2(v___x_473_, v___x_474_, v___x_479_, v___x_487_);
v_a_413_ = v___x_488_;
goto v___jp_412_;
}
}
v___jp_412_:
{
size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; 
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_393_, v___x_414_);
v___x_416_ = lean_array_uset(v_bs_x27_411_, v_i_393_, v_a_413_);
v_i_393_ = v___x_415_;
v_bs_394_ = v___x_416_;
goto _start;
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_v_400_);
lean_dec_ref(v___y_395_);
lean_dec_ref(v_bs_394_);
v_a_491_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_401_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_401_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___boxed(lean_object* v_header_499_, lean_object* v_sz_500_, lean_object* v_i_501_, lean_object* v_bs_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
size_t v_sz_boxed_506_; size_t v_i_boxed_507_; lean_object* v_res_508_; 
v_sz_boxed_506_ = lean_unbox_usize(v_sz_500_);
lean_dec(v_sz_500_);
v_i_boxed_507_ = lean_unbox_usize(v_i_501_);
lean_dec(v_i_501_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg(v_header_499_, v_sz_boxed_506_, v_i_boxed_507_, v_bs_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v_header_499_);
return v_res_508_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__2));
v___x_514_ = l_String_toRawSubstring_x27(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__10(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__9));
v___x_530_ = l_String_toRawSubstring_x27(v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct(lean_object* v_header_547_, lean_object* v_indName_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_556_; lean_object* v_env_557_; uint8_t v___x_558_; lean_object* v___x_559_; size_t v_sz_560_; size_t v___x_561_; lean_object* v___x_562_; 
v___x_556_ = lean_st_ref_get(v_a_554_);
v_env_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc_ref(v_env_557_);
lean_dec(v___x_556_);
v___x_558_ = 0;
v___x_559_ = l_Lean_getStructureFieldsFlattened(v_env_557_, v_indName_548_, v___x_558_);
v_sz_560_ = lean_array_size(v___x_559_);
v___x_561_ = ((size_t)0ULL);
lean_inc_ref(v_a_553_);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg(v_header_547_, v_sz_560_, v___x_561_, v___x_559_, v_a_553_, v_a_554_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_603_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_603_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_603_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_603_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v_ref_567_; lean_object* v_quotContext_568_; lean_object* v_currMacroScope_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v_ref_567_ = lean_ctor_get(v_a_553_, 5);
lean_inc(v_ref_567_);
v_quotContext_568_ = lean_ctor_get(v_a_553_, 10);
lean_inc(v_quotContext_568_);
v_currMacroScope_569_ = lean_ctor_get(v_a_553_, 11);
lean_inc(v_currMacroScope_569_);
lean_dec_ref(v_a_553_);
v___x_570_ = l_Lean_SourceInfo_fromRef(v_ref_567_, v___x_558_);
lean_dec(v_ref_567_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__1));
v___x_572_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3, &l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3_once, _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3);
v___x_573_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__4));
lean_inc(v_currMacroScope_569_);
lean_inc(v_quotContext_568_);
v___x_574_ = l_Lean_addMacroScope(v_quotContext_568_, v___x_573_, v_currMacroScope_569_);
v___x_575_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__7));
lean_inc(v___x_570_);
v___x_576_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_576_, 0, v___x_570_);
lean_ctor_set(v___x_576_, 1, v___x_572_);
lean_ctor_set(v___x_576_, 2, v___x_574_);
lean_ctor_set(v___x_576_, 3, v___x_575_);
v___x_577_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__8));
lean_inc(v___x_570_);
v___x_578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_570_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_580_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__10, &l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__10_once, _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__10);
v___x_581_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__13));
v___x_582_ = l_Lean_addMacroScope(v_quotContext_568_, v___x_581_, v_currMacroScope_569_);
v___x_583_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__17));
lean_inc(v___x_570_);
v___x_584_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_584_, 0, v___x_570_);
lean_ctor_set(v___x_584_, 1, v___x_580_);
lean_ctor_set(v___x_584_, 2, v___x_582_);
lean_ctor_set(v___x_584_, 3, v___x_583_);
v___x_585_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1));
v___x_587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_570_);
v___x_588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_570_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v___x_590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
v___x_591_ = l_Lean_Syntax_SepArray_ofElems(v___x_590_, v_a_563_);
lean_dec(v_a_563_);
v___x_592_ = l_Array_append___redArg(v___x_589_, v___x_591_);
lean_dec_ref(v___x_591_);
lean_inc(v___x_570_);
v___x_593_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_593_, 0, v___x_570_);
lean_ctor_set(v___x_593_, 1, v___x_585_);
lean_ctor_set(v___x_593_, 2, v___x_592_);
v___x_594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_570_);
v___x_595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_570_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
lean_inc(v___x_570_);
v___x_596_ = l_Lean_Syntax_node3(v___x_570_, v___x_586_, v___x_588_, v___x_593_, v___x_595_);
lean_inc(v___x_570_);
v___x_597_ = l_Lean_Syntax_node1(v___x_570_, v___x_585_, v___x_596_);
lean_inc(v___x_570_);
v___x_598_ = l_Lean_Syntax_node2(v___x_570_, v___x_579_, v___x_584_, v___x_597_);
v___x_599_ = l_Lean_Syntax_node3(v___x_570_, v___x_571_, v___x_576_, v___x_578_, v___x_598_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_599_);
v___x_601_ = v___x_565_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v_a_553_);
v_a_604_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_562_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_562_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___boxed(lean_object* v_header_612_, lean_object* v_indName_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct(v_header_612_, v_indName_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec_ref(v_header_612_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0(lean_object* v_header_622_, size_t v_sz_623_, size_t v_i_624_, lean_object* v_bs_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg(v_header_622_, v_sz_623_, v_i_624_, v_bs_625_, v___y_630_, v___y_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___boxed(lean_object* v_header_634_, lean_object* v_sz_635_, lean_object* v_i_636_, lean_object* v_bs_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
size_t v_sz_boxed_645_; size_t v_i_boxed_646_; lean_object* v_res_647_; 
v_sz_boxed_645_ = lean_unbox_usize(v_sz_635_);
lean_dec(v_sz_635_);
v_i_boxed_646_ = lean_unbox_usize(v_i_636_);
lean_dec(v_i_636_);
v_res_647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0(v_header_634_, v_sz_boxed_645_, v_i_boxed_646_, v_bs_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v_header_634_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___lam__0(lean_object* v_k_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v_b_651_, lean_object* v_c_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = lean_apply_9(v_k_648_, v_b_651_, v_c_652_, v___y_649_, v___y_650_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, lean_box(0));
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___lam__0___boxed(lean_object* v_k_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v_b_662_, lean_object* v_c_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___lam__0(v_k_659_, v___y_660_, v___y_661_, v_b_662_, v_c_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(lean_object* v_type_670_, lean_object* v_k_671_, uint8_t v_cleanupAnnotations_672_, uint8_t v_whnfType_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___f_681_; lean_object* v___x_682_; 
v___f_681_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_681_, 0, v_k_671_);
lean_closure_set(v___f_681_, 1, v___y_674_);
lean_closure_set(v___f_681_, 2, v___y_675_);
v___x_682_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_670_, v___f_681_, v_cleanupAnnotations_672_, v_whnfType_673_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_682_) == 0)
{
return v___x_682_;
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___boxed(lean_object* v_type_691_, lean_object* v_k_692_, lean_object* v_cleanupAnnotations_693_, lean_object* v_whnfType_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_702_; uint8_t v_whnfType_boxed_703_; lean_object* v_res_704_; 
v_cleanupAnnotations_boxed_702_ = lean_unbox(v_cleanupAnnotations_693_);
v_whnfType_boxed_703_ = lean_unbox(v_whnfType_694_);
v_res_704_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(v_type_691_, v_k_692_, v_cleanupAnnotations_boxed_702_, v_whnfType_boxed_703_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4(lean_object* v_00_u03b1_705_, lean_object* v_type_706_, lean_object* v_k_707_, uint8_t v_cleanupAnnotations_708_, uint8_t v_whnfType_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(v_type_706_, v_k_707_, v_cleanupAnnotations_708_, v_whnfType_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___boxed(lean_object* v_00_u03b1_718_, lean_object* v_type_719_, lean_object* v_k_720_, lean_object* v_cleanupAnnotations_721_, lean_object* v_whnfType_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_730_; uint8_t v_whnfType_boxed_731_; lean_object* v_res_732_; 
v_cleanupAnnotations_boxed_730_ = lean_unbox(v_cleanupAnnotations_721_);
v_whnfType_boxed_731_ = lean_unbox(v_whnfType_722_);
v_res_732_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4(v_00_u03b1_718_, v_type_719_, v_k_720_, v_cleanupAnnotations_boxed_730_, v_whnfType_boxed_731_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
return v_res_732_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1(lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v_toApplicative_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_841_; 
v___x_748_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__0);
v___x_749_ = l_ReaderT_instMonad___redArg(v___x_748_);
v_toApplicative_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v___x_749_, 1);
lean_dec(v_unused_842_);
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_841_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_toApplicative_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_841_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_toFunctor_754_; lean_object* v_toSeq_755_; lean_object* v_toSeqLeft_756_; lean_object* v_toSeqRight_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_839_; 
v_toFunctor_754_ = lean_ctor_get(v_toApplicative_750_, 0);
v_toSeq_755_ = lean_ctor_get(v_toApplicative_750_, 2);
v_toSeqLeft_756_ = lean_ctor_get(v_toApplicative_750_, 3);
v_toSeqRight_757_ = lean_ctor_get(v_toApplicative_750_, 4);
v_isSharedCheck_839_ = !lean_is_exclusive(v_toApplicative_750_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v_toApplicative_750_, 1);
lean_dec(v_unused_840_);
v___x_759_ = v_toApplicative_750_;
v_isShared_760_ = v_isSharedCheck_839_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_toSeqRight_757_);
lean_inc(v_toSeqLeft_756_);
lean_inc(v_toSeq_755_);
lean_inc(v_toFunctor_754_);
lean_dec(v_toApplicative_750_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_839_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___f_761_; lean_object* v___f_762_; lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___f_768_; lean_object* v___x_770_; 
v___f_761_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__1));
v___f_762_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_754_);
v___f_763_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_763_, 0, v_toFunctor_754_);
v___f_764_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_764_, 0, v_toFunctor_754_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___f_763_);
lean_ctor_set(v___x_765_, 1, v___f_764_);
v___f_766_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_766_, 0, v_toSeqRight_757_);
v___f_767_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_767_, 0, v_toSeqLeft_756_);
v___f_768_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_768_, 0, v_toSeq_755_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 4, v___f_766_);
lean_ctor_set(v___x_759_, 3, v___f_767_);
lean_ctor_set(v___x_759_, 2, v___f_768_);
lean_ctor_set(v___x_759_, 1, v___f_761_);
lean_ctor_set(v___x_759_, 0, v___x_765_);
v___x_770_ = v___x_759_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___f_761_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v___f_768_);
lean_ctor_set(v_reuseFailAlloc_838_, 3, v___f_767_);
lean_ctor_set(v_reuseFailAlloc_838_, 4, v___f_766_);
v___x_770_ = v_reuseFailAlloc_838_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_772_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v___f_762_);
lean_ctor_set(v___x_752_, 0, v___x_770_);
v___x_772_ = v___x_752_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v___f_762_);
v___x_772_ = v_reuseFailAlloc_837_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v_toApplicative_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_835_; 
v___x_773_ = l_ReaderT_instMonad___redArg(v___x_772_);
v_toApplicative_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v___x_773_, 1);
lean_dec(v_unused_836_);
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_835_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_toApplicative_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_835_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_toFunctor_778_; lean_object* v_toSeq_779_; lean_object* v_toSeqLeft_780_; lean_object* v_toSeqRight_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_833_; 
v_toFunctor_778_ = lean_ctor_get(v_toApplicative_774_, 0);
v_toSeq_779_ = lean_ctor_get(v_toApplicative_774_, 2);
v_toSeqLeft_780_ = lean_ctor_get(v_toApplicative_774_, 3);
v_toSeqRight_781_ = lean_ctor_get(v_toApplicative_774_, 4);
v_isSharedCheck_833_ = !lean_is_exclusive(v_toApplicative_774_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v_toApplicative_774_, 1);
lean_dec(v_unused_834_);
v___x_783_ = v_toApplicative_774_;
v_isShared_784_ = v_isSharedCheck_833_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_toSeqRight_781_);
lean_inc(v_toSeqLeft_780_);
lean_inc(v_toSeq_779_);
lean_inc(v_toFunctor_778_);
lean_dec(v_toApplicative_774_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_833_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___x_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___f_792_; lean_object* v___x_794_; 
v___f_785_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__3));
v___f_786_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_778_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_787_, 0, v_toFunctor_778_);
v___f_788_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_788_, 0, v_toFunctor_778_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___f_787_);
lean_ctor_set(v___x_789_, 1, v___f_788_);
v___f_790_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_790_, 0, v_toSeqRight_781_);
v___f_791_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_791_, 0, v_toSeqLeft_780_);
v___f_792_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_792_, 0, v_toSeq_779_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 4, v___f_790_);
lean_ctor_set(v___x_783_, 3, v___f_791_);
lean_ctor_set(v___x_783_, 2, v___f_792_);
lean_ctor_set(v___x_783_, 1, v___f_785_);
lean_ctor_set(v___x_783_, 0, v___x_789_);
v___x_794_ = v___x_783_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___f_785_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v___f_792_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v___f_791_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v___f_790_);
v___x_794_ = v_reuseFailAlloc_832_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_796_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___f_786_);
lean_ctor_set(v___x_776_, 0, v___x_794_);
v___x_796_ = v___x_776_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___f_786_);
v___x_796_ = v_reuseFailAlloc_831_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v_toApplicative_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_829_; 
v___x_797_ = l_ReaderT_instMonad___redArg(v___x_796_);
v_toApplicative_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_797_, 1);
lean_dec(v_unused_830_);
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_829_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_toApplicative_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_829_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_toFunctor_802_; lean_object* v_toSeq_803_; lean_object* v_toSeqLeft_804_; lean_object* v_toSeqRight_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_827_; 
v_toFunctor_802_ = lean_ctor_get(v_toApplicative_798_, 0);
v_toSeq_803_ = lean_ctor_get(v_toApplicative_798_, 2);
v_toSeqLeft_804_ = lean_ctor_get(v_toApplicative_798_, 3);
v_toSeqRight_805_ = lean_ctor_get(v_toApplicative_798_, 4);
v_isSharedCheck_827_ = !lean_is_exclusive(v_toApplicative_798_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v_toApplicative_798_, 1);
lean_dec(v_unused_828_);
v___x_807_ = v_toApplicative_798_;
v_isShared_808_ = v_isSharedCheck_827_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_toSeqRight_805_);
lean_inc(v_toSeqLeft_804_);
lean_inc(v_toSeq_803_);
lean_inc(v_toFunctor_802_);
lean_dec(v_toApplicative_798_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_827_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___f_809_; lean_object* v___f_810_; lean_object* v___f_811_; lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___f_814_; lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___x_818_; 
v___f_809_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__5));
v___f_810_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_802_);
v___f_811_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_811_, 0, v_toFunctor_802_);
v___f_812_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_812_, 0, v_toFunctor_802_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___f_811_);
lean_ctor_set(v___x_813_, 1, v___f_812_);
v___f_814_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_814_, 0, v_toSeqRight_805_);
v___f_815_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_815_, 0, v_toSeqLeft_804_);
v___f_816_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_816_, 0, v_toSeq_803_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v___f_814_);
lean_ctor_set(v___x_807_, 3, v___f_815_);
lean_ctor_set(v___x_807_, 2, v___f_816_);
lean_ctor_set(v___x_807_, 1, v___f_809_);
lean_ctor_set(v___x_807_, 0, v___x_813_);
v___x_818_ = v___x_807_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___f_809_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v___f_816_);
lean_ctor_set(v_reuseFailAlloc_826_, 3, v___f_815_);
lean_ctor_set(v_reuseFailAlloc_826_, 4, v___f_814_);
v___x_818_ = v_reuseFailAlloc_826_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_820_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___f_810_);
lean_ctor_set(v___x_800_, 0, v___x_818_);
v___x_820_ = v___x_800_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___f_810_);
v___x_820_ = v_reuseFailAlloc_825_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_16637__overap_823_; lean_object* v___x_824_; 
v___x_821_ = lean_box(0);
v___x_822_ = l_instInhabitedOfMonad___redArg(v___x_820_, v___x_821_);
v___x_16637__overap_823_ = lean_panic_fn(v___x_822_, v_msg_740_);
v___x_824_ = lean_apply_7(v___x_16637__overap_823_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, lean_box(0));
return v___x_824_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___boxed(lean_object* v_msg_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1(v_msg_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
return v_res_851_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__10(lean_object* v_opts_852_, lean_object* v_opt_853_){
_start:
{
lean_object* v_name_854_; lean_object* v_defValue_855_; lean_object* v_map_856_; lean_object* v___x_857_; 
v_name_854_ = lean_ctor_get(v_opt_853_, 0);
v_defValue_855_ = lean_ctor_get(v_opt_853_, 1);
v_map_856_ = lean_ctor_get(v_opts_852_, 0);
v___x_857_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_856_, v_name_854_);
if (lean_obj_tag(v___x_857_) == 0)
{
uint8_t v___x_858_; 
v___x_858_ = lean_unbox(v_defValue_855_);
return v___x_858_;
}
else
{
lean_object* v_val_859_; 
v_val_859_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_val_859_);
lean_dec_ref(v___x_857_);
if (lean_obj_tag(v_val_859_) == 1)
{
uint8_t v_v_860_; 
v_v_860_ = lean_ctor_get_uint8(v_val_859_, 0);
lean_dec_ref(v_val_859_);
return v_v_860_;
}
else
{
uint8_t v___x_861_; 
lean_dec(v_val_859_);
v___x_861_ = lean_unbox(v_defValue_855_);
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_opts_862_, lean_object* v_opt_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__10(v_opts_862_, v_opt_863_);
lean_dec_ref(v_opt_863_);
lean_dec_ref(v_opts_862_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_box(1);
v___x_867_ = l_Lean_MessageData_ofFormat(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2));
v___x_872_ = l_Lean_MessageData_ofFormat(v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
if (lean_obj_tag(v_x_874_) == 0)
{
return v_x_873_;
}
else
{
lean_object* v_head_875_; lean_object* v_tail_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_898_; 
v_head_875_ = lean_ctor_get(v_x_874_, 0);
v_tail_876_ = lean_ctor_get(v_x_874_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_x_874_);
if (v_isSharedCheck_898_ == 0)
{
v___x_878_ = v_x_874_;
v_isShared_879_ = v_isSharedCheck_898_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_tail_876_);
lean_inc(v_head_875_);
lean_dec(v_x_874_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_898_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_before_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_896_; 
v_before_880_ = lean_ctor_get(v_head_875_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v_head_875_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v_head_875_, 1);
lean_dec(v_unused_897_);
v___x_882_ = v_head_875_;
v_isShared_883_ = v_isSharedCheck_896_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_before_880_);
lean_dec(v_head_875_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_896_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_883_ == 0)
{
lean_ctor_set_tag(v___x_882_, 7);
lean_ctor_set(v___x_882_, 1, v___x_884_);
lean_ctor_set(v___x_882_, 0, v_x_873_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_x_873_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_895_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3);
if (v_isShared_879_ == 0)
{
lean_ctor_set_tag(v___x_878_, 7);
lean_ctor_set(v___x_878_, 1, v___x_887_);
lean_ctor_set(v___x_878_, 0, v___x_886_);
v___x_889_ = v___x_878_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_887_);
v___x_889_ = v_reuseFailAlloc_894_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = l_Lean_MessageData_ofSyntax(v_before_880_);
v___x_891_ = l_Lean_indentD(v___x_890_);
v___x_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_889_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v_x_873_ = v___x_892_;
v_x_874_ = v_tail_876_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_903_ = l_Lean_MessageData_ofFormat(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_904_, lean_object* v_macroStack_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_options_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_options_908_ = lean_ctor_get(v___y_906_, 2);
v___x_909_ = l_Lean_Elab_pp_macroStack;
v___x_910_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__10(v_options_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
lean_dec(v_macroStack_905_);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v_msgData_904_);
return v___x_911_;
}
else
{
if (lean_obj_tag(v_macroStack_905_) == 0)
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v_msgData_904_);
return v___x_912_;
}
else
{
lean_object* v_head_913_; lean_object* v_after_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_929_; 
v_head_913_ = lean_ctor_get(v_macroStack_905_, 0);
lean_inc(v_head_913_);
v_after_914_ = lean_ctor_get(v_head_913_, 1);
v_isSharedCheck_929_ = !lean_is_exclusive(v_head_913_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; 
v_unused_930_ = lean_ctor_get(v_head_913_, 0);
lean_dec(v_unused_930_);
v___x_916_ = v_head_913_;
v_isShared_917_ = v_isSharedCheck_929_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_after_914_);
lean_dec(v_head_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_929_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_917_ == 0)
{
lean_ctor_set_tag(v___x_916_, 7);
lean_ctor_set(v___x_916_, 1, v___x_918_);
lean_ctor_set(v___x_916_, 0, v_msgData_904_);
v___x_920_ = v___x_916_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_msgData_904_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v___x_918_);
v___x_920_ = v_reuseFailAlloc_928_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v_msgData_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_921_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l_Lean_MessageData_ofSyntax(v_after_914_);
v___x_924_ = l_Lean_indentD(v___x_923_);
v_msgData_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_925_, 0, v___x_922_);
lean_ctor_set(v_msgData_925_, 1, v___x_924_);
v___x_926_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11(v_msgData_925_, v_macroStack_905_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_931_, lean_object* v_macroStack_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_931_, v_macroStack_932_, v___y_933_);
lean_dec_ref(v___y_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__2(lean_object* v_msgData_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; lean_object* v_env_943_; lean_object* v___x_944_; lean_object* v_mctx_945_; lean_object* v_lctx_946_; lean_object* v_options_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_942_ = lean_st_ref_get(v___y_940_);
v_env_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc_ref(v_env_943_);
lean_dec(v___x_942_);
v___x_944_ = lean_st_ref_get(v___y_938_);
v_mctx_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc_ref(v_mctx_945_);
lean_dec(v___x_944_);
v_lctx_946_ = lean_ctor_get(v___y_937_, 2);
v_options_947_ = lean_ctor_get(v___y_939_, 2);
lean_inc_ref(v_options_947_);
lean_inc_ref(v_lctx_946_);
v___x_948_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_948_, 0, v_env_943_);
lean_ctor_set(v___x_948_, 1, v_mctx_945_);
lean_ctor_set(v___x_948_, 2, v_lctx_946_);
lean_ctor_set(v___x_948_, 3, v_options_947_);
v___x_949_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v_msgData_936_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__2(v_msgData_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_ref_966_; lean_object* v___x_967_; lean_object* v_a_968_; lean_object* v_macroStack_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_980_; 
v_ref_966_ = lean_ctor_get(v___y_963_, 5);
v___x_967_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__2(v_msg_958_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref(v___x_967_);
v_macroStack_969_ = lean_ctor_get(v___y_959_, 1);
lean_inc(v_macroStack_969_);
lean_dec_ref(v___y_959_);
lean_inc(v_macroStack_969_);
v___x_970_ = l_Lean_Elab_getBetterRef(v_ref_966_, v_macroStack_969_);
v___x_971_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_968_, v_macroStack_969_, v___y_963_);
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_980_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_980_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_980_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_970_);
lean_ctor_set(v___x_976_, 1, v_a_972_);
if (v_isShared_975_ == 0)
{
lean_ctor_set_tag(v___x_974_, 1);
lean_ctor_set(v___x_974_, 0, v___x_976_);
v___x_978_ = v___x_974_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg(v_msg_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
return v_res_989_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__0));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__2));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_999_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__6));
v___x_1000_ = lean_unsigned_to_nat(11u);
v___x_1001_ = lean_unsigned_to_nat(122u);
v___x_1002_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__5));
v___x_1003_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__4));
v___x_1004_ = l_mkPanicMessageWithDecl(v___x_1003_, v___x_1002_, v___x_1001_, v___x_1000_, v___x_999_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0(lean_object* v_constName_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1021_; lean_object* v_env_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1021_ = lean_st_ref_get(v___y_1011_);
v_env_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc_ref(v_env_1022_);
lean_dec(v___x_1021_);
v___x_1023_ = 0;
lean_inc(v_constName_1005_);
v___x_1024_ = l_Lean_Environment_findAsync_x3f(v_env_1022_, v_constName_1005_, v___x_1023_);
if (lean_obj_tag(v___x_1024_) == 1)
{
lean_object* v_val_1025_; uint8_t v_kind_1026_; 
v_val_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_val_1025_);
lean_dec_ref(v___x_1024_);
v_kind_1026_ = lean_ctor_get_uint8(v_val_1025_, sizeof(void*)*3);
if (v_kind_1026_ == 6)
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1025_);
if (lean_obj_tag(v___x_1027_) == 6)
{
lean_object* v_val_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v_constName_1005_);
v_val_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_val_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 0);
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_val_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec_ref(v___x_1027_);
v___x_1036_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__7);
lean_inc(v___y_1011_);
lean_inc_ref(v___y_1010_);
lean_inc(v___y_1009_);
lean_inc_ref(v___y_1008_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
v___x_1037_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1(v___x_1036_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1046_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
if (lean_obj_tag(v_a_1038_) == 0)
{
lean_del_object(v___x_1040_);
goto v___jp_1013_;
}
else
{
lean_object* v_val_1042_; lean_object* v___x_1044_; 
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v_constName_1005_);
v_val_1042_ = lean_ctor_get(v_a_1038_, 0);
lean_inc(v_val_1042_);
lean_dec_ref(v_a_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v_val_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_val_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v_constName_1005_);
v_a_1047_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1037_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1037_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
else
{
lean_dec(v_val_1025_);
goto v___jp_1013_;
}
}
else
{
lean_dec(v___x_1024_);
goto v___jp_1013_;
}
v___jp_1013_:
{
lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1014_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1);
v___x_1015_ = 0;
v___x_1016_ = l_Lean_MessageData_ofConstName(v_constName_1005_, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1014_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__3);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg(v___x_1019_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___boxed(lean_object* v_constName_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0(v_constName_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg(lean_object* v_upperBound_1071_, lean_object* v_a_1072_, lean_object* v_b_1073_, lean_object* v___y_1074_){
_start:
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_nat_dec_lt(v_a_1072_, v_upperBound_1071_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
lean_dec(v_a_1072_);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v_b_1073_);
return v___x_1077_;
}
else
{
lean_object* v_ref_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_ref_1078_ = lean_ctor_get(v___y_1074_, 5);
v___x_1079_ = 0;
v___x_1080_ = l_Lean_SourceInfo_fromRef(v_ref_1078_, v___x_1079_);
v___x_1081_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1));
v___x_1082_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__2));
lean_inc(v___x_1080_);
v___x_1083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1080_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_Syntax_node1(v___x_1080_, v___x_1081_, v___x_1083_);
v___x_1085_ = lean_array_push(v_b_1073_, v___x_1084_);
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = lean_nat_add(v_a_1072_, v___x_1086_);
lean_dec(v_a_1072_);
v_a_1072_ = v___x_1087_;
v_b_1073_ = v___x_1085_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_1089_, lean_object* v_a_1090_, lean_object* v_b_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg(v_upperBound_1089_, v_a_1090_, v_b_1091_, v___y_1092_);
lean_dec_ref(v___y_1092_);
lean_dec(v_upperBound_1089_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0(lean_object* v_a_1098_, lean_object* v_fst_1099_, lean_object* v_fst_1100_, lean_object* v_____r_1101_, lean_object* v_userNames_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___closed__1));
v___x_1111_ = l_Lean_Core_mkFreshUserName(v___x_1110_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1127_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1127_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1127_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1116_ = lean_mk_syntax_ident(v_a_1112_);
v___x_1117_ = l_Lean_LocalDecl_type(v_a_1098_);
lean_inc(v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_array_push(v_fst_1099_, v___x_1118_);
v___x_1120_ = lean_array_push(v_fst_1100_, v___x_1116_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v_userNames_1102_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1123_);
v___x_1125_ = v___x_1114_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v_userNames_1102_);
lean_dec(v_fst_1100_);
lean_dec(v_fst_1099_);
v_a_1128_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1111_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1111_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___boxed(lean_object* v_a_1136_, lean_object* v_fst_1137_, lean_object* v_fst_1138_, lean_object* v_____r_1139_, lean_object* v_userNames_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0(v_a_1136_, v_fst_1137_, v_fst_1138_, v_____r_1139_, v_userNames_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_a_1136_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg(lean_object* v_upperBound_1149_, lean_object* v___x_1150_, lean_object* v_xs_1151_, lean_object* v_a_1152_, lean_object* v_b_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___y_1162_; uint8_t v___x_1184_; 
v___x_1184_ = lean_nat_dec_lt(v_a_1152_, v_upperBound_1149_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; 
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v___y_1156_);
lean_dec(v_a_1152_);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v_b_1153_);
return v___x_1185_;
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1186_ = l_Lean_instInhabitedExpr;
v___x_1187_ = lean_nat_add(v___x_1150_, v_a_1152_);
v___x_1188_ = lean_array_get_borrowed(v___x_1186_, v_xs_1151_, v___x_1187_);
lean_dec(v___x_1187_);
v___x_1189_ = l_Lean_Expr_fvarId_x21(v___x_1188_);
lean_inc_ref(v___y_1156_);
v___x_1190_ = l_Lean_FVarId_getDecl___redArg(v___x_1189_, v___y_1156_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_snd_1191_; lean_object* v_a_1192_; lean_object* v_fst_1193_; lean_object* v_fst_1194_; lean_object* v_snd_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_snd_1191_ = lean_ctor_get(v_b_1153_, 1);
lean_inc(v_snd_1191_);
v_a_1192_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1192_);
lean_dec_ref(v___x_1190_);
v_fst_1193_ = lean_ctor_get(v_b_1153_, 0);
lean_inc(v_fst_1193_);
lean_dec_ref(v_b_1153_);
v_fst_1194_ = lean_ctor_get(v_snd_1191_, 0);
lean_inc(v_fst_1194_);
v_snd_1195_ = lean_ctor_get(v_snd_1191_, 1);
lean_inc(v_snd_1195_);
lean_dec(v_snd_1191_);
v___x_1196_ = l_Lean_LocalDecl_userName(v_a_1192_);
v___x_1197_ = l_Lean_Name_hasMacroScopes(v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = lean_array_push(v_snd_1195_, v___x_1196_);
v___x_1199_ = lean_box(0);
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
v___x_1200_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0(v_a_1192_, v_fst_1194_, v_fst_1193_, v___x_1199_, v___x_1198_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v_a_1192_);
v___y_1162_ = v___x_1200_;
goto v___jp_1161_;
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec(v___x_1196_);
v___x_1201_ = lean_box(0);
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
v___x_1202_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0(v_a_1192_, v_fst_1194_, v_fst_1193_, v___x_1201_, v_snd_1195_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v_a_1192_);
v___y_1162_ = v___x_1202_;
goto v___jp_1161_;
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v___y_1156_);
lean_dec_ref(v_b_1153_);
lean_dec(v_a_1152_);
v_a_1203_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1190_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1190_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
v___jp_1161_:
{
if (lean_obj_tag(v___y_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1175_; 
v_a_1163_ = lean_ctor_get(v___y_1162_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___y_1162_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1165_ = v___y_1162_;
v_isShared_1166_ = v_isSharedCheck_1175_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___y_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1175_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
if (lean_obj_tag(v_a_1163_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; 
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v___y_1156_);
lean_dec(v_a_1152_);
v_a_1167_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_a_1167_);
lean_dec_ref(v_a_1163_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v_a_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_del_object(v___x_1165_);
v_a_1171_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_a_1171_);
lean_dec_ref(v_a_1163_);
v___x_1172_ = lean_unsigned_to_nat(1u);
v___x_1173_ = lean_nat_add(v_a_1152_, v___x_1172_);
lean_dec(v_a_1152_);
v_a_1152_ = v___x_1173_;
v_b_1153_ = v_a_1171_;
goto _start;
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v___y_1156_);
lean_dec(v_a_1152_);
v_a_1176_ = lean_ctor_get(v___y_1162_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___y_1162_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___y_1162_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___y_1162_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___boxed(lean_object* v_upperBound_1211_, lean_object* v___x_1212_, lean_object* v_xs_1213_, lean_object* v_a_1214_, lean_object* v_b_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_1211_, v___x_1212_, v_xs_1213_, v_a_1214_, v_b_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1219_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v_xs_1213_);
lean_dec(v___x_1212_);
lean_dec(v_upperBound_1211_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(size_t v_sz_1224_, size_t v_i_1225_, lean_object* v_bs_1226_){
_start:
{
uint8_t v___x_1227_; 
v___x_1227_ = lean_usize_dec_lt(v_i_1225_, v_sz_1224_);
if (v___x_1227_ == 0)
{
return v_bs_1226_;
}
else
{
lean_object* v_v_1228_; lean_object* v___x_1229_; lean_object* v_bs_x27_1230_; size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; 
v_v_1228_ = lean_array_uget(v_bs_1226_, v_i_1225_);
v___x_1229_ = lean_unsigned_to_nat(0u);
v_bs_x27_1230_ = lean_array_uset(v_bs_1226_, v_i_1225_, v___x_1229_);
v___x_1231_ = ((size_t)1ULL);
v___x_1232_ = lean_usize_add(v_i_1225_, v___x_1231_);
v___x_1233_ = lean_array_uset(v_bs_x27_1230_, v_i_1225_, v_v_1228_);
v_i_1225_ = v___x_1232_;
v_bs_1226_ = v___x_1233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1___boxed(lean_object* v_sz_1235_, lean_object* v_i_1236_, lean_object* v_bs_1237_){
_start:
{
size_t v_sz_boxed_1238_; size_t v_i_boxed_1239_; lean_object* v_res_1240_; 
v_sz_boxed_1238_ = lean_unbox_usize(v_sz_1235_);
lean_dec(v_sz_1235_);
v_i_boxed_1239_ = lean_unbox_usize(v_i_1236_);
lean_dec(v_i_1236_);
v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(v_sz_boxed_1238_, v_i_boxed_1239_, v_bs_1237_);
return v_res_1240_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
v___x_1256_ = l_Lean_mkAtom(v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(lean_object* v_indVal_1258_, lean_object* v___x_1259_, lean_object* v_alts_1260_, lean_object* v_numFields_1261_, lean_object* v_name_1262_, lean_object* v_rhs_1263_, lean_object* v_a_1264_, lean_object* v_xs_1265_, lean_object* v_x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_numParams_1274_; lean_object* v_numIndices_1275_; lean_object* v___x_1276_; 
v_numParams_1274_ = lean_ctor_get(v_indVal_1258_, 1);
v_numIndices_1275_ = lean_ctor_get(v_indVal_1258_, 2);
lean_inc_ref(v_alts_1260_);
lean_inc(v___x_1259_);
v___x_1276_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg(v_numIndices_1275_, v___x_1259_, v_alts_1260_, v___y_1271_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref(v___x_1276_);
lean_inc(v___x_1259_);
v___x_1278_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg(v_numParams_1274_, v___x_1259_, v_alts_1260_, v___y_1271_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1278_);
v___x_1280_ = lean_mk_empty_array_with_capacity(v___x_1259_);
lean_inc_ref(v___x_1280_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v_a_1279_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
lean_inc_ref(v___y_1269_);
v___x_1283_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg(v_numFields_1261_, v_numParams_1274_, v_xs_1265_, v___x_1259_, v___x_1282_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_snd_1285_; lean_object* v_fst_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1345_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v___x_1283_);
v_snd_1285_ = lean_ctor_get(v_a_1284_, 1);
v_fst_1286_ = lean_ctor_get(v_a_1284_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_a_1284_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1288_ = v_a_1284_;
v_isShared_1289_ = v_isSharedCheck_1345_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_snd_1285_);
lean_inc(v_fst_1286_);
lean_dec(v_a_1284_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1345_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_fst_1290_; lean_object* v_snd_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1344_; 
v_fst_1290_ = lean_ctor_get(v_snd_1285_, 0);
v_snd_1291_ = lean_ctor_get(v_snd_1285_, 1);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_snd_1285_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1293_ = v_snd_1285_;
v_isShared_1294_ = v_isSharedCheck_1344_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_snd_1291_);
lean_inc(v_fst_1290_);
lean_dec(v_snd_1285_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1344_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_ref_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v_ref_1295_ = lean_ctor_get(v___y_1271_, 5);
v___x_1296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1297_ = 0;
v___x_1298_ = l_Lean_SourceInfo_fromRef(v_ref_1295_, v___x_1297_);
v___x_1299_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__1));
v___x_1300_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__2));
lean_inc(v___x_1298_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set_tag(v___x_1293_, 2);
lean_ctor_set(v___x_1293_, 1, v___x_1300_);
lean_ctor_set(v___x_1293_, 0, v___x_1298_);
v___x_1302_ = v___x_1293_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___y_1312_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1303_ = lean_mk_syntax_ident(v_name_1262_);
lean_inc(v___x_1298_);
v___x_1304_ = l_Lean_Syntax_node2(v___x_1298_, v___x_1299_, v___x_1302_, v___x_1303_);
v___x_1305_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_1306_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v___x_1307_ = l_Array_append___redArg(v___x_1306_, v_fst_1286_);
lean_dec(v_fst_1286_);
lean_inc(v___x_1298_);
v___x_1308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1298_);
lean_ctor_set(v___x_1308_, 1, v___x_1305_);
lean_ctor_set(v___x_1308_, 2, v___x_1307_);
lean_inc(v___x_1298_);
v___x_1309_ = l_Lean_Syntax_node2(v___x_1298_, v___x_1296_, v___x_1304_, v___x_1308_);
v___x_1310_ = lean_array_push(v_a_1277_, v___x_1309_);
v___x_1338_ = lean_array_get_size(v_snd_1291_);
v___x_1339_ = lean_array_get_size(v_fst_1290_);
v___x_1340_ = lean_nat_dec_eq(v___x_1338_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
lean_dec(v_snd_1291_);
v___x_1341_ = lean_box(0);
v___y_1312_ = v___x_1341_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1342_, 0, v_snd_1291_);
v___y_1312_ = v___x_1342_;
goto v___jp_1311_;
}
v___jp_1311_:
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_apply_10(v_rhs_1263_, v_a_1264_, v_fst_1290_, v___y_1312_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, lean_box(0));
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1337_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1337_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1337_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1318_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4));
v___x_1319_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__5));
lean_inc(v___x_1298_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set_tag(v___x_1288_, 2);
lean_ctor_set(v___x_1288_, 1, v___x_1319_);
lean_ctor_set(v___x_1288_, 0, v___x_1298_);
v___x_1321_ = v___x_1288_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
size_t v_sz_1322_; size_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v_sz_1322_ = lean_array_size(v___x_1310_);
v___x_1323_ = ((size_t)0ULL);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(v_sz_1322_, v___x_1323_, v___x_1310_);
v___x_1325_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6);
v___x_1326_ = l_Lean_mkSepArray(v___x_1324_, v___x_1325_);
lean_dec_ref(v___x_1324_);
v___x_1327_ = l_Array_append___redArg(v___x_1306_, v___x_1326_);
lean_dec_ref(v___x_1326_);
lean_inc(v___x_1298_);
v___x_1328_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1298_);
lean_ctor_set(v___x_1328_, 1, v___x_1305_);
lean_ctor_set(v___x_1328_, 2, v___x_1327_);
lean_inc(v___x_1298_);
v___x_1329_ = l_Lean_Syntax_node1(v___x_1298_, v___x_1305_, v___x_1328_);
v___x_1330_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__7));
lean_inc(v___x_1298_);
v___x_1331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1298_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_Syntax_node4(v___x_1298_, v___x_1318_, v___x_1321_, v___x_1329_, v___x_1331_, v_a_1314_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1332_);
v___x_1334_ = v___x_1316_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
else
{
lean_dec_ref(v___x_1310_);
lean_dec(v___x_1298_);
lean_del_object(v___x_1288_);
return v___x_1313_;
}
}
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_a_1277_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec_ref(v_a_1264_);
lean_dec_ref(v_rhs_1263_);
lean_dec(v_name_1262_);
v_a_1346_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1283_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1283_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v_a_1277_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec_ref(v_a_1264_);
lean_dec_ref(v_rhs_1263_);
lean_dec(v_name_1262_);
lean_dec(v___x_1259_);
v_a_1354_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1278_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1278_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec_ref(v_a_1264_);
lean_dec_ref(v_rhs_1263_);
lean_dec(v_name_1262_);
lean_dec_ref(v_alts_1260_);
lean_dec(v___x_1259_);
v_a_1362_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1276_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1276_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___boxed(lean_object* v_indVal_1370_, lean_object* v___x_1371_, lean_object* v_alts_1372_, lean_object* v_numFields_1373_, lean_object* v_name_1374_, lean_object* v_rhs_1375_, lean_object* v_a_1376_, lean_object* v_xs_1377_, lean_object* v_x_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(v_indVal_1370_, v___x_1371_, v_alts_1372_, v_numFields_1373_, v_name_1374_, v_rhs_1375_, v_a_1376_, v_xs_1377_, v_x_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec_ref(v_x_1378_);
lean_dec_ref(v_xs_1377_);
lean_dec(v_numFields_1373_);
lean_dec_ref(v_indVal_1370_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg(lean_object* v_indVal_1389_, lean_object* v_rhs_1390_, lean_object* v_as_x27_1391_, lean_object* v_b_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
if (lean_obj_tag(v_as_x27_1391_) == 0)
{
lean_object* v___x_1400_; 
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec_ref(v_rhs_1390_);
lean_dec_ref(v_indVal_1389_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_b_1392_);
return v___x_1400_;
}
else
{
lean_object* v_head_1401_; lean_object* v_tail_1402_; lean_object* v___x_1403_; 
v_head_1401_ = lean_ctor_get(v_as_x27_1391_, 0);
lean_inc(v_head_1401_);
v_tail_1402_ = lean_ctor_get(v_as_x27_1391_, 1);
lean_inc(v_tail_1402_);
lean_dec_ref(v_as_x27_1391_);
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
v___x_1403_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0(v_head_1401_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v_toConstantVal_1405_; lean_object* v_numFields_1406_; lean_object* v_name_1407_; lean_object* v_type_1408_; lean_object* v___x_1409_; lean_object* v_alts_1410_; lean_object* v___f_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref(v___x_1403_);
v_toConstantVal_1405_ = lean_ctor_get(v_a_1404_, 0);
v_numFields_1406_ = lean_ctor_get(v_a_1404_, 4);
lean_inc(v_numFields_1406_);
v_name_1407_ = lean_ctor_get(v_toConstantVal_1405_, 0);
lean_inc(v_name_1407_);
v_type_1408_ = lean_ctor_get(v_toConstantVal_1405_, 2);
lean_inc_ref(v_type_1408_);
v___x_1409_ = lean_unsigned_to_nat(0u);
v_alts_1410_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___closed__0));
lean_inc_ref(v_rhs_1390_);
lean_inc_ref(v_indVal_1389_);
v___f_1411_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___boxed), 16, 7);
lean_closure_set(v___f_1411_, 0, v_indVal_1389_);
lean_closure_set(v___f_1411_, 1, v___x_1409_);
lean_closure_set(v___f_1411_, 2, v_alts_1410_);
lean_closure_set(v___f_1411_, 3, v_numFields_1406_);
lean_closure_set(v___f_1411_, 4, v_name_1407_);
lean_closure_set(v___f_1411_, 5, v_rhs_1390_);
lean_closure_set(v___f_1411_, 6, v_a_1404_);
v___x_1412_ = 0;
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
v___x_1413_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(v_type_1408_, v___f_1411_, v___x_1412_, v___x_1412_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref(v___x_1413_);
v___x_1415_ = lean_array_push(v_b_1392_, v_a_1414_);
v_as_x27_1391_ = v_tail_1402_;
v_b_1392_ = v___x_1415_;
goto _start;
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec(v_tail_1402_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec_ref(v_b_1392_);
lean_dec_ref(v_rhs_1390_);
lean_dec_ref(v_indVal_1389_);
v_a_1417_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1413_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1413_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_tail_1402_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec_ref(v_b_1392_);
lean_dec_ref(v_rhs_1390_);
lean_dec_ref(v_indVal_1389_);
v_a_1425_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1403_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1403_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___boxed(lean_object* v_indVal_1433_, lean_object* v_rhs_1434_, lean_object* v_as_x27_1435_, lean_object* v_b_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg(v_indVal_1433_, v_rhs_1434_, v_as_x27_1435_, v_b_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__6(size_t v_sz_1445_, size_t v_i_1446_, lean_object* v_bs_1447_){
_start:
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_usize_dec_lt(v_i_1446_, v_sz_1445_);
if (v___x_1448_ == 0)
{
return v_bs_1447_;
}
else
{
lean_object* v_v_1449_; lean_object* v___x_1450_; lean_object* v_bs_x27_1451_; size_t v___x_1452_; size_t v___x_1453_; lean_object* v___x_1454_; 
v_v_1449_ = lean_array_uget(v_bs_1447_, v_i_1446_);
v___x_1450_ = lean_unsigned_to_nat(0u);
v_bs_x27_1451_ = lean_array_uset(v_bs_1447_, v_i_1446_, v___x_1450_);
v___x_1452_ = ((size_t)1ULL);
v___x_1453_ = lean_usize_add(v_i_1446_, v___x_1452_);
v___x_1454_ = lean_array_uset(v_bs_x27_1451_, v_i_1446_, v_v_1449_);
v_i_1446_ = v___x_1453_;
v_bs_1447_ = v___x_1454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__6___boxed(lean_object* v_sz_1456_, lean_object* v_i_1457_, lean_object* v_bs_1458_){
_start:
{
size_t v_sz_boxed_1459_; size_t v_i_boxed_1460_; lean_object* v_res_1461_; 
v_sz_boxed_1459_ = lean_unbox_usize(v_sz_1456_);
lean_dec(v_sz_1456_);
v_i_boxed_1460_ = lean_unbox_usize(v_i_1457_);
lean_dec(v_i_1457_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__6(v_sz_boxed_1459_, v_i_boxed_1460_, v_bs_1458_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts(lean_object* v_indVal_1462_, lean_object* v_rhs_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_ctors_1471_; lean_object* v_alts_1472_; lean_object* v___x_1473_; 
v_ctors_1471_ = lean_ctor_get(v_indVal_1462_, 4);
lean_inc(v_ctors_1471_);
v_alts_1472_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___closed__0));
v___x_1473_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg(v_indVal_1462_, v_rhs_1463_, v_ctors_1471_, v_alts_1472_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1484_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1484_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1484_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
size_t v_sz_1478_; size_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v_sz_1478_ = lean_array_size(v_a_1474_);
v___x_1479_ = ((size_t)0ULL);
v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__6(v_sz_1478_, v___x_1479_, v_a_1474_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1480_);
v___x_1482_ = v___x_1476_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
else
{
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts___boxed(lean_object* v_indVal_1485_, lean_object* v_rhs_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts(v_indVal_1485_, v_rhs_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2(lean_object* v_upperBound_1495_, lean_object* v___x_1496_, lean_object* v_xs_1497_, lean_object* v_inst_1498_, lean_object* v_R_1499_, lean_object* v_a_1500_, lean_object* v_b_1501_, lean_object* v_c_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_1495_, v___x_1496_, v_xs_1497_, v_a_1500_, v_b_1501_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___boxed(lean_object* v_upperBound_1511_, lean_object* v___x_1512_, lean_object* v_xs_1513_, lean_object* v_inst_1514_, lean_object* v_R_1515_, lean_object* v_a_1516_, lean_object* v_b_1517_, lean_object* v_c_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2(v_upperBound_1511_, v___x_1512_, v_xs_1513_, v_inst_1514_, v_R_1515_, v_a_1516_, v_b_1517_, v_c_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1522_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec_ref(v_xs_1513_);
lean_dec(v___x_1512_);
lean_dec(v_upperBound_1511_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3(lean_object* v_upperBound_1527_, lean_object* v_inst_1528_, lean_object* v_R_1529_, lean_object* v_a_1530_, lean_object* v_b_1531_, lean_object* v_c_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg(v_upperBound_1527_, v_a_1530_, v_b_1531_, v___y_1537_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___boxed(lean_object* v_upperBound_1541_, lean_object* v_inst_1542_, lean_object* v_R_1543_, lean_object* v_a_1544_, lean_object* v_b_1545_, lean_object* v_c_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3(v_upperBound_1541_, v_inst_1542_, v_R_1543_, v_a_1544_, v_b_1545_, v_c_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v_upperBound_1541_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5(lean_object* v_indVal_1555_, lean_object* v_rhs_1556_, lean_object* v_as_1557_, lean_object* v_as_x27_1558_, lean_object* v_b_1559_, lean_object* v_a_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg(v_indVal_1555_, v_rhs_1556_, v_as_x27_1558_, v_b_1559_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___boxed(lean_object* v_indVal_1569_, lean_object* v_rhs_1570_, lean_object* v_as_1571_, lean_object* v_as_x27_1572_, lean_object* v_b_1573_, lean_object* v_a_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5(v_indVal_1569_, v_rhs_1570_, v_as_1571_, v_as_x27_1572_, v_b_1573_, v_a_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v_as_1571_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1583_, lean_object* v_msg_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg(v_msg_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1593_, lean_object* v_msg_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0(v_00_u03b1_1593_, v_msg_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1603_, lean_object* v_macroStack_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1603_, v_macroStack_1604_, v___y_1609_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1613_, lean_object* v_macroStack_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3(v_msgData_1613_, v_macroStack_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg(lean_object* v_a_1629_, lean_object* v___x_1630_, size_t v_sz_1631_, size_t v_i_1632_, lean_object* v_bs_1633_, lean_object* v___y_1634_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_usize_dec_lt(v_i_1632_, v_sz_1631_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref(v___y_1634_);
lean_dec(v___x_1630_);
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_bs_1633_);
return v___x_1637_;
}
else
{
lean_object* v_v_1638_; lean_object* v_toConstantVal_1639_; lean_object* v_fst_1640_; lean_object* v_snd_1641_; lean_object* v_name_1642_; lean_object* v___x_1643_; lean_object* v_bs_x27_1644_; lean_object* v_a_1646_; uint8_t v___x_1651_; 
v_v_1638_ = lean_array_uget_borrowed(v_bs_1633_, v_i_1632_);
v_toConstantVal_1639_ = lean_ctor_get(v_a_1629_, 0);
v_fst_1640_ = lean_ctor_get(v_v_1638_, 0);
lean_inc(v_fst_1640_);
v_snd_1641_ = lean_ctor_get(v_v_1638_, 1);
lean_inc(v_snd_1641_);
v_name_1642_ = lean_ctor_get(v_toConstantVal_1639_, 0);
v___x_1643_ = lean_unsigned_to_nat(0u);
v_bs_x27_1644_ = lean_array_uset(v_bs_1633_, v_i_1632_, v___x_1643_);
v___x_1651_ = l_Lean_Expr_isAppOf(v_snd_1641_, v_name_1642_);
lean_dec(v_snd_1641_);
if (v___x_1651_ == 0)
{
lean_object* v_ref_1652_; lean_object* v_quotContext_1653_; lean_object* v_currMacroScope_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_ref_1652_ = lean_ctor_get(v___y_1634_, 5);
v_quotContext_1653_ = lean_ctor_get(v___y_1634_, 10);
v_currMacroScope_1654_ = lean_ctor_get(v___y_1634_, 11);
v___x_1655_ = l_Lean_SourceInfo_fromRef(v_ref_1652_, v___x_1651_);
v___x_1656_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1657_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_1658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
lean_inc(v_currMacroScope_1654_);
lean_inc(v_quotContext_1653_);
v___x_1659_ = l_Lean_addMacroScope(v_quotContext_1653_, v___x_1658_, v_currMacroScope_1654_);
v___x_1660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1));
lean_inc(v___x_1655_);
v___x_1661_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1655_);
lean_ctor_set(v___x_1661_, 1, v___x_1657_);
lean_ctor_set(v___x_1661_, 2, v___x_1659_);
lean_ctor_set(v___x_1661_, 3, v___x_1660_);
v___x_1662_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1655_);
v___x_1663_ = l_Lean_Syntax_node1(v___x_1655_, v___x_1662_, v_fst_1640_);
v___x_1664_ = l_Lean_Syntax_node2(v___x_1655_, v___x_1656_, v___x_1661_, v___x_1663_);
v_a_1646_ = v___x_1664_;
goto v___jp_1645_;
}
else
{
lean_object* v_ref_1665_; uint8_t v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_ref_1665_ = lean_ctor_get(v___y_1634_, 5);
v___x_1666_ = 0;
v___x_1667_ = l_Lean_SourceInfo_fromRef(v_ref_1665_, v___x_1666_);
v___x_1668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1669_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1667_);
v___x_1670_ = l_Lean_Syntax_node1(v___x_1667_, v___x_1669_, v_fst_1640_);
lean_inc(v___x_1630_);
v___x_1671_ = l_Lean_Syntax_node2(v___x_1667_, v___x_1668_, v___x_1630_, v___x_1670_);
v_a_1646_ = v___x_1671_;
goto v___jp_1645_;
}
v___jp_1645_:
{
size_t v___x_1647_; size_t v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = ((size_t)1ULL);
v___x_1648_ = lean_usize_add(v_i_1632_, v___x_1647_);
v___x_1649_ = lean_array_uset(v_bs_x27_1644_, v_i_1632_, v_a_1646_);
v_i_1632_ = v___x_1648_;
v_bs_1633_ = v___x_1649_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___boxed(lean_object* v_a_1672_, lean_object* v___x_1673_, lean_object* v_sz_1674_, lean_object* v_i_1675_, lean_object* v_bs_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
size_t v_sz_boxed_1679_; size_t v_i_boxed_1680_; lean_object* v_res_1681_; 
v_sz_boxed_1679_ = lean_unbox_usize(v_sz_1674_);
lean_dec(v_sz_1674_);
v_i_boxed_1680_ = lean_unbox_usize(v_i_1675_);
lean_dec(v_i_1675_);
v_res_1681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg(v_a_1672_, v___x_1673_, v_sz_boxed_1679_, v_i_boxed_1680_, v_bs_1676_, v___y_1677_);
lean_dec_ref(v_a_1672_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2(lean_object* v_a_1682_, lean_object* v___x_1683_, size_t v_sz_1684_, size_t v_i_1685_, lean_object* v_bs_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_usize_dec_lt(v_i_1685_, v_sz_1684_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; 
lean_dec_ref(v___y_1691_);
lean_dec(v___x_1683_);
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_bs_1686_);
return v___x_1695_;
}
else
{
lean_object* v_v_1696_; lean_object* v_toConstantVal_1697_; lean_object* v_fst_1698_; lean_object* v_snd_1699_; lean_object* v_name_1700_; lean_object* v___x_1701_; lean_object* v_bs_x27_1702_; lean_object* v_a_1704_; uint8_t v___x_1709_; 
v_v_1696_ = lean_array_uget_borrowed(v_bs_1686_, v_i_1685_);
v_toConstantVal_1697_ = lean_ctor_get(v_a_1682_, 0);
v_fst_1698_ = lean_ctor_get(v_v_1696_, 0);
lean_inc(v_fst_1698_);
v_snd_1699_ = lean_ctor_get(v_v_1696_, 1);
lean_inc(v_snd_1699_);
v_name_1700_ = lean_ctor_get(v_toConstantVal_1697_, 0);
v___x_1701_ = lean_unsigned_to_nat(0u);
v_bs_x27_1702_ = lean_array_uset(v_bs_1686_, v_i_1685_, v___x_1701_);
v___x_1709_ = l_Lean_Expr_isAppOf(v_snd_1699_, v_name_1700_);
lean_dec(v_snd_1699_);
if (v___x_1709_ == 0)
{
lean_object* v_ref_1710_; lean_object* v_quotContext_1711_; lean_object* v_currMacroScope_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_ref_1710_ = lean_ctor_get(v___y_1691_, 5);
v_quotContext_1711_ = lean_ctor_get(v___y_1691_, 10);
v_currMacroScope_1712_ = lean_ctor_get(v___y_1691_, 11);
v___x_1713_ = l_Lean_SourceInfo_fromRef(v_ref_1710_, v___x_1709_);
v___x_1714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1715_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_1716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
lean_inc(v_currMacroScope_1712_);
lean_inc(v_quotContext_1711_);
v___x_1717_ = l_Lean_addMacroScope(v_quotContext_1711_, v___x_1716_, v_currMacroScope_1712_);
v___x_1718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1));
lean_inc(v___x_1713_);
v___x_1719_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1713_);
lean_ctor_set(v___x_1719_, 1, v___x_1715_);
lean_ctor_set(v___x_1719_, 2, v___x_1717_);
lean_ctor_set(v___x_1719_, 3, v___x_1718_);
v___x_1720_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1713_);
v___x_1721_ = l_Lean_Syntax_node1(v___x_1713_, v___x_1720_, v_fst_1698_);
v___x_1722_ = l_Lean_Syntax_node2(v___x_1713_, v___x_1714_, v___x_1719_, v___x_1721_);
v_a_1704_ = v___x_1722_;
goto v___jp_1703_;
}
else
{
lean_object* v_ref_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_ref_1723_ = lean_ctor_get(v___y_1691_, 5);
v___x_1724_ = 0;
v___x_1725_ = l_Lean_SourceInfo_fromRef(v_ref_1723_, v___x_1724_);
v___x_1726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1727_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1725_);
v___x_1728_ = l_Lean_Syntax_node1(v___x_1725_, v___x_1727_, v_fst_1698_);
lean_inc(v___x_1683_);
v___x_1729_ = l_Lean_Syntax_node2(v___x_1725_, v___x_1726_, v___x_1683_, v___x_1728_);
v_a_1704_ = v___x_1729_;
goto v___jp_1703_;
}
v___jp_1703_:
{
size_t v___x_1705_; size_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1705_ = ((size_t)1ULL);
v___x_1706_ = lean_usize_add(v_i_1685_, v___x_1705_);
v___x_1707_ = lean_array_uset(v_bs_x27_1702_, v_i_1685_, v_a_1704_);
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg(v_a_1682_, v___x_1683_, v_sz_1684_, v___x_1706_, v___x_1707_, v___y_1691_);
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2___boxed(lean_object* v_a_1730_, lean_object* v___x_1731_, lean_object* v_sz_1732_, lean_object* v_i_1733_, lean_object* v_bs_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
size_t v_sz_boxed_1742_; size_t v_i_boxed_1743_; lean_object* v_res_1744_; 
v_sz_boxed_1742_ = lean_unbox_usize(v_sz_1732_);
lean_dec(v_sz_1732_);
v_i_boxed_1743_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_res_1744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2(v_a_1730_, v___x_1731_, v_sz_boxed_1742_, v_i_boxed_1743_, v_bs_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec_ref(v_a_1730_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___redArg(lean_object* v_userNames_1745_, lean_object* v_a_1746_, lean_object* v___x_1747_, lean_object* v_as_1748_, lean_object* v_i_1749_, lean_object* v_j_1750_, lean_object* v_bs_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_zero_1754_; uint8_t v_isZero_1755_; 
v_zero_1754_ = lean_unsigned_to_nat(0u);
v_isZero_1755_ = lean_nat_dec_eq(v_i_1749_, v_zero_1754_);
if (v_isZero_1755_ == 1)
{
lean_object* v___x_1756_; 
lean_dec_ref(v___y_1752_);
lean_dec(v_j_1750_);
lean_dec(v_i_1749_);
lean_dec(v___x_1747_);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v_bs_1751_);
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; lean_object* v_toConstantVal_1758_; lean_object* v_fst_1759_; lean_object* v_snd_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1823_; 
v___x_1757_ = lean_array_fget(v_as_1748_, v_j_1750_);
v_toConstantVal_1758_ = lean_ctor_get(v_a_1746_, 0);
v_fst_1759_ = lean_ctor_get(v___x_1757_, 0);
v_snd_1760_ = lean_ctor_get(v___x_1757_, 1);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1762_ = v___x_1757_;
v_isShared_1763_ = v_isSharedCheck_1823_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_snd_1760_);
lean_inc(v_fst_1759_);
lean_dec(v___x_1757_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1823_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v_name_1764_; lean_object* v___x_1765_; lean_object* v_one_1766_; lean_object* v_n_1767_; lean_object* v_a_1769_; uint8_t v___x_1803_; 
v_name_1764_ = lean_ctor_get(v_toConstantVal_1758_, 0);
v___x_1765_ = lean_box(0);
v_one_1766_ = lean_unsigned_to_nat(1u);
v_n_1767_ = lean_nat_sub(v_i_1749_, v_one_1766_);
lean_dec(v_i_1749_);
v___x_1803_ = l_Lean_Expr_isAppOf(v_snd_1760_, v_name_1764_);
lean_dec(v_snd_1760_);
if (v___x_1803_ == 0)
{
lean_object* v_ref_1804_; lean_object* v_quotContext_1805_; lean_object* v_currMacroScope_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v_ref_1804_ = lean_ctor_get(v___y_1752_, 5);
v_quotContext_1805_ = lean_ctor_get(v___y_1752_, 10);
v_currMacroScope_1806_ = lean_ctor_get(v___y_1752_, 11);
v___x_1807_ = l_Lean_SourceInfo_fromRef(v_ref_1804_, v___x_1803_);
v___x_1808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1809_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_1810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
lean_inc(v_currMacroScope_1806_);
lean_inc(v_quotContext_1805_);
v___x_1811_ = l_Lean_addMacroScope(v_quotContext_1805_, v___x_1810_, v_currMacroScope_1806_);
v___x_1812_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1));
lean_inc(v___x_1807_);
v___x_1813_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1807_);
lean_ctor_set(v___x_1813_, 1, v___x_1809_);
lean_ctor_set(v___x_1813_, 2, v___x_1811_);
lean_ctor_set(v___x_1813_, 3, v___x_1812_);
v___x_1814_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1807_);
v___x_1815_ = l_Lean_Syntax_node1(v___x_1807_, v___x_1814_, v_fst_1759_);
v___x_1816_ = l_Lean_Syntax_node2(v___x_1807_, v___x_1808_, v___x_1813_, v___x_1815_);
v_a_1769_ = v___x_1816_;
goto v___jp_1768_;
}
else
{
lean_object* v_ref_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v_ref_1817_ = lean_ctor_get(v___y_1752_, 5);
v___x_1818_ = l_Lean_SourceInfo_fromRef(v_ref_1817_, v_isZero_1755_);
v___x_1819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1820_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1818_);
v___x_1821_ = l_Lean_Syntax_node1(v___x_1818_, v___x_1820_, v_fst_1759_);
lean_inc(v___x_1747_);
v___x_1822_ = l_Lean_Syntax_node2(v___x_1818_, v___x_1819_, v___x_1747_, v___x_1821_);
v_a_1769_ = v___x_1822_;
goto v___jp_1768_;
}
v___jp_1768_:
{
lean_object* v_ref_1770_; lean_object* v_quotContext_1771_; lean_object* v_currMacroScope_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
v_ref_1770_ = lean_ctor_get(v___y_1752_, 5);
v_quotContext_1771_ = lean_ctor_get(v___y_1752_, 10);
v_currMacroScope_1772_ = lean_ctor_get(v___y_1752_, 11);
v___x_1773_ = l_Lean_SourceInfo_fromRef(v_ref_1770_, v_isZero_1755_);
v___x_1774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4));
v___x_1775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_1776_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_1773_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 2);
lean_ctor_set(v___x_1762_, 1, v___x_1776_);
lean_ctor_set(v___x_1762_, 0, v___x_1773_);
v___x_1778_ = v___x_1762_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1779_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_1780_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
lean_inc(v_currMacroScope_1772_);
lean_inc(v_quotContext_1771_);
v___x_1781_ = l_Lean_addMacroScope(v_quotContext_1771_, v___x_1765_, v_currMacroScope_1772_);
v___x_1782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__28));
lean_inc(v___x_1773_);
v___x_1783_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1773_);
lean_ctor_set(v___x_1783_, 1, v___x_1780_);
lean_ctor_set(v___x_1783_, 2, v___x_1781_);
lean_ctor_set(v___x_1783_, 3, v___x_1782_);
lean_inc(v___x_1773_);
v___x_1784_ = l_Lean_Syntax_node1(v___x_1773_, v___x_1779_, v___x_1783_);
lean_inc(v___x_1773_);
v___x_1785_ = l_Lean_Syntax_node2(v___x_1773_, v___x_1775_, v___x_1778_, v___x_1784_);
v___x_1786_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_1787_ = lean_array_get_borrowed(v___x_1765_, v_userNames_1745_, v_j_1750_);
lean_inc(v___x_1787_);
v___x_1788_ = lean_erase_macro_scopes(v___x_1787_);
v___x_1789_ = l_Lean_Name_getString_x21(v___x_1788_);
lean_dec(v___x_1788_);
v___x_1790_ = lean_box(2);
v___x_1791_ = l_Lean_Syntax_mkStrLit(v___x_1789_, v___x_1790_);
v___x_1792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
lean_inc(v___x_1773_);
v___x_1793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1773_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
lean_inc(v___x_1773_);
v___x_1794_ = l_Lean_Syntax_node1(v___x_1773_, v___x_1786_, v_a_1769_);
lean_inc(v___x_1773_);
v___x_1795_ = l_Lean_Syntax_node3(v___x_1773_, v___x_1786_, v___x_1791_, v___x_1793_, v___x_1794_);
v___x_1796_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_1773_);
v___x_1797_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1773_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = l_Lean_Syntax_node3(v___x_1773_, v___x_1774_, v___x_1785_, v___x_1795_, v___x_1797_);
v___x_1799_ = lean_nat_add(v_j_1750_, v_one_1766_);
lean_dec(v_j_1750_);
v___x_1800_ = lean_array_push(v_bs_1751_, v___x_1798_);
v_i_1749_ = v_n_1767_;
v_j_1750_ = v___x_1799_;
v_bs_1751_ = v___x_1800_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___redArg___boxed(lean_object* v_userNames_1824_, lean_object* v_a_1825_, lean_object* v___x_1826_, lean_object* v_as_1827_, lean_object* v_i_1828_, lean_object* v_j_1829_, lean_object* v_bs_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___redArg(v_userNames_1824_, v_a_1825_, v___x_1826_, v_as_1827_, v_i_1828_, v_j_1829_, v_bs_1830_, v___y_1831_);
lean_dec_ref(v_as_1827_);
lean_dec_ref(v_a_1825_);
lean_dec_ref(v_userNames_1824_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___redArg(lean_object* v_a_1834_, lean_object* v___x_1835_, lean_object* v_userNames_1836_, lean_object* v_as_1837_, lean_object* v_i_1838_, lean_object* v_j_1839_, lean_object* v_bs_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_zero_1848_; uint8_t v_isZero_1849_; 
v_zero_1848_ = lean_unsigned_to_nat(0u);
v_isZero_1849_ = lean_nat_dec_eq(v_i_1838_, v_zero_1848_);
if (v_isZero_1849_ == 1)
{
lean_object* v___x_1850_; 
lean_dec_ref(v___y_1845_);
lean_dec(v___x_1835_);
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v_bs_1840_);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; lean_object* v_toConstantVal_1852_; lean_object* v_fst_1853_; lean_object* v_snd_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1917_; 
v___x_1851_ = lean_array_fget(v_as_1837_, v_j_1839_);
v_toConstantVal_1852_ = lean_ctor_get(v_a_1834_, 0);
v_fst_1853_ = lean_ctor_get(v___x_1851_, 0);
v_snd_1854_ = lean_ctor_get(v___x_1851_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1856_ = v___x_1851_;
v_isShared_1857_ = v_isSharedCheck_1917_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_snd_1854_);
lean_inc(v_fst_1853_);
lean_dec(v___x_1851_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1917_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v_name_1858_; lean_object* v___x_1859_; lean_object* v_one_1860_; lean_object* v_n_1861_; lean_object* v_a_1863_; uint8_t v___x_1897_; 
v_name_1858_ = lean_ctor_get(v_toConstantVal_1852_, 0);
v___x_1859_ = lean_box(0);
v_one_1860_ = lean_unsigned_to_nat(1u);
v_n_1861_ = lean_nat_sub(v_i_1838_, v_one_1860_);
v___x_1897_ = l_Lean_Expr_isAppOf(v_snd_1854_, v_name_1858_);
lean_dec(v_snd_1854_);
if (v___x_1897_ == 0)
{
lean_object* v_ref_1898_; lean_object* v_quotContext_1899_; lean_object* v_currMacroScope_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_ref_1898_ = lean_ctor_get(v___y_1845_, 5);
v_quotContext_1899_ = lean_ctor_get(v___y_1845_, 10);
v_currMacroScope_1900_ = lean_ctor_get(v___y_1845_, 11);
v___x_1901_ = l_Lean_SourceInfo_fromRef(v_ref_1898_, v___x_1897_);
v___x_1902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1903_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_1904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
lean_inc(v_currMacroScope_1900_);
lean_inc(v_quotContext_1899_);
v___x_1905_ = l_Lean_addMacroScope(v_quotContext_1899_, v___x_1904_, v_currMacroScope_1900_);
v___x_1906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1));
lean_inc(v___x_1901_);
v___x_1907_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1901_);
lean_ctor_set(v___x_1907_, 1, v___x_1903_);
lean_ctor_set(v___x_1907_, 2, v___x_1905_);
lean_ctor_set(v___x_1907_, 3, v___x_1906_);
v___x_1908_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1901_);
v___x_1909_ = l_Lean_Syntax_node1(v___x_1901_, v___x_1908_, v_fst_1853_);
v___x_1910_ = l_Lean_Syntax_node2(v___x_1901_, v___x_1902_, v___x_1907_, v___x_1909_);
v_a_1863_ = v___x_1910_;
goto v___jp_1862_;
}
else
{
lean_object* v_ref_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_ref_1911_ = lean_ctor_get(v___y_1845_, 5);
v___x_1912_ = l_Lean_SourceInfo_fromRef(v_ref_1911_, v_isZero_1849_);
v___x_1913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1914_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1912_);
v___x_1915_ = l_Lean_Syntax_node1(v___x_1912_, v___x_1914_, v_fst_1853_);
lean_inc(v___x_1835_);
v___x_1916_ = l_Lean_Syntax_node2(v___x_1912_, v___x_1913_, v___x_1835_, v___x_1915_);
v_a_1863_ = v___x_1916_;
goto v___jp_1862_;
}
v___jp_1862_:
{
lean_object* v_ref_1864_; lean_object* v_quotContext_1865_; lean_object* v_currMacroScope_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v_ref_1864_ = lean_ctor_get(v___y_1845_, 5);
v_quotContext_1865_ = lean_ctor_get(v___y_1845_, 10);
v_currMacroScope_1866_ = lean_ctor_get(v___y_1845_, 11);
v___x_1867_ = l_Lean_SourceInfo_fromRef(v_ref_1864_, v_isZero_1849_);
v___x_1868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4));
v___x_1869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_1870_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_1867_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set_tag(v___x_1856_, 2);
lean_ctor_set(v___x_1856_, 1, v___x_1870_);
lean_ctor_set(v___x_1856_, 0, v___x_1867_);
v___x_1872_ = v___x_1856_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_1874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
lean_inc(v_currMacroScope_1866_);
lean_inc(v_quotContext_1865_);
v___x_1875_ = l_Lean_addMacroScope(v_quotContext_1865_, v___x_1859_, v_currMacroScope_1866_);
v___x_1876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__28));
lean_inc(v___x_1867_);
v___x_1877_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1867_);
lean_ctor_set(v___x_1877_, 1, v___x_1874_);
lean_ctor_set(v___x_1877_, 2, v___x_1875_);
lean_ctor_set(v___x_1877_, 3, v___x_1876_);
lean_inc(v___x_1867_);
v___x_1878_ = l_Lean_Syntax_node1(v___x_1867_, v___x_1873_, v___x_1877_);
lean_inc(v___x_1867_);
v___x_1879_ = l_Lean_Syntax_node2(v___x_1867_, v___x_1869_, v___x_1872_, v___x_1878_);
v___x_1880_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_1881_ = lean_array_get_borrowed(v___x_1859_, v_userNames_1836_, v_j_1839_);
lean_inc(v___x_1881_);
v___x_1882_ = lean_erase_macro_scopes(v___x_1881_);
v___x_1883_ = l_Lean_Name_getString_x21(v___x_1882_);
lean_dec(v___x_1882_);
v___x_1884_ = lean_box(2);
v___x_1885_ = l_Lean_Syntax_mkStrLit(v___x_1883_, v___x_1884_);
v___x_1886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
lean_inc(v___x_1867_);
v___x_1887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1867_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
lean_inc(v___x_1867_);
v___x_1888_ = l_Lean_Syntax_node1(v___x_1867_, v___x_1880_, v_a_1863_);
lean_inc(v___x_1867_);
v___x_1889_ = l_Lean_Syntax_node3(v___x_1867_, v___x_1880_, v___x_1885_, v___x_1887_, v___x_1888_);
v___x_1890_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_1867_);
v___x_1891_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1867_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_Lean_Syntax_node3(v___x_1867_, v___x_1868_, v___x_1879_, v___x_1889_, v___x_1891_);
v___x_1893_ = lean_nat_add(v_j_1839_, v_one_1860_);
v___x_1894_ = lean_array_push(v_bs_1840_, v___x_1892_);
v___x_1895_ = l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___redArg(v_userNames_1836_, v_a_1834_, v___x_1835_, v_as_1837_, v_n_1861_, v___x_1893_, v___x_1894_, v___y_1845_);
return v___x_1895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___redArg___boxed(lean_object* v_a_1918_, lean_object* v___x_1919_, lean_object* v_userNames_1920_, lean_object* v_as_1921_, lean_object* v_i_1922_, lean_object* v_j_1923_, lean_object* v_bs_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___redArg(v_a_1918_, v___x_1919_, v_userNames_1920_, v_as_1921_, v_i_1922_, v_j_1923_, v_bs_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v_j_1923_);
lean_dec(v_i_1922_);
lean_dec_ref(v_as_1921_);
lean_dec_ref(v_userNames_1920_);
lean_dec_ref(v_a_1918_);
return v_res_1932_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__5));
v___x_1950_ = l_String_toRawSubstring_x27(v___x_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0(lean_object* v___x_1974_, lean_object* v_a_1975_, lean_object* v___x_1976_, lean_object* v_ctor_1977_, lean_object* v_args_1978_, lean_object* v_userNames_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_toConstantVal_1987_; lean_object* v_name_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2240_; 
v_toConstantVal_1987_ = lean_ctor_get(v_ctor_1977_, 0);
lean_inc_ref(v_toConstantVal_1987_);
lean_dec_ref(v_ctor_1977_);
v_name_1988_ = lean_ctor_get(v_toConstantVal_1987_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_toConstantVal_1987_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; lean_object* v_unused_2242_; 
v_unused_2241_ = lean_ctor_get(v_toConstantVal_1987_, 2);
lean_dec(v_unused_2241_);
v_unused_2242_ = lean_ctor_get(v_toConstantVal_1987_, 1);
lean_dec(v_unused_2242_);
v___x_1990_ = v_toConstantVal_1987_;
v_isShared_1991_ = v_isSharedCheck_2240_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_name_1988_);
lean_dec(v_toConstantVal_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2240_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; lean_object* v_a_1997_; lean_object* v_xs_2041_; lean_object* v_userNames_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; 
v___x_1992_ = lean_erase_macro_scopes(v_name_1988_);
v___x_1993_ = l_Lean_Name_getString_x21(v___x_1992_);
lean_dec(v___x_1992_);
v___x_1994_ = lean_array_get_size(v_args_1978_);
v___x_1995_ = lean_nat_dec_eq(v___x_1994_, v___x_1974_);
if (v___x_1995_ == 0)
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = lean_unsigned_to_nat(1u);
v___x_2115_ = lean_nat_dec_eq(v___x_1994_, v___x_2114_);
if (v___x_2115_ == 0)
{
if (lean_obj_tag(v_userNames_1979_) == 0)
{
size_t v_sz_2116_; size_t v___x_2117_; lean_object* v___x_2118_; 
lean_del_object(v___x_1990_);
v_sz_2116_ = lean_array_size(v_args_1978_);
v___x_2117_ = ((size_t)0ULL);
lean_inc_ref(v___y_1984_);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2(v_a_1975_, v___x_1976_, v_sz_2116_, v___x_2117_, v_args_1978_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2185_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2185_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2185_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_ref_2123_; lean_object* v_quotContext_2124_; lean_object* v_currMacroScope_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; size_t v_sz_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v_ref_2123_ = lean_ctor_get(v___y_1984_, 5);
lean_inc(v_ref_2123_);
v_quotContext_2124_ = lean_ctor_get(v___y_1984_, 10);
lean_inc(v_quotContext_2124_);
v_currMacroScope_2125_ = lean_ctor_get(v___y_1984_, 11);
lean_inc(v_currMacroScope_2125_);
lean_dec_ref(v___y_1984_);
v___x_2126_ = l_Lean_SourceInfo_fromRef(v_ref_2123_, v___x_2115_);
lean_dec(v_ref_2123_);
v___x_2127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2128_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3, &l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3_once, _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3);
v___x_2129_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__4));
lean_inc(v_currMacroScope_2125_);
lean_inc(v_quotContext_2124_);
v___x_2130_ = l_Lean_addMacroScope(v_quotContext_2124_, v___x_2129_, v_currMacroScope_2125_);
v___x_2131_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__7));
lean_inc(v___x_2126_);
v___x_2132_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2126_);
lean_ctor_set(v___x_2132_, 1, v___x_2128_);
lean_ctor_set(v___x_2132_, 2, v___x_2130_);
lean_ctor_set(v___x_2132_, 3, v___x_2131_);
v___x_2133_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1));
v___x_2135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_2126_);
v___x_2136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2126_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4));
v___x_2138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_2139_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_2126_);
v___x_2140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2126_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_2142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
v___x_2143_ = lean_box(0);
lean_inc(v_currMacroScope_2125_);
lean_inc(v_quotContext_2124_);
v___x_2144_ = l_Lean_addMacroScope(v_quotContext_2124_, v___x_2143_, v_currMacroScope_2125_);
v___x_2145_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__4));
lean_inc(v___x_2126_);
v___x_2146_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2126_);
lean_ctor_set(v___x_2146_, 1, v___x_2142_);
lean_ctor_set(v___x_2146_, 2, v___x_2144_);
lean_ctor_set(v___x_2146_, 3, v___x_2145_);
lean_inc(v___x_2126_);
v___x_2147_ = l_Lean_Syntax_node1(v___x_2126_, v___x_2141_, v___x_2146_);
lean_inc(v___x_2126_);
v___x_2148_ = l_Lean_Syntax_node2(v___x_2126_, v___x_2138_, v___x_2140_, v___x_2147_);
v___x_2149_ = lean_box(2);
v___x_2150_ = l_Lean_Syntax_mkStrLit(v___x_1993_, v___x_2149_);
v___x_2151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
lean_inc(v___x_2126_);
v___x_2152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2126_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__6, &l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__6_once, _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__6);
v___x_2154_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__8));
v___x_2155_ = l_Lean_addMacroScope(v_quotContext_2124_, v___x_2154_, v_currMacroScope_2125_);
v___x_2156_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__13));
lean_inc(v___x_2126_);
v___x_2157_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2126_);
lean_ctor_set(v___x_2157_, 1, v___x_2153_);
lean_ctor_set(v___x_2157_, 2, v___x_2155_);
lean_ctor_set(v___x_2157_, 3, v___x_2156_);
v___x_2158_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__15));
v___x_2159_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__16));
lean_inc(v___x_2126_);
v___x_2160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2126_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v_sz_2162_ = lean_array_size(v_a_2119_);
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(v_sz_2162_, v___x_2117_, v_a_2119_);
v___x_2164_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6);
v___x_2165_ = l_Lean_mkSepArray(v___x_2163_, v___x_2164_);
lean_dec_ref(v___x_2163_);
v___x_2166_ = l_Array_append___redArg(v___x_2161_, v___x_2165_);
lean_dec_ref(v___x_2165_);
lean_inc(v___x_2126_);
v___x_2167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2126_);
lean_ctor_set(v___x_2167_, 1, v___x_2133_);
lean_ctor_set(v___x_2167_, 2, v___x_2166_);
v___x_2168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_2126_);
v___x_2169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2126_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
lean_inc_ref(v___x_2169_);
lean_inc(v___x_2126_);
v___x_2170_ = l_Lean_Syntax_node3(v___x_2126_, v___x_2158_, v___x_2160_, v___x_2167_, v___x_2169_);
lean_inc(v___x_2126_);
v___x_2171_ = l_Lean_Syntax_node1(v___x_2126_, v___x_2133_, v___x_2170_);
lean_inc(v___x_2126_);
v___x_2172_ = l_Lean_Syntax_node2(v___x_2126_, v___x_2127_, v___x_2157_, v___x_2171_);
lean_inc(v___x_2126_);
v___x_2173_ = l_Lean_Syntax_node1(v___x_2126_, v___x_2133_, v___x_2172_);
lean_inc(v___x_2126_);
v___x_2174_ = l_Lean_Syntax_node3(v___x_2126_, v___x_2133_, v___x_2150_, v___x_2152_, v___x_2173_);
v___x_2175_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_2126_);
v___x_2176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2126_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
lean_inc(v___x_2126_);
v___x_2177_ = l_Lean_Syntax_node3(v___x_2126_, v___x_2137_, v___x_2148_, v___x_2174_, v___x_2176_);
lean_inc(v___x_2126_);
v___x_2178_ = l_Lean_Syntax_node1(v___x_2126_, v___x_2133_, v___x_2177_);
lean_inc(v___x_2126_);
v___x_2179_ = l_Lean_Syntax_node3(v___x_2126_, v___x_2134_, v___x_2136_, v___x_2178_, v___x_2169_);
lean_inc(v___x_2126_);
v___x_2180_ = l_Lean_Syntax_node1(v___x_2126_, v___x_2133_, v___x_2179_);
v___x_2181_ = l_Lean_Syntax_node2(v___x_2126_, v___x_2127_, v___x_2132_, v___x_2180_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2181_);
v___x_2183_ = v___x_2121_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec_ref(v___x_1993_);
lean_dec_ref(v___y_1984_);
v_a_2186_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2118_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2118_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_object* v_val_2194_; 
v_val_2194_ = lean_ctor_get(v_userNames_1979_, 0);
v_xs_2041_ = v_args_1978_;
v_userNames_2042_ = v_val_2194_;
v___y_2043_ = v___y_1980_;
v___y_2044_ = v___y_1981_;
v___y_2045_ = v___y_1982_;
v___y_2046_ = v___y_1983_;
v___y_2047_ = v___y_1984_;
v___y_2048_ = v___y_1985_;
goto v___jp_2040_;
}
}
else
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_array_fget(v_args_1978_, v___x_1974_);
lean_dec_ref(v_args_1978_);
if (lean_obj_tag(v_userNames_1979_) == 0)
{
lean_object* v_toConstantVal_2196_; lean_object* v_fst_2197_; lean_object* v_snd_2198_; lean_object* v_name_2199_; uint8_t v___x_2200_; 
lean_del_object(v___x_1990_);
v_toConstantVal_2196_ = lean_ctor_get(v_a_1975_, 0);
v_fst_2197_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_fst_2197_);
v_snd_2198_ = lean_ctor_get(v___x_2195_, 1);
lean_inc(v_snd_2198_);
lean_dec(v___x_2195_);
v_name_2199_ = lean_ctor_get(v_toConstantVal_2196_, 0);
v___x_2200_ = l_Lean_Expr_isAppOf(v_snd_2198_, v_name_2199_);
lean_dec(v_snd_2198_);
if (v___x_2200_ == 0)
{
lean_object* v_ref_2201_; lean_object* v_quotContext_2202_; lean_object* v_currMacroScope_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec(v___x_1976_);
v_ref_2201_ = lean_ctor_get(v___y_1984_, 5);
v_quotContext_2202_ = lean_ctor_get(v___y_1984_, 10);
v_currMacroScope_2203_ = lean_ctor_get(v___y_1984_, 11);
v___x_2204_ = l_Lean_SourceInfo_fromRef(v_ref_2201_, v___x_2200_);
v___x_2205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2206_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_2207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
lean_inc(v_currMacroScope_2203_);
lean_inc(v_quotContext_2202_);
v___x_2208_ = l_Lean_addMacroScope(v_quotContext_2202_, v___x_2207_, v_currMacroScope_2203_);
v___x_2209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1));
lean_inc(v___x_2204_);
v___x_2210_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2204_);
lean_ctor_set(v___x_2210_, 1, v___x_2206_);
lean_ctor_set(v___x_2210_, 2, v___x_2208_);
lean_ctor_set(v___x_2210_, 3, v___x_2209_);
v___x_2211_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_2204_);
v___x_2212_ = l_Lean_Syntax_node1(v___x_2204_, v___x_2211_, v_fst_2197_);
v___x_2213_ = l_Lean_Syntax_node2(v___x_2204_, v___x_2205_, v___x_2210_, v___x_2212_);
v_a_1997_ = v___x_2213_;
goto v___jp_1996_;
}
else
{
lean_object* v_ref_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v_ref_2214_ = lean_ctor_get(v___y_1984_, 5);
v___x_2215_ = l_Lean_SourceInfo_fromRef(v_ref_2214_, v___x_1995_);
v___x_2216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2217_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_2215_);
v___x_2218_ = l_Lean_Syntax_node1(v___x_2215_, v___x_2217_, v_fst_2197_);
v___x_2219_ = l_Lean_Syntax_node2(v___x_2215_, v___x_2216_, v___x_1976_, v___x_2218_);
v_a_1997_ = v___x_2219_;
goto v___jp_1996_;
}
}
else
{
lean_object* v_val_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_val_2220_ = lean_ctor_get(v_userNames_1979_, 0);
v___x_2221_ = lean_mk_empty_array_with_capacity(v___x_2114_);
v___x_2222_ = lean_array_push(v___x_2221_, v___x_2195_);
v_xs_2041_ = v___x_2222_;
v_userNames_2042_ = v_val_2220_;
v___y_2043_ = v___y_1980_;
v___y_2044_ = v___y_1981_;
v___y_2045_ = v___y_1982_;
v___y_2046_ = v___y_1983_;
v___y_2047_ = v___y_1984_;
v___y_2048_ = v___y_1985_;
goto v___jp_2040_;
}
}
}
else
{
lean_object* v_ref_2223_; lean_object* v_quotContext_2224_; lean_object* v_currMacroScope_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_del_object(v___x_1990_);
lean_dec_ref(v_args_1978_);
lean_dec(v___x_1976_);
v_ref_2223_ = lean_ctor_get(v___y_1984_, 5);
lean_inc(v_ref_2223_);
v_quotContext_2224_ = lean_ctor_get(v___y_1984_, 10);
lean_inc(v_quotContext_2224_);
v_currMacroScope_2225_ = lean_ctor_get(v___y_1984_, 11);
lean_inc(v_currMacroScope_2225_);
lean_dec_ref(v___y_1984_);
v___x_2226_ = 0;
v___x_2227_ = l_Lean_SourceInfo_fromRef(v_ref_2223_, v___x_2226_);
lean_dec(v_ref_2223_);
v___x_2228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2229_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_2230_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
v___x_2231_ = l_Lean_addMacroScope(v_quotContext_2224_, v___x_2230_, v_currMacroScope_2225_);
v___x_2232_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1));
lean_inc(v___x_2227_);
v___x_2233_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2227_);
lean_ctor_set(v___x_2233_, 1, v___x_2229_);
lean_ctor_set(v___x_2233_, 2, v___x_2231_);
lean_ctor_set(v___x_2233_, 3, v___x_2232_);
v___x_2234_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2235_ = lean_box(2);
v___x_2236_ = l_Lean_Syntax_mkStrLit(v___x_1993_, v___x_2235_);
lean_inc(v___x_2227_);
v___x_2237_ = l_Lean_Syntax_node1(v___x_2227_, v___x_2234_, v___x_2236_);
v___x_2238_ = l_Lean_Syntax_node2(v___x_2227_, v___x_2228_, v___x_2233_, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
return v___x_2239_;
}
v___jp_1996_:
{
lean_object* v_ref_1998_; lean_object* v_quotContext_1999_; lean_object* v_currMacroScope_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_ref_1998_ = lean_ctor_get(v___y_1984_, 5);
lean_inc(v_ref_1998_);
v_quotContext_1999_ = lean_ctor_get(v___y_1984_, 10);
lean_inc(v_quotContext_1999_);
v_currMacroScope_2000_ = lean_ctor_get(v___y_1984_, 11);
lean_inc(v_currMacroScope_2000_);
lean_dec_ref(v___y_1984_);
v___x_2001_ = l_Lean_SourceInfo_fromRef(v_ref_1998_, v___x_1995_);
lean_dec(v_ref_1998_);
v___x_2002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2003_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3, &l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3_once, _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3);
v___x_2004_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__4));
lean_inc(v_currMacroScope_2000_);
lean_inc(v_quotContext_1999_);
v___x_2005_ = l_Lean_addMacroScope(v_quotContext_1999_, v___x_2004_, v_currMacroScope_2000_);
v___x_2006_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__7));
lean_inc(v___x_2001_);
v___x_2007_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2001_);
lean_ctor_set(v___x_2007_, 1, v___x_2003_);
lean_ctor_set(v___x_2007_, 2, v___x_2005_);
lean_ctor_set(v___x_2007_, 3, v___x_2006_);
v___x_2008_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1));
v___x_2010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_2001_);
v___x_2011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2001_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4));
v___x_2013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_2014_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_2001_);
v___x_2015_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2001_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_2017_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
v___x_2018_ = lean_box(0);
v___x_2019_ = l_Lean_addMacroScope(v_quotContext_1999_, v___x_2018_, v_currMacroScope_2000_);
v___x_2020_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__4));
lean_inc(v___x_2001_);
v___x_2021_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2001_);
lean_ctor_set(v___x_2021_, 1, v___x_2017_);
lean_ctor_set(v___x_2021_, 2, v___x_2019_);
lean_ctor_set(v___x_2021_, 3, v___x_2020_);
lean_inc(v___x_2001_);
v___x_2022_ = l_Lean_Syntax_node1(v___x_2001_, v___x_2016_, v___x_2021_);
lean_inc(v___x_2001_);
v___x_2023_ = l_Lean_Syntax_node2(v___x_2001_, v___x_2013_, v___x_2015_, v___x_2022_);
v___x_2024_ = lean_box(2);
v___x_2025_ = l_Lean_Syntax_mkStrLit(v___x_1993_, v___x_2024_);
v___x_2026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
lean_inc(v___x_2001_);
v___x_2027_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2001_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
lean_inc(v___x_2001_);
v___x_2028_ = l_Lean_Syntax_node1(v___x_2001_, v___x_2008_, v_a_1997_);
lean_inc(v___x_2001_);
v___x_2029_ = l_Lean_Syntax_node3(v___x_2001_, v___x_2008_, v___x_2025_, v___x_2027_, v___x_2028_);
v___x_2030_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_2001_);
v___x_2031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2001_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
lean_inc(v___x_2001_);
v___x_2032_ = l_Lean_Syntax_node3(v___x_2001_, v___x_2012_, v___x_2023_, v___x_2029_, v___x_2031_);
lean_inc(v___x_2001_);
v___x_2033_ = l_Lean_Syntax_node1(v___x_2001_, v___x_2008_, v___x_2032_);
v___x_2034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_2001_);
v___x_2035_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2001_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
lean_inc(v___x_2001_);
v___x_2036_ = l_Lean_Syntax_node3(v___x_2001_, v___x_2009_, v___x_2011_, v___x_2033_, v___x_2035_);
lean_inc(v___x_2001_);
v___x_2037_ = l_Lean_Syntax_node1(v___x_2001_, v___x_2008_, v___x_2036_);
v___x_2038_ = l_Lean_Syntax_node2(v___x_2001_, v___x_2002_, v___x_2007_, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
v___jp_2040_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2113_; 
v___x_2049_ = lean_array_get_size(v_xs_2041_);
v___x_2050_ = lean_mk_empty_array_with_capacity(v___x_2049_);
lean_inc_ref(v___y_2047_);
v___x_2051_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___redArg(v_a_1975_, v___x_1976_, v_userNames_2042_, v_xs_2041_, v___x_2049_, v___x_1974_, v___x_2050_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec_ref(v_xs_2041_);
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2113_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2113_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_ref_2056_; lean_object* v_quotContext_2057_; lean_object* v_currMacroScope_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; size_t v_sz_2087_; size_t v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v_ref_2056_ = lean_ctor_get(v___y_2047_, 5);
lean_inc(v_ref_2056_);
v_quotContext_2057_ = lean_ctor_get(v___y_2047_, 10);
lean_inc(v_quotContext_2057_);
v_currMacroScope_2058_ = lean_ctor_get(v___y_2047_, 11);
lean_inc(v_currMacroScope_2058_);
lean_dec_ref(v___y_2047_);
v___x_2059_ = l_Lean_SourceInfo_fromRef(v_ref_2056_, v___x_1995_);
lean_dec(v_ref_2056_);
v___x_2060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2061_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3, &l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3_once, _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3);
v___x_2062_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__4));
lean_inc(v_currMacroScope_2058_);
lean_inc(v_quotContext_2057_);
v___x_2063_ = l_Lean_addMacroScope(v_quotContext_2057_, v___x_2062_, v_currMacroScope_2058_);
v___x_2064_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__7));
lean_inc(v___x_2059_);
v___x_2065_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2059_);
lean_ctor_set(v___x_2065_, 1, v___x_2061_);
lean_ctor_set(v___x_2065_, 2, v___x_2063_);
lean_ctor_set(v___x_2065_, 3, v___x_2064_);
v___x_2066_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1));
v___x_2068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_2059_);
v___x_2069_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2059_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4));
v___x_2071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_2072_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_2059_);
v___x_2073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2059_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_2075_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
v___x_2076_ = lean_box(0);
v___x_2077_ = l_Lean_addMacroScope(v_quotContext_2057_, v___x_2076_, v_currMacroScope_2058_);
v___x_2078_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__4));
lean_inc(v___x_2059_);
v___x_2079_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2059_);
lean_ctor_set(v___x_2079_, 1, v___x_2075_);
lean_ctor_set(v___x_2079_, 2, v___x_2077_);
lean_ctor_set(v___x_2079_, 3, v___x_2078_);
lean_inc(v___x_2059_);
v___x_2080_ = l_Lean_Syntax_node1(v___x_2059_, v___x_2074_, v___x_2079_);
lean_inc(v___x_2059_);
v___x_2081_ = l_Lean_Syntax_node2(v___x_2059_, v___x_2071_, v___x_2073_, v___x_2080_);
v___x_2082_ = lean_box(2);
v___x_2083_ = l_Lean_Syntax_mkStrLit(v___x_1993_, v___x_2082_);
v___x_2084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
lean_inc(v___x_2059_);
v___x_2085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2059_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v_sz_2087_ = lean_array_size(v_a_2052_);
v___x_2088_ = ((size_t)0ULL);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(v_sz_2087_, v___x_2088_, v_a_2052_);
v___x_2090_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6);
v___x_2091_ = l_Lean_mkSepArray(v___x_2089_, v___x_2090_);
lean_dec_ref(v___x_2089_);
v___x_2092_ = l_Array_append___redArg(v___x_2086_, v___x_2091_);
lean_dec_ref(v___x_2091_);
lean_inc(v___x_2059_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set_tag(v___x_1990_, 1);
lean_ctor_set(v___x_1990_, 2, v___x_2092_);
lean_ctor_set(v___x_1990_, 1, v___x_2066_);
lean_ctor_set(v___x_1990_, 0, v___x_2059_);
v___x_2094_ = v___x_1990_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2059_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_2059_);
v___x_2096_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2059_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
lean_inc_ref(v___x_2096_);
lean_inc_ref(v___x_2069_);
lean_inc(v___x_2059_);
v___x_2097_ = l_Lean_Syntax_node3(v___x_2059_, v___x_2067_, v___x_2069_, v___x_2094_, v___x_2096_);
lean_inc(v___x_2059_);
v___x_2098_ = l_Lean_Syntax_node1(v___x_2059_, v___x_2066_, v___x_2097_);
lean_inc_ref(v___x_2065_);
lean_inc(v___x_2059_);
v___x_2099_ = l_Lean_Syntax_node2(v___x_2059_, v___x_2060_, v___x_2065_, v___x_2098_);
lean_inc(v___x_2059_);
v___x_2100_ = l_Lean_Syntax_node1(v___x_2059_, v___x_2066_, v___x_2099_);
lean_inc(v___x_2059_);
v___x_2101_ = l_Lean_Syntax_node3(v___x_2059_, v___x_2066_, v___x_2083_, v___x_2085_, v___x_2100_);
v___x_2102_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_2059_);
v___x_2103_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2059_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
lean_inc(v___x_2059_);
v___x_2104_ = l_Lean_Syntax_node3(v___x_2059_, v___x_2070_, v___x_2081_, v___x_2101_, v___x_2103_);
lean_inc(v___x_2059_);
v___x_2105_ = l_Lean_Syntax_node1(v___x_2059_, v___x_2066_, v___x_2104_);
lean_inc(v___x_2059_);
v___x_2106_ = l_Lean_Syntax_node3(v___x_2059_, v___x_2067_, v___x_2069_, v___x_2105_, v___x_2096_);
lean_inc(v___x_2059_);
v___x_2107_ = l_Lean_Syntax_node1(v___x_2059_, v___x_2066_, v___x_2106_);
v___x_2108_ = l_Lean_Syntax_node2(v___x_2059_, v___x_2060_, v___x_2065_, v___x_2107_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2108_);
v___x_2110_ = v___x_2054_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___boxed(lean_object* v___x_2243_, lean_object* v_a_2244_, lean_object* v___x_2245_, lean_object* v_ctor_2246_, lean_object* v_args_2247_, lean_object* v_userNames_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0(v___x_2243_, v_a_2244_, v___x_2245_, v_ctor_2246_, v_args_2247_, v_userNames_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v_userNames_2248_);
lean_dec_ref(v_a_2244_);
lean_dec(v___x_2243_);
return v_res_2256_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__0));
v___x_2259_ = l_Lean_stringToMessageData(v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0(lean_object* v_constName_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; lean_object* v_env_2269_; lean_object* v___x_2270_; 
v___x_2268_ = lean_st_ref_get(v___y_2266_);
v_env_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc_ref(v_env_2269_);
lean_dec(v___x_2268_);
lean_inc(v_constName_2260_);
v___x_2270_ = l_Lean_isInductiveCore_x3f(v_env_2269_, v_constName_2260_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v___x_2271_; uint8_t v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2271_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1);
v___x_2272_ = 0;
v___x_2273_ = l_Lean_MessageData_ofConstName(v_constName_2260_, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2271_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__1);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg(v___x_2276_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2277_;
}
else
{
lean_object* v_val_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v___y_2261_);
lean_dec(v_constName_2260_);
v_val_2278_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2270_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_val_2278_);
lean_dec(v___x_2270_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set_tag(v___x_2280_, 0);
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_val_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___boxed(lean_object* v_constName_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0(v_constName_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct(lean_object* v_ctx_2308_, lean_object* v_header_2309_, lean_object* v_indName_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v___x_2318_; 
lean_inc_ref(v_a_2311_);
v___x_2318_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0(v_indName_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___x_2318_);
lean_inc(v_a_2319_);
v___x_2320_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2309_, v_a_2319_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v_auxFunNames_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___f_2327_; lean_object* v___x_2328_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref(v___x_2320_);
v_auxFunNames_2322_ = lean_ctor_get(v_ctx_2308_, 2);
v___x_2323_ = lean_box(0);
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = lean_array_get_borrowed(v___x_2323_, v_auxFunNames_2322_, v___x_2324_);
lean_inc(v___x_2325_);
v___x_2326_ = lean_mk_syntax_ident(v___x_2325_);
lean_inc(v_a_2319_);
v___f_2327_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___boxed), 13, 3);
lean_closure_set(v___f_2327_, 0, v___x_2324_);
lean_closure_set(v___f_2327_, 1, v_a_2319_);
lean_closure_set(v___f_2327_, 2, v___x_2326_);
lean_inc_ref(v_a_2315_);
v___x_2328_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts(v_a_2319_, v___f_2327_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2359_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2359_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2359_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v_ref_2333_; uint8_t v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; size_t v_sz_2342_; size_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v_ref_2333_ = lean_ctor_get(v_a_2315_, 5);
lean_inc(v_ref_2333_);
lean_dec_ref(v_a_2315_);
v___x_2334_ = 0;
v___x_2335_ = l_Lean_SourceInfo_fromRef(v_ref_2333_, v___x_2334_);
lean_dec(v_ref_2333_);
v___x_2336_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__0));
v___x_2337_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1));
lean_inc(v___x_2335_);
v___x_2338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2335_);
lean_ctor_set(v___x_2338_, 1, v___x_2336_);
v___x_2339_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2340_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_2335_);
v___x_2341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2335_);
lean_ctor_set(v___x_2341_, 1, v___x_2339_);
lean_ctor_set(v___x_2341_, 2, v___x_2340_);
v_sz_2342_ = lean_array_size(v_a_2321_);
v___x_2343_ = ((size_t)0ULL);
v___x_2344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(v_sz_2342_, v___x_2343_, v_a_2321_);
v___x_2345_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6);
v___x_2346_ = l_Lean_mkSepArray(v___x_2344_, v___x_2345_);
lean_dec_ref(v___x_2344_);
v___x_2347_ = l_Array_append___redArg(v___x_2340_, v___x_2346_);
lean_dec_ref(v___x_2346_);
lean_inc(v___x_2335_);
v___x_2348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2335_);
lean_ctor_set(v___x_2348_, 1, v___x_2339_);
lean_ctor_set(v___x_2348_, 2, v___x_2347_);
v___x_2349_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__2));
lean_inc(v___x_2335_);
v___x_2350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2335_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4));
v___x_2352_ = l_Array_append___redArg(v___x_2340_, v_a_2329_);
lean_dec(v_a_2329_);
lean_inc(v___x_2335_);
v___x_2353_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2335_);
lean_ctor_set(v___x_2353_, 1, v___x_2339_);
lean_ctor_set(v___x_2353_, 2, v___x_2352_);
lean_inc(v___x_2335_);
v___x_2354_ = l_Lean_Syntax_node1(v___x_2335_, v___x_2351_, v___x_2353_);
lean_inc_ref(v___x_2341_);
v___x_2355_ = l_Lean_Syntax_node6(v___x_2335_, v___x_2337_, v___x_2338_, v___x_2341_, v___x_2341_, v___x_2348_, v___x_2350_, v___x_2354_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2355_);
v___x_2357_ = v___x_2331_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2315_);
v_a_2360_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2328_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2328_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_a_2319_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
v_a_2368_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2320_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2320_);
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
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec_ref(v_header_2309_);
v_a_2376_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2318_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2318_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___boxed(lean_object* v_ctx_2384_, lean_object* v_header_2385_, lean_object* v_indName_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct(v_ctx_2384_, v_header_2385_, v_indName_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec_ref(v_ctx_2384_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1(lean_object* v_a_2395_, lean_object* v___x_2396_, lean_object* v_userNames_2397_, lean_object* v_as_2398_, lean_object* v_i_2399_, lean_object* v_j_2400_, lean_object* v_inv_2401_, lean_object* v_bs_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___redArg(v_a_2395_, v___x_2396_, v_userNames_2397_, v_as_2398_, v_i_2399_, v_j_2400_, v_bs_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___boxed(lean_object* v_a_2411_, lean_object* v___x_2412_, lean_object* v_userNames_2413_, lean_object* v_as_2414_, lean_object* v_i_2415_, lean_object* v_j_2416_, lean_object* v_inv_2417_, lean_object* v_bs_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1(v_a_2411_, v___x_2412_, v_userNames_2413_, v_as_2414_, v_i_2415_, v_j_2416_, v_inv_2417_, v_bs_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v_j_2416_);
lean_dec(v_i_2415_);
lean_dec_ref(v_as_2414_);
lean_dec_ref(v_userNames_2413_);
lean_dec_ref(v_a_2411_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1(lean_object* v_userNames_2427_, lean_object* v_a_2428_, lean_object* v___x_2429_, lean_object* v_as_2430_, lean_object* v_i_2431_, lean_object* v_j_2432_, lean_object* v_inv_2433_, lean_object* v_bs_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___redArg(v_userNames_2427_, v_a_2428_, v___x_2429_, v_as_2430_, v_i_2431_, v_j_2432_, v_bs_2434_, v___y_2439_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___boxed(lean_object* v_userNames_2443_, lean_object* v_a_2444_, lean_object* v___x_2445_, lean_object* v_as_2446_, lean_object* v_i_2447_, lean_object* v_j_2448_, lean_object* v_inv_2449_, lean_object* v_bs_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1(v_userNames_2443_, v_a_2444_, v___x_2445_, v_as_2446_, v_i_2447_, v_j_2448_, v_inv_2449_, v_bs_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec_ref(v_as_2446_);
lean_dec_ref(v_a_2444_);
lean_dec_ref(v_userNames_2443_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3(lean_object* v_a_2459_, lean_object* v___x_2460_, size_t v_sz_2461_, size_t v_i_2462_, lean_object* v_bs_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg(v_a_2459_, v___x_2460_, v_sz_2461_, v_i_2462_, v_bs_2463_, v___y_2468_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___boxed(lean_object* v_a_2472_, lean_object* v___x_2473_, lean_object* v_sz_2474_, lean_object* v_i_2475_, lean_object* v_bs_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
size_t v_sz_boxed_2484_; size_t v_i_boxed_2485_; lean_object* v_res_2486_; 
v_sz_boxed_2484_ = lean_unbox_usize(v_sz_2474_);
lean_dec(v_sz_2474_);
v_i_boxed_2485_ = lean_unbox_usize(v_i_2475_);
lean_dec(v_i_2475_);
v_res_2486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3(v_a_2472_, v___x_2473_, v_sz_boxed_2484_, v_i_boxed_2485_, v_bs_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec_ref(v_a_2472_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2(lean_object* v___x_2507_, size_t v_sz_2508_, size_t v_i_2509_, lean_object* v_bs_2510_){
_start:
{
uint8_t v___x_2511_; 
v___x_2511_ = lean_usize_dec_lt(v_i_2509_, v_sz_2508_);
if (v___x_2511_ == 0)
{
lean_dec(v___x_2507_);
return v_bs_2510_;
}
else
{
lean_object* v_v_2512_; lean_object* v_fst_2513_; lean_object* v_snd_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2539_; 
v_v_2512_ = lean_array_uget(v_bs_2510_, v_i_2509_);
v_fst_2513_ = lean_ctor_get(v_v_2512_, 0);
v_snd_2514_ = lean_ctor_get(v_v_2512_, 1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_v_2512_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2516_ = v_v_2512_;
v_isShared_2517_ = v_isSharedCheck_2539_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_snd_2514_);
lean_inc(v_fst_2513_);
lean_dec(v_v_2512_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2539_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v_bs_x27_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2518_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2519_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v___x_2520_ = lean_unsigned_to_nat(0u);
v_bs_x27_2521_ = lean_array_uset(v_bs_2510_, v_i_2509_, v___x_2520_);
v___x_2522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1));
v___x_2523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3));
v___x_2524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__4));
lean_inc(v___x_2507_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set_tag(v___x_2516_, 2);
lean_ctor_set(v___x_2516_, 1, v___x_2524_);
lean_ctor_set(v___x_2516_, 0, v___x_2507_);
v___x_2526_ = v___x_2516_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; size_t v___x_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
lean_inc(v___x_2507_);
v___x_2527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2507_);
lean_ctor_set(v___x_2527_, 1, v___x_2518_);
lean_ctor_set(v___x_2527_, 2, v___x_2519_);
v___x_2528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6));
v___x_2529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__7));
lean_inc(v___x_2507_);
v___x_2530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2507_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
lean_inc_ref(v___x_2527_);
lean_inc(v___x_2507_);
v___x_2531_ = l_Lean_Syntax_node4(v___x_2507_, v___x_2528_, v_fst_2513_, v___x_2527_, v___x_2530_, v_snd_2514_);
lean_inc_ref(v___x_2527_);
lean_inc(v___x_2507_);
v___x_2532_ = l_Lean_Syntax_node3(v___x_2507_, v___x_2523_, v___x_2526_, v___x_2527_, v___x_2531_);
lean_inc(v___x_2507_);
v___x_2533_ = l_Lean_Syntax_node2(v___x_2507_, v___x_2522_, v___x_2532_, v___x_2527_);
v___x_2534_ = ((size_t)1ULL);
v___x_2535_ = lean_usize_add(v_i_2509_, v___x_2534_);
v___x_2536_ = lean_array_uset(v_bs_x27_2521_, v_i_2509_, v___x_2533_);
v_i_2509_ = v___x_2535_;
v_bs_2510_ = v___x_2536_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___boxed(lean_object* v___x_2540_, lean_object* v_sz_2541_, lean_object* v_i_2542_, lean_object* v_bs_2543_){
_start:
{
size_t v_sz_boxed_2544_; size_t v_i_boxed_2545_; lean_object* v_res_2546_; 
v_sz_boxed_2544_ = lean_unbox_usize(v_sz_2541_);
lean_dec(v_sz_2541_);
v_i_boxed_2545_ = lean_unbox_usize(v_i_2542_);
lean_dec(v_i_2542_);
v_res_2546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2(v___x_2540_, v_sz_boxed_2544_, v_i_boxed_2545_, v_bs_2543_);
return v_res_2546_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__0));
v___x_2549_ = l_String_toRawSubstring_x27(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__9));
v___x_2573_ = l_String_toRawSubstring_x27(v___x_2572_);
return v___x_2573_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__21(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__20));
v___x_2599_ = l_String_toRawSubstring_x27(v___x_2598_);
return v___x_2599_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__26(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__25));
v___x_2607_ = l_String_toRawSubstring_x27(v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg(lean_object* v_indName_2626_, size_t v_sz_2627_, size_t v_i_2628_, lean_object* v_bs_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
uint8_t v___x_2633_; 
v___x_2633_ = lean_usize_dec_lt(v_i_2628_, v_sz_2627_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; 
lean_dec_ref(v___y_2630_);
lean_dec(v_indName_2626_);
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_bs_2629_);
return v___x_2634_;
}
else
{
lean_object* v_v_2635_; lean_object* v___x_2636_; 
v_v_2635_ = lean_array_uget(v_bs_2629_, v_i_2628_);
lean_inc(v_v_2635_);
v___x_2636_ = l_Lean_Elab_Deriving_FromToJson_mkJsonField(v_v_2635_, v___y_2630_, v___y_2631_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v_ref_2638_; lean_object* v_quotContext_2639_; lean_object* v_currMacroScope_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v_snd_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2744_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref(v___x_2636_);
v_ref_2638_ = lean_ctor_get(v___y_2630_, 5);
v_quotContext_2639_ = lean_ctor_get(v___y_2630_, 10);
v_currMacroScope_2640_ = lean_ctor_get(v___y_2630_, 11);
v___x_2641_ = 0;
v___x_2642_ = l_Lean_SourceInfo_fromRef(v_ref_2638_, v___x_2641_);
v___x_2643_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2644_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__1);
v___x_2645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v_currMacroScope_2640_);
lean_inc(v_quotContext_2639_);
v___x_2646_ = l_Lean_addMacroScope(v_quotContext_2639_, v___x_2645_, v_currMacroScope_2640_);
v___x_2647_ = lean_box(0);
v___x_2648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__5));
lean_inc(v___x_2642_);
v___x_2649_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2642_);
lean_ctor_set(v___x_2649_, 1, v___x_2644_);
lean_ctor_set(v___x_2649_, 2, v___x_2646_);
lean_ctor_set(v___x_2649_, 3, v___x_2648_);
v___x_2650_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10);
v___x_2651_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__11));
lean_inc(v_currMacroScope_2640_);
lean_inc(v_quotContext_2639_);
v___x_2652_ = l_Lean_addMacroScope(v_quotContext_2639_, v___x_2651_, v_currMacroScope_2640_);
v___x_2653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__6));
lean_inc(v___x_2642_);
v___x_2654_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2642_);
lean_ctor_set(v___x_2654_, 1, v___x_2650_);
lean_ctor_set(v___x_2654_, 2, v___x_2652_);
lean_ctor_set(v___x_2654_, 3, v___x_2653_);
v_snd_2655_ = lean_ctor_get(v_a_2637_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_a_2637_);
if (v_isSharedCheck_2744_ == 0)
{
lean_object* v_unused_2745_; 
v_unused_2745_ = lean_ctor_get(v_a_2637_, 0);
lean_dec(v_unused_2745_);
v___x_2657_ = v_a_2637_;
v_isShared_2658_ = v_isSharedCheck_2744_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_snd_2655_);
lean_dec(v_a_2637_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2744_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__2));
lean_inc(v___x_2642_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set_tag(v___x_2657_, 2);
lean_ctor_set(v___x_2657_, 1, v___x_2659_);
lean_ctor_set(v___x_2657_, 0, v___x_2642_);
v___x_2661_ = v___x_2657_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2662_; lean_object* v_bs_x27_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; size_t v___x_2739_; size_t v___x_2740_; lean_object* v___x_2741_; 
v___x_2662_ = lean_unsigned_to_nat(0u);
v_bs_x27_2663_ = lean_array_uset(v_bs_2629_, v_i_2628_, v___x_2662_);
v___x_2664_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2665_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1));
lean_inc(v___x_2642_);
v___x_2666_ = l_Lean_Syntax_node1(v___x_2642_, v___x_2665_, v___x_2661_);
lean_inc(v___x_2642_);
v___x_2667_ = l_Lean_Syntax_node3(v___x_2642_, v___x_2664_, v___x_2654_, v___x_2666_, v_snd_2655_);
lean_inc(v___x_2642_);
v___x_2668_ = l_Lean_Syntax_node2(v___x_2642_, v___x_2643_, v___x_2649_, v___x_2667_);
v___x_2669_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_2670_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__1));
v___x_2671_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__10);
v___x_2672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__13));
lean_inc(v_currMacroScope_2640_);
lean_inc(v_quotContext_2639_);
v___x_2673_ = l_Lean_addMacroScope(v_quotContext_2639_, v___x_2672_, v_currMacroScope_2640_);
v___x_2674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__15));
lean_inc(v___x_2642_);
v___x_2675_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2642_);
lean_ctor_set(v___x_2675_, 1, v___x_2671_);
lean_ctor_set(v___x_2675_, 2, v___x_2673_);
lean_ctor_set(v___x_2675_, 3, v___x_2674_);
v___x_2676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41));
v___x_2677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_2678_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_2642_);
v___x_2679_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2642_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_2681_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
v___x_2682_ = lean_box(0);
lean_inc(v_currMacroScope_2640_);
lean_inc(v_quotContext_2639_);
v___x_2683_ = l_Lean_addMacroScope(v_quotContext_2639_, v___x_2682_, v_currMacroScope_2640_);
v___x_2684_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__4));
lean_inc(v___x_2642_);
v___x_2685_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2642_);
lean_ctor_set(v___x_2685_, 1, v___x_2681_);
lean_ctor_set(v___x_2685_, 2, v___x_2683_);
lean_ctor_set(v___x_2685_, 3, v___x_2684_);
lean_inc(v___x_2642_);
v___x_2686_ = l_Lean_Syntax_node1(v___x_2642_, v___x_2680_, v___x_2685_);
lean_inc(v___x_2642_);
v___x_2687_ = l_Lean_Syntax_node2(v___x_2642_, v___x_2677_, v___x_2679_, v___x_2686_);
v___x_2688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__16));
v___x_2689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17));
lean_inc(v___x_2642_);
v___x_2690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2642_);
lean_ctor_set(v___x_2690_, 1, v___x_2688_);
v___x_2691_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19));
v___x_2692_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__21, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__21);
v___x_2693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__22));
lean_inc(v_currMacroScope_2640_);
lean_inc(v_quotContext_2639_);
v___x_2694_ = l_Lean_addMacroScope(v_quotContext_2639_, v___x_2693_, v_currMacroScope_2640_);
lean_inc(v___x_2642_);
v___x_2695_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2642_);
lean_ctor_set(v___x_2695_, 1, v___x_2692_);
lean_ctor_set(v___x_2695_, 2, v___x_2694_);
lean_ctor_set(v___x_2695_, 3, v___x_2647_);
lean_inc_ref(v___x_2695_);
lean_inc(v___x_2642_);
v___x_2696_ = l_Lean_Syntax_node1(v___x_2642_, v___x_2664_, v___x_2695_);
v___x_2697_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_2642_);
v___x_2698_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2642_);
lean_ctor_set(v___x_2698_, 1, v___x_2664_);
lean_ctor_set(v___x_2698_, 2, v___x_2697_);
v___x_2699_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__7));
lean_inc(v___x_2642_);
v___x_2700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2642_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__24));
v___x_2702_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__26, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__26_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__26);
v___x_2703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__27));
lean_inc(v_currMacroScope_2640_);
lean_inc(v_quotContext_2639_);
v___x_2704_ = l_Lean_addMacroScope(v_quotContext_2639_, v___x_2703_, v_currMacroScope_2640_);
v___x_2705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__31));
lean_inc(v___x_2642_);
v___x_2706_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2642_);
lean_ctor_set(v___x_2706_, 1, v___x_2702_);
lean_ctor_set(v___x_2706_, 2, v___x_2704_);
lean_ctor_set(v___x_2706_, 3, v___x_2705_);
lean_inc(v_indName_2626_);
v___x_2707_ = l_Lean_instQuoteNameMkStr1___private__1(v_indName_2626_);
lean_inc(v___x_2642_);
v___x_2708_ = l_Lean_Syntax_node1(v___x_2642_, v___x_2664_, v___x_2707_);
lean_inc_ref(v___x_2706_);
lean_inc(v___x_2642_);
v___x_2709_ = l_Lean_Syntax_node2(v___x_2642_, v___x_2643_, v___x_2706_, v___x_2708_);
v___x_2710_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_2642_);
v___x_2711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2642_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
lean_inc_ref(v___x_2711_);
lean_inc(v___x_2687_);
lean_inc(v___x_2642_);
v___x_2712_ = l_Lean_Syntax_node3(v___x_2642_, v___x_2676_, v___x_2687_, v___x_2709_, v___x_2711_);
v___x_2713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__32));
lean_inc(v___x_2642_);
v___x_2714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2642_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
v___x_2715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__34));
v___x_2716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__35));
lean_inc(v___x_2642_);
v___x_2717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2642_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
lean_inc(v___x_2642_);
v___x_2718_ = l_Lean_Syntax_node1(v___x_2642_, v___x_2715_, v___x_2717_);
lean_inc_ref(v___x_2714_);
lean_inc(v___x_2642_);
v___x_2719_ = l_Lean_Syntax_node3(v___x_2642_, v___x_2701_, v___x_2712_, v___x_2714_, v___x_2718_);
v___x_2720_ = l_Lean_instQuoteNameMkStr1___private__1(v_v_2635_);
lean_inc(v___x_2642_);
v___x_2721_ = l_Lean_Syntax_node1(v___x_2642_, v___x_2664_, v___x_2720_);
lean_inc(v___x_2642_);
v___x_2722_ = l_Lean_Syntax_node2(v___x_2642_, v___x_2643_, v___x_2706_, v___x_2721_);
lean_inc_ref(v___x_2711_);
lean_inc(v___x_2687_);
lean_inc(v___x_2642_);
v___x_2723_ = l_Lean_Syntax_node3(v___x_2642_, v___x_2676_, v___x_2687_, v___x_2722_, v___x_2711_);
lean_inc_ref(v___x_2714_);
lean_inc(v___x_2642_);
v___x_2724_ = l_Lean_Syntax_node3(v___x_2642_, v___x_2701_, v___x_2719_, v___x_2714_, v___x_2723_);
v___x_2725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__36));
lean_inc(v___x_2642_);
v___x_2726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2642_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
lean_inc(v___x_2642_);
v___x_2727_ = l_Lean_Syntax_node1(v___x_2642_, v___x_2715_, v___x_2726_);
lean_inc_ref(v___x_2714_);
lean_inc(v___x_2642_);
v___x_2728_ = l_Lean_Syntax_node3(v___x_2642_, v___x_2701_, v___x_2724_, v___x_2714_, v___x_2727_);
lean_inc(v___x_2642_);
v___x_2729_ = l_Lean_Syntax_node3(v___x_2642_, v___x_2701_, v___x_2728_, v___x_2714_, v___x_2695_);
lean_inc(v___x_2642_);
v___x_2730_ = l_Lean_Syntax_node4(v___x_2642_, v___x_2691_, v___x_2696_, v___x_2698_, v___x_2700_, v___x_2729_);
lean_inc(v___x_2642_);
v___x_2731_ = l_Lean_Syntax_node2(v___x_2642_, v___x_2689_, v___x_2690_, v___x_2730_);
lean_inc(v___x_2642_);
v___x_2732_ = l_Lean_Syntax_node3(v___x_2642_, v___x_2676_, v___x_2687_, v___x_2731_, v___x_2711_);
lean_inc(v___x_2642_);
v___x_2733_ = l_Lean_Syntax_node1(v___x_2642_, v___x_2664_, v___x_2732_);
lean_inc(v___x_2642_);
v___x_2734_ = l_Lean_Syntax_node2(v___x_2642_, v___x_2643_, v___x_2675_, v___x_2733_);
v___x_2735_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__8));
lean_inc(v___x_2642_);
v___x_2736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2642_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
lean_inc(v___x_2642_);
v___x_2737_ = l_Lean_Syntax_node3(v___x_2642_, v___x_2670_, v___x_2734_, v___x_2736_, v___x_2668_);
v___x_2738_ = l_Lean_Syntax_node1(v___x_2642_, v___x_2669_, v___x_2737_);
v___x_2739_ = ((size_t)1ULL);
v___x_2740_ = lean_usize_add(v_i_2628_, v___x_2739_);
v___x_2741_ = lean_array_uset(v_bs_x27_2663_, v_i_2628_, v___x_2738_);
v_i_2628_ = v___x_2740_;
v_bs_2629_ = v___x_2741_;
goto _start;
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_v_2635_);
lean_dec_ref(v___y_2630_);
lean_dec_ref(v_bs_2629_);
lean_dec(v_indName_2626_);
v_a_2746_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2636_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2636_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___boxed(lean_object* v_indName_2754_, lean_object* v_sz_2755_, lean_object* v_i_2756_, lean_object* v_bs_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
size_t v_sz_boxed_2761_; size_t v_i_boxed_2762_; lean_object* v_res_2763_; 
v_sz_boxed_2761_ = lean_unbox_usize(v_sz_2755_);
lean_dec(v_sz_2755_);
v_i_boxed_2762_ = lean_unbox_usize(v_i_2756_);
lean_dec(v_i_2756_);
v_res_2763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg(v_indName_2754_, v_sz_boxed_2761_, v_i_boxed_2762_, v_bs_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3(lean_object* v___x_2783_, lean_object* v___x_2784_, size_t v_sz_2785_, size_t v_i_2786_, lean_object* v_bs_2787_){
_start:
{
uint8_t v___x_2788_; 
v___x_2788_ = lean_usize_dec_lt(v_i_2786_, v_sz_2785_);
if (v___x_2788_ == 0)
{
lean_dec(v___x_2784_);
lean_dec(v___x_2783_);
return v_bs_2787_;
}
else
{
lean_object* v_v_2789_; lean_object* v_fst_2790_; lean_object* v_snd_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2813_; 
v_v_2789_ = lean_array_uget(v_bs_2787_, v_i_2786_);
v_fst_2790_ = lean_ctor_get(v_v_2789_, 0);
v_snd_2791_ = lean_ctor_get(v_v_2789_, 1);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_v_2789_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2793_ = v_v_2789_;
v_isShared_2794_ = v_isSharedCheck_2813_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_snd_2791_);
lean_inc(v_fst_2790_);
lean_dec(v_v_2789_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2813_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v_bs_x27_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2795_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2796_ = lean_unsigned_to_nat(0u);
v_bs_x27_2797_ = lean_array_uset(v_bs_2787_, v_i_2786_, v___x_2796_);
v___x_2798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__1));
v___x_2799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__3));
lean_inc(v___x_2784_);
lean_inc(v___x_2783_);
v___x_2800_ = l_Lean_Syntax_node2(v___x_2783_, v___x_2799_, v_fst_2790_, v___x_2784_);
v___x_2801_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__5));
v___x_2802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6));
lean_inc(v___x_2783_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set_tag(v___x_2793_, 2);
lean_ctor_set(v___x_2793_, 1, v___x_2802_);
lean_ctor_set(v___x_2793_, 0, v___x_2783_);
v___x_2804_ = v___x_2793_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; size_t v___x_2808_; size_t v___x_2809_; lean_object* v___x_2810_; 
lean_inc(v___x_2784_);
lean_inc(v___x_2783_);
v___x_2805_ = l_Lean_Syntax_node3(v___x_2783_, v___x_2801_, v___x_2804_, v___x_2784_, v_snd_2791_);
lean_inc_n(v___x_2784_, 2);
lean_inc(v___x_2783_);
v___x_2806_ = l_Lean_Syntax_node3(v___x_2783_, v___x_2795_, v___x_2784_, v___x_2784_, v___x_2805_);
lean_inc(v___x_2783_);
v___x_2807_ = l_Lean_Syntax_node2(v___x_2783_, v___x_2798_, v___x_2800_, v___x_2806_);
v___x_2808_ = ((size_t)1ULL);
v___x_2809_ = lean_usize_add(v_i_2786_, v___x_2808_);
v___x_2810_ = lean_array_uset(v_bs_x27_2797_, v_i_2786_, v___x_2807_);
v_i_2786_ = v___x_2809_;
v_bs_2787_ = v___x_2810_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___boxed(lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v_sz_2816_, lean_object* v_i_2817_, lean_object* v_bs_2818_){
_start:
{
size_t v_sz_boxed_2819_; size_t v_i_boxed_2820_; lean_object* v_res_2821_; 
v_sz_boxed_2819_ = lean_unbox_usize(v_sz_2816_);
lean_dec(v_sz_2816_);
v_i_boxed_2820_ = lean_unbox_usize(v_i_2817_);
lean_dec(v_i_2817_);
v_res_2821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3(v___x_2814_, v___x_2815_, v_sz_boxed_2819_, v_i_boxed_2820_, v_bs_2818_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__1(size_t v_sz_2822_, size_t v_i_2823_, lean_object* v_bs_2824_){
_start:
{
uint8_t v___x_2825_; 
v___x_2825_ = lean_usize_dec_lt(v_i_2823_, v_sz_2822_);
if (v___x_2825_ == 0)
{
return v_bs_2824_;
}
else
{
lean_object* v_v_2826_; lean_object* v___x_2827_; lean_object* v_bs_x27_2828_; lean_object* v___x_2829_; size_t v___x_2830_; size_t v___x_2831_; lean_object* v___x_2832_; 
v_v_2826_ = lean_array_uget(v_bs_2824_, v_i_2823_);
v___x_2827_ = lean_unsigned_to_nat(0u);
v_bs_x27_2828_ = lean_array_uset(v_bs_2824_, v_i_2823_, v___x_2827_);
v___x_2829_ = lean_mk_syntax_ident(v_v_2826_);
v___x_2830_ = ((size_t)1ULL);
v___x_2831_ = lean_usize_add(v_i_2823_, v___x_2830_);
v___x_2832_ = lean_array_uset(v_bs_x27_2828_, v_i_2823_, v___x_2829_);
v_i_2823_ = v___x_2831_;
v_bs_2824_ = v___x_2832_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__1___boxed(lean_object* v_sz_2834_, lean_object* v_i_2835_, lean_object* v_bs_2836_){
_start:
{
size_t v_sz_boxed_2837_; size_t v_i_boxed_2838_; lean_object* v_res_2839_; 
v_sz_boxed_2837_ = lean_unbox_usize(v_sz_2834_);
lean_dec(v_sz_2834_);
v_i_boxed_2838_ = lean_unbox_usize(v_i_2835_);
lean_dec(v_i_2835_);
v_res_2839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__1(v_sz_boxed_2837_, v_i_boxed_2838_, v_bs_2836_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct(lean_object* v_indName_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v___x_2887_; lean_object* v_env_2888_; uint8_t v___x_2889_; lean_object* v___x_2890_; size_t v_sz_2891_; size_t v___x_2892_; lean_object* v___x_2893_; 
v___x_2887_ = lean_st_ref_get(v_a_2885_);
v_env_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc_ref(v_env_2888_);
lean_dec(v___x_2887_);
v___x_2889_ = 0;
lean_inc(v_indName_2879_);
v___x_2890_ = l_Lean_getStructureFieldsFlattened(v_env_2888_, v_indName_2879_, v___x_2889_);
v_sz_2891_ = lean_array_size(v___x_2890_);
v___x_2892_ = ((size_t)0ULL);
lean_inc_ref(v_a_2884_);
lean_inc_ref(v___x_2890_);
v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg(v_indName_2879_, v_sz_2891_, v___x_2892_, v___x_2890_, v_a_2884_, v_a_2885_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2943_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2943_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2943_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v_ref_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; size_t v_sz_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; size_t v_sz_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2941_; 
v_ref_2898_ = lean_ctor_get(v_a_2884_, 5);
lean_inc(v_ref_2898_);
lean_dec_ref(v_a_2884_);
v___x_2899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__1(v_sz_2891_, v___x_2892_, v___x_2890_);
v___x_2900_ = l_Lean_SourceInfo_fromRef(v_ref_2898_, v___x_2889_);
lean_dec(v_ref_2898_);
v___x_2901_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__0));
v___x_2902_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1));
lean_inc(v___x_2900_);
v___x_2903_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2900_);
lean_ctor_set(v___x_2903_, 1, v___x_2901_);
v___x_2904_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3));
v___x_2905_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2906_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v___x_2907_ = l_Array_zip___redArg(v___x_2899_, v_a_2894_);
lean_dec(v_a_2894_);
v_sz_2908_ = lean_array_size(v___x_2907_);
lean_inc(v___x_2900_);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2(v___x_2900_, v_sz_2908_, v___x_2892_, v___x_2907_);
v___x_2910_ = l_Array_append___redArg(v___x_2906_, v___x_2909_);
lean_dec_ref(v___x_2909_);
v___x_2911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1));
v___x_2912_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5));
v___x_2913_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__6));
lean_inc(v___x_2900_);
v___x_2914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2900_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__8));
v___x_2916_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__9));
lean_inc(v___x_2900_);
v___x_2917_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2900_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
lean_inc(v___x_2900_);
v___x_2918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2900_);
lean_ctor_set(v___x_2918_, 1, v___x_2905_);
lean_ctor_set(v___x_2918_, 2, v___x_2906_);
v___x_2919_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__11));
v___x_2920_ = l_Array_zip___redArg(v___x_2899_, v___x_2899_);
lean_dec_ref(v___x_2899_);
v_sz_2921_ = lean_array_size(v___x_2920_);
lean_inc_ref(v___x_2918_);
lean_inc(v___x_2900_);
v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3(v___x_2900_, v___x_2918_, v_sz_2921_, v___x_2892_, v___x_2920_);
v___x_2923_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6);
v___x_2924_ = l_Lean_mkSepArray(v___x_2922_, v___x_2923_);
lean_dec_ref(v___x_2922_);
v___x_2925_ = l_Array_append___redArg(v___x_2906_, v___x_2924_);
lean_dec_ref(v___x_2924_);
lean_inc(v___x_2900_);
v___x_2926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2900_);
lean_ctor_set(v___x_2926_, 1, v___x_2905_);
lean_ctor_set(v___x_2926_, 2, v___x_2925_);
lean_inc(v___x_2900_);
v___x_2927_ = l_Lean_Syntax_node1(v___x_2900_, v___x_2919_, v___x_2926_);
v___x_2928_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__13));
lean_inc_ref(v___x_2918_);
lean_inc(v___x_2900_);
v___x_2929_ = l_Lean_Syntax_node1(v___x_2900_, v___x_2928_, v___x_2918_);
v___x_2930_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__14));
lean_inc(v___x_2900_);
v___x_2931_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2900_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
lean_inc_ref_n(v___x_2918_, 2);
lean_inc(v___x_2900_);
v___x_2932_ = l_Lean_Syntax_node6(v___x_2900_, v___x_2915_, v___x_2917_, v___x_2918_, v___x_2927_, v___x_2929_, v___x_2918_, v___x_2931_);
lean_inc(v___x_2900_);
v___x_2933_ = l_Lean_Syntax_node1(v___x_2900_, v___x_2905_, v___x_2932_);
lean_inc(v___x_2900_);
v___x_2934_ = l_Lean_Syntax_node2(v___x_2900_, v___x_2912_, v___x_2914_, v___x_2933_);
lean_inc(v___x_2900_);
v___x_2935_ = l_Lean_Syntax_node2(v___x_2900_, v___x_2911_, v___x_2934_, v___x_2918_);
v___x_2936_ = lean_array_push(v___x_2910_, v___x_2935_);
lean_inc(v___x_2900_);
v___x_2937_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2900_);
lean_ctor_set(v___x_2937_, 1, v___x_2905_);
lean_ctor_set(v___x_2937_, 2, v___x_2936_);
lean_inc(v___x_2900_);
v___x_2938_ = l_Lean_Syntax_node1(v___x_2900_, v___x_2904_, v___x_2937_);
v___x_2939_ = l_Lean_Syntax_node2(v___x_2900_, v___x_2902_, v___x_2903_, v___x_2938_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2939_);
v___x_2941_ = v___x_2896_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_dec_ref(v___x_2890_);
lean_dec_ref(v_a_2884_);
v_a_2944_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2893_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2893_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___boxed(lean_object* v_indName_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct(v_indName_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
lean_dec(v_a_2958_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0(lean_object* v_indName_2961_, size_t v_sz_2962_, size_t v_i_2963_, lean_object* v_bs_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg(v_indName_2961_, v_sz_2962_, v_i_2963_, v_bs_2964_, v___y_2969_, v___y_2970_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___boxed(lean_object* v_indName_2973_, lean_object* v_sz_2974_, lean_object* v_i_2975_, lean_object* v_bs_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
size_t v_sz_boxed_2984_; size_t v_i_boxed_2985_; lean_object* v_res_2986_; 
v_sz_boxed_2984_ = lean_unbox_usize(v_sz_2974_);
lean_dec(v_sz_2974_);
v_i_boxed_2985_ = lean_unbox_usize(v_i_2975_);
lean_dec(v_i_2975_);
v_res_2986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0(v_indName_2973_, v_sz_boxed_2984_, v_i_boxed_2985_, v_bs_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__4(size_t v_sz_2987_, size_t v_i_2988_, lean_object* v_bs_2989_){
_start:
{
uint8_t v___x_2990_; 
v___x_2990_ = lean_usize_dec_lt(v_i_2988_, v_sz_2987_);
if (v___x_2990_ == 0)
{
return v_bs_2989_;
}
else
{
lean_object* v_v_2991_; lean_object* v___x_2992_; lean_object* v_bs_x27_2993_; lean_object* v___x_2994_; size_t v___x_2995_; size_t v___x_2996_; lean_object* v___x_2997_; 
v_v_2991_ = lean_array_uget(v_bs_2989_, v_i_2988_);
v___x_2992_ = lean_unsigned_to_nat(0u);
v_bs_x27_2993_ = lean_array_uset(v_bs_2989_, v_i_2988_, v___x_2992_);
v___x_2994_ = l_Lean_instQuoteNameMkStr1___private__1(v_v_2991_);
v___x_2995_ = ((size_t)1ULL);
v___x_2996_ = lean_usize_add(v_i_2988_, v___x_2995_);
v___x_2997_ = lean_array_uset(v_bs_x27_2993_, v_i_2988_, v___x_2994_);
v_i_2988_ = v___x_2996_;
v_bs_2989_ = v___x_2997_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__4___boxed(lean_object* v_sz_2999_, lean_object* v_i_3000_, lean_object* v_bs_3001_){
_start:
{
size_t v_sz_boxed_3002_; size_t v_i_boxed_3003_; lean_object* v_res_3004_; 
v_sz_boxed_3002_ = lean_unbox_usize(v_sz_2999_);
lean_dec(v_sz_2999_);
v_i_boxed_3003_ = lean_unbox_usize(v_i_3000_);
lean_dec(v_i_3000_);
v_res_3004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__4(v_sz_boxed_3002_, v_i_boxed_3003_, v_bs_3001_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__0(size_t v_sz_3005_, size_t v_i_3006_, lean_object* v_bs_3007_){
_start:
{
uint8_t v___x_3008_; 
v___x_3008_ = lean_usize_dec_lt(v_i_3006_, v_sz_3005_);
if (v___x_3008_ == 0)
{
return v_bs_3007_;
}
else
{
lean_object* v_v_3009_; lean_object* v_fst_3010_; lean_object* v___x_3011_; lean_object* v_bs_x27_3012_; size_t v___x_3013_; size_t v___x_3014_; lean_object* v___x_3015_; 
v_v_3009_ = lean_array_uget_borrowed(v_bs_3007_, v_i_3006_);
v_fst_3010_ = lean_ctor_get(v_v_3009_, 0);
lean_inc(v_fst_3010_);
v___x_3011_ = lean_unsigned_to_nat(0u);
v_bs_x27_3012_ = lean_array_uset(v_bs_3007_, v_i_3006_, v___x_3011_);
v___x_3013_ = ((size_t)1ULL);
v___x_3014_ = lean_usize_add(v_i_3006_, v___x_3013_);
v___x_3015_ = lean_array_uset(v_bs_x27_3012_, v_i_3006_, v_fst_3010_);
v_i_3006_ = v___x_3014_;
v_bs_3007_ = v___x_3015_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__0___boxed(lean_object* v_sz_3017_, lean_object* v_i_3018_, lean_object* v_bs_3019_){
_start:
{
size_t v_sz_boxed_3020_; size_t v_i_boxed_3021_; lean_object* v_res_3022_; 
v_sz_boxed_3020_ = lean_unbox_usize(v_sz_3017_);
lean_dec(v_sz_3017_);
v_i_boxed_3021_ = lean_unbox_usize(v_i_3018_);
lean_dec(v_i_3018_);
v_res_3022_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__0(v_sz_boxed_3020_, v_i_boxed_3021_, v_bs_3019_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__2(lean_object* v___x_3023_, lean_object* v___x_3024_, size_t v_sz_3025_, size_t v_i_3026_, lean_object* v_bs_3027_){
_start:
{
uint8_t v___x_3028_; 
v___x_3028_ = lean_usize_dec_lt(v_i_3026_, v_sz_3025_);
if (v___x_3028_ == 0)
{
lean_dec(v___x_3024_);
lean_dec(v___x_3023_);
return v_bs_3027_;
}
else
{
lean_object* v_v_3029_; lean_object* v_fst_3030_; lean_object* v_snd_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3053_; 
v_v_3029_ = lean_array_uget(v_bs_3027_, v_i_3026_);
v_fst_3030_ = lean_ctor_get(v_v_3029_, 0);
v_snd_3031_ = lean_ctor_get(v_v_3029_, 1);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_v_3029_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3033_ = v_v_3029_;
v_isShared_3034_ = v_isSharedCheck_3053_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_snd_3031_);
lean_inc(v_fst_3030_);
lean_dec(v_v_3029_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3053_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; lean_object* v_bs_x27_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
v___x_3035_ = lean_unsigned_to_nat(0u);
v_bs_x27_3036_ = lean_array_uset(v_bs_3027_, v_i_3026_, v___x_3035_);
v___x_3037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1));
v___x_3038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3));
v___x_3039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__4));
lean_inc(v___x_3023_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set_tag(v___x_3033_, 2);
lean_ctor_set(v___x_3033_, 1, v___x_3039_);
lean_ctor_set(v___x_3033_, 0, v___x_3023_);
v___x_3041_ = v___x_3033_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; size_t v___x_3048_; size_t v___x_3049_; lean_object* v___x_3050_; 
v___x_3042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6));
v___x_3043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__7));
lean_inc(v___x_3023_);
v___x_3044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3023_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
lean_inc(v___x_3024_);
lean_inc(v___x_3023_);
v___x_3045_ = l_Lean_Syntax_node4(v___x_3023_, v___x_3042_, v_fst_3030_, v___x_3024_, v___x_3044_, v_snd_3031_);
lean_inc(v___x_3024_);
lean_inc(v___x_3023_);
v___x_3046_ = l_Lean_Syntax_node3(v___x_3023_, v___x_3038_, v___x_3041_, v___x_3024_, v___x_3045_);
lean_inc(v___x_3024_);
lean_inc(v___x_3023_);
v___x_3047_ = l_Lean_Syntax_node2(v___x_3023_, v___x_3037_, v___x_3046_, v___x_3024_);
v___x_3048_ = ((size_t)1ULL);
v___x_3049_ = lean_usize_add(v_i_3026_, v___x_3048_);
v___x_3050_ = lean_array_uset(v_bs_x27_3036_, v_i_3026_, v___x_3047_);
v_i_3026_ = v___x_3049_;
v_bs_3027_ = v___x_3050_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__2___boxed(lean_object* v___x_3054_, lean_object* v___x_3055_, lean_object* v_sz_3056_, lean_object* v_i_3057_, lean_object* v_bs_3058_){
_start:
{
size_t v_sz_boxed_3059_; size_t v_i_boxed_3060_; lean_object* v_res_3061_; 
v_sz_boxed_3059_ = lean_unbox_usize(v_sz_3056_);
lean_dec(v_sz_3056_);
v_i_boxed_3060_ = lean_unbox_usize(v_i_3057_);
lean_dec(v_i_3057_);
v_res_3061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__2(v___x_3054_, v___x_3055_, v_sz_boxed_3059_, v_i_boxed_3060_, v_bs_3058_);
return v_res_3061_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__0));
v___x_3064_ = l_String_toRawSubstring_x27(v___x_3063_);
return v___x_3064_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9(void){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__8));
v___x_3082_ = l_String_toRawSubstring_x27(v___x_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg(lean_object* v_indVal_3089_, lean_object* v___x_3090_, lean_object* v_as_3091_, lean_object* v_i_3092_, lean_object* v_j_3093_, lean_object* v_bs_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v_zero_3097_; uint8_t v_isZero_3098_; 
v_zero_3097_ = lean_unsigned_to_nat(0u);
v_isZero_3098_ = lean_nat_dec_eq(v_i_3092_, v_zero_3097_);
if (v_isZero_3098_ == 1)
{
lean_object* v___x_3099_; 
lean_dec_ref(v___y_3095_);
lean_dec(v_j_3093_);
lean_dec(v_i_3092_);
lean_dec(v___x_3090_);
lean_dec_ref(v_indVal_3089_);
v___x_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3099_, 0, v_bs_3094_);
return v___x_3099_;
}
else
{
lean_object* v___x_3100_; lean_object* v_toConstantVal_3101_; lean_object* v_snd_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3192_; 
v___x_3100_ = lean_array_fget(v_as_3091_, v_j_3093_);
v_toConstantVal_3101_ = lean_ctor_get(v_indVal_3089_, 0);
lean_inc_ref(v_toConstantVal_3101_);
v_snd_3102_ = lean_ctor_get(v___x_3100_, 1);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3192_ == 0)
{
lean_object* v_unused_3193_; 
v_unused_3193_ = lean_ctor_get(v___x_3100_, 0);
lean_dec(v_unused_3193_);
v___x_3104_ = v___x_3100_;
v_isShared_3105_ = v_isSharedCheck_3192_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_snd_3102_);
lean_dec(v___x_3100_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3192_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v_name_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3189_; 
v_name_3106_ = lean_ctor_get(v_toConstantVal_3101_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_toConstantVal_3101_);
if (v_isSharedCheck_3189_ == 0)
{
lean_object* v_unused_3190_; lean_object* v_unused_3191_; 
v_unused_3190_ = lean_ctor_get(v_toConstantVal_3101_, 2);
lean_dec(v_unused_3190_);
v_unused_3191_ = lean_ctor_get(v_toConstantVal_3101_, 1);
lean_dec(v_unused_3191_);
v___x_3108_ = v_toConstantVal_3101_;
v_isShared_3109_ = v_isSharedCheck_3189_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_name_3106_);
lean_dec(v_toConstantVal_3101_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3189_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v_one_3110_; lean_object* v_n_3111_; lean_object* v_a_3113_; uint8_t v___x_3117_; 
v_one_3110_ = lean_unsigned_to_nat(1u);
v_n_3111_ = lean_nat_sub(v_i_3092_, v_one_3110_);
lean_dec(v_i_3092_);
v___x_3117_ = l_Lean_Expr_isAppOf(v_snd_3102_, v_name_3106_);
lean_dec(v_name_3106_);
lean_dec(v_snd_3102_);
if (v___x_3117_ == 0)
{
lean_object* v_ref_3118_; lean_object* v_quotContext_3119_; lean_object* v_currMacroScope_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3139_; 
v_ref_3118_ = lean_ctor_get(v___y_3095_, 5);
v_quotContext_3119_ = lean_ctor_get(v___y_3095_, 10);
v_currMacroScope_3120_ = lean_ctor_get(v___y_3095_, 11);
v___x_3121_ = l_Lean_SourceInfo_fromRef(v_ref_3118_, v___x_3117_);
v___x_3122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_3123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_3124_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__1, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__1);
v___x_3125_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_3120_);
lean_inc(v_quotContext_3119_);
v___x_3126_ = l_Lean_addMacroScope(v_quotContext_3119_, v___x_3125_, v_currMacroScope_3120_);
v___x_3127_ = lean_box(0);
v___x_3128_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__5));
lean_inc(v___x_3121_);
v___x_3129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3121_);
lean_ctor_set(v___x_3129_, 1, v___x_3124_);
lean_ctor_set(v___x_3129_, 2, v___x_3126_);
lean_ctor_set(v___x_3129_, 3, v___x_3128_);
v___x_3130_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_3131_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__7));
v___x_3132_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9);
v___x_3133_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__10));
lean_inc(v_currMacroScope_3120_);
lean_inc(v_quotContext_3119_);
v___x_3134_ = l_Lean_addMacroScope(v_quotContext_3119_, v___x_3133_, v_currMacroScope_3120_);
lean_inc(v___x_3121_);
v___x_3135_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3121_);
lean_ctor_set(v___x_3135_, 1, v___x_3132_);
lean_ctor_set(v___x_3135_, 2, v___x_3134_);
lean_ctor_set(v___x_3135_, 3, v___x_3127_);
v___x_3136_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__12));
v___x_3137_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_3121_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set_tag(v___x_3108_, 1);
lean_ctor_set(v___x_3108_, 2, v___x_3137_);
lean_ctor_set(v___x_3108_, 1, v___x_3136_);
lean_ctor_set(v___x_3108_, 0, v___x_3121_);
v___x_3139_ = v___x_3108_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3155_, 1, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3155_, 2, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_3121_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set_tag(v___x_3104_, 2);
lean_ctor_set(v___x_3104_, 1, v___x_3140_);
lean_ctor_set(v___x_3104_, 0, v___x_3121_);
v___x_3142_ = v___x_3104_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_inc(v_j_3093_);
v___x_3143_ = l_Nat_reprFast(v_j_3093_);
v___x_3144_ = lean_box(2);
v___x_3145_ = l_Lean_Syntax_mkNumLit(v___x_3143_, v___x_3144_);
v___x_3146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_3121_);
v___x_3147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3121_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__13));
lean_inc(v___x_3121_);
v___x_3149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3121_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
lean_inc_ref(v___x_3139_);
lean_inc(v___x_3121_);
v___x_3150_ = l_Lean_Syntax_node7(v___x_3121_, v___x_3131_, v___x_3135_, v___x_3139_, v___x_3142_, v___x_3145_, v___x_3147_, v___x_3139_, v___x_3149_);
lean_inc(v___x_3121_);
v___x_3151_ = l_Lean_Syntax_node1(v___x_3121_, v___x_3130_, v___x_3150_);
lean_inc(v___x_3121_);
v___x_3152_ = l_Lean_Syntax_node2(v___x_3121_, v___x_3123_, v___x_3129_, v___x_3151_);
v___x_3153_ = l_Lean_Syntax_node1(v___x_3121_, v___x_3122_, v___x_3152_);
v_a_3113_ = v___x_3153_;
goto v___jp_3112_;
}
}
}
else
{
lean_object* v_ref_3156_; lean_object* v_quotContext_3157_; lean_object* v_currMacroScope_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3172_; 
v_ref_3156_ = lean_ctor_get(v___y_3095_, 5);
v_quotContext_3157_ = lean_ctor_get(v___y_3095_, 10);
v_currMacroScope_3158_ = lean_ctor_get(v___y_3095_, 11);
v___x_3159_ = l_Lean_SourceInfo_fromRef(v_ref_3156_, v_isZero_3098_);
v___x_3160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_3161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_3162_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_3163_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__7));
v___x_3164_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9);
v___x_3165_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__10));
lean_inc(v_currMacroScope_3158_);
lean_inc(v_quotContext_3157_);
v___x_3166_ = l_Lean_addMacroScope(v_quotContext_3157_, v___x_3165_, v_currMacroScope_3158_);
v___x_3167_ = lean_box(0);
lean_inc(v___x_3159_);
v___x_3168_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3159_);
lean_ctor_set(v___x_3168_, 1, v___x_3164_);
lean_ctor_set(v___x_3168_, 2, v___x_3166_);
lean_ctor_set(v___x_3168_, 3, v___x_3167_);
v___x_3169_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__12));
v___x_3170_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_3159_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set_tag(v___x_3108_, 1);
lean_ctor_set(v___x_3108_, 2, v___x_3170_);
lean_ctor_set(v___x_3108_, 1, v___x_3169_);
lean_ctor_set(v___x_3108_, 0, v___x_3159_);
v___x_3172_ = v___x_3108_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_3159_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set_tag(v___x_3104_, 2);
lean_ctor_set(v___x_3104_, 1, v___x_3173_);
lean_ctor_set(v___x_3104_, 0, v___x_3159_);
v___x_3175_ = v___x_3104_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_inc(v_j_3093_);
v___x_3176_ = l_Nat_reprFast(v_j_3093_);
v___x_3177_ = lean_box(2);
v___x_3178_ = l_Lean_Syntax_mkNumLit(v___x_3176_, v___x_3177_);
v___x_3179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_3159_);
v___x_3180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3159_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__13));
lean_inc(v___x_3159_);
v___x_3182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3159_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
lean_inc_ref(v___x_3172_);
lean_inc(v___x_3159_);
v___x_3183_ = l_Lean_Syntax_node7(v___x_3159_, v___x_3163_, v___x_3168_, v___x_3172_, v___x_3175_, v___x_3178_, v___x_3180_, v___x_3172_, v___x_3182_);
lean_inc(v___x_3159_);
v___x_3184_ = l_Lean_Syntax_node1(v___x_3159_, v___x_3162_, v___x_3183_);
lean_inc(v___x_3090_);
lean_inc(v___x_3159_);
v___x_3185_ = l_Lean_Syntax_node2(v___x_3159_, v___x_3161_, v___x_3090_, v___x_3184_);
v___x_3186_ = l_Lean_Syntax_node1(v___x_3159_, v___x_3160_, v___x_3185_);
v_a_3113_ = v___x_3186_;
goto v___jp_3112_;
}
}
}
v___jp_3112_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = lean_nat_add(v_j_3093_, v_one_3110_);
lean_dec(v_j_3093_);
v___x_3115_ = lean_array_push(v_bs_3094_, v_a_3113_);
v_i_3092_ = v_n_3111_;
v_j_3093_ = v___x_3114_;
v_bs_3094_ = v___x_3115_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___boxed(lean_object* v_indVal_3194_, lean_object* v___x_3195_, lean_object* v_as_3196_, lean_object* v_i_3197_, lean_object* v_j_3198_, lean_object* v_bs_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg(v_indVal_3194_, v___x_3195_, v_as_3196_, v_i_3197_, v_j_3198_, v_bs_3199_, v___y_3200_);
lean_dec_ref(v_as_3196_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(lean_object* v_a_3203_, lean_object* v_fst_3204_, lean_object* v_____r_3205_, lean_object* v_userNames_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___closed__1));
v___x_3215_ = l_Lean_Core_mkFreshUserName(v___x_3214_, v___y_3211_, v___y_3212_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3229_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3218_ = v___x_3215_;
v_isShared_3219_ = v_isSharedCheck_3229_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3215_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3229_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3227_; 
v___x_3220_ = lean_mk_syntax_ident(v_a_3216_);
v___x_3221_ = l_Lean_LocalDecl_type(v_a_3203_);
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3220_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = lean_array_push(v_fst_3204_, v___x_3222_);
v___x_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v_userNames_3206_);
v___x_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 0, v___x_3225_);
v___x_3227_ = v___x_3218_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v_userNames_3206_);
lean_dec(v_fst_3204_);
v_a_3230_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3215_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3215_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___boxed(lean_object* v_a_3238_, lean_object* v_fst_3239_, lean_object* v_____r_3240_, lean_object* v_userNames_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(v_a_3238_, v_fst_3239_, v_____r_3240_, v_userNames_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec_ref(v_a_3238_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg(lean_object* v_upperBound_3250_, lean_object* v_indVal_3251_, lean_object* v_xs_3252_, lean_object* v_a_3253_, lean_object* v_b_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v___y_3263_; uint8_t v___x_3285_; 
v___x_3285_ = lean_nat_dec_lt(v_a_3253_, v_upperBound_3250_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; 
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v___y_3257_);
lean_dec(v_a_3253_);
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_b_3254_);
return v___x_3286_;
}
else
{
lean_object* v_numParams_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_numParams_3287_ = lean_ctor_get(v_indVal_3251_, 1);
v___x_3288_ = l_Lean_instInhabitedExpr;
v___x_3289_ = lean_nat_add(v_numParams_3287_, v_a_3253_);
v___x_3290_ = lean_array_get_borrowed(v___x_3288_, v_xs_3252_, v___x_3289_);
lean_dec(v___x_3289_);
v___x_3291_ = l_Lean_Expr_fvarId_x21(v___x_3290_);
lean_inc_ref(v___y_3257_);
v___x_3292_ = l_Lean_FVarId_getDecl___redArg(v___x_3291_, v___y_3257_, v___y_3259_, v___y_3260_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; lean_object* v_fst_3294_; lean_object* v_snd_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_a_3293_);
lean_dec_ref(v___x_3292_);
v_fst_3294_ = lean_ctor_get(v_b_3254_, 0);
lean_inc(v_fst_3294_);
v_snd_3295_ = lean_ctor_get(v_b_3254_, 1);
lean_inc(v_snd_3295_);
lean_dec_ref(v_b_3254_);
v___x_3296_ = l_Lean_LocalDecl_userName(v_a_3293_);
v___x_3297_ = l_Lean_Name_hasMacroScopes(v___x_3296_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3298_ = lean_array_push(v_snd_3295_, v___x_3296_);
v___x_3299_ = lean_box(0);
lean_inc(v___y_3260_);
lean_inc_ref(v___y_3259_);
v___x_3300_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(v_a_3293_, v_fst_3294_, v___x_3299_, v___x_3298_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v_a_3293_);
v___y_3263_ = v___x_3300_;
goto v___jp_3262_;
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_dec(v___x_3296_);
v___x_3301_ = lean_box(0);
lean_inc(v___y_3260_);
lean_inc_ref(v___y_3259_);
v___x_3302_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(v_a_3293_, v_fst_3294_, v___x_3301_, v_snd_3295_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v_a_3293_);
v___y_3263_ = v___x_3302_;
goto v___jp_3262_;
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v___y_3257_);
lean_dec_ref(v_b_3254_);
lean_dec(v_a_3253_);
v_a_3303_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3292_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3292_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
v___jp_3262_:
{
if (lean_obj_tag(v___y_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3276_; 
v_a_3264_ = lean_ctor_get(v___y_3263_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___y_3263_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3266_ = v___y_3263_;
v_isShared_3267_ = v_isSharedCheck_3276_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___y_3263_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3276_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
if (lean_obj_tag(v_a_3264_) == 0)
{
lean_object* v_a_3268_; lean_object* v___x_3270_; 
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v___y_3257_);
lean_dec(v_a_3253_);
v_a_3268_ = lean_ctor_get(v_a_3264_, 0);
lean_inc(v_a_3268_);
lean_dec_ref(v_a_3264_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v_a_3268_);
v___x_3270_ = v___x_3266_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3268_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
lean_del_object(v___x_3266_);
v_a_3272_ = lean_ctor_get(v_a_3264_, 0);
lean_inc(v_a_3272_);
lean_dec_ref(v_a_3264_);
v___x_3273_ = lean_unsigned_to_nat(1u);
v___x_3274_ = lean_nat_add(v_a_3253_, v___x_3273_);
lean_dec(v_a_3253_);
v_a_3253_ = v___x_3274_;
v_b_3254_ = v_a_3272_;
goto _start;
}
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v___y_3257_);
lean_dec(v_a_3253_);
v_a_3277_ = lean_ctor_get(v___y_3263_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___y_3263_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___y_3263_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___y_3263_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___boxed(lean_object* v_upperBound_3311_, lean_object* v_indVal_3312_, lean_object* v_xs_3313_, lean_object* v_a_3314_, lean_object* v_b_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg(v_upperBound_3311_, v_indVal_3312_, v_xs_3313_, v_a_3314_, v_b_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3319_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec_ref(v_xs_3313_);
lean_dec_ref(v_indVal_3312_);
lean_dec(v_upperBound_3311_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__3(size_t v_sz_3324_, size_t v_i_3325_, lean_object* v_bs_3326_){
_start:
{
uint8_t v___x_3327_; 
v___x_3327_ = lean_usize_dec_lt(v_i_3325_, v_sz_3324_);
if (v___x_3327_ == 0)
{
return v_bs_3326_;
}
else
{
lean_object* v_v_3328_; lean_object* v___x_3329_; lean_object* v_bs_x27_3330_; size_t v___x_3331_; size_t v___x_3332_; lean_object* v___x_3333_; 
v_v_3328_ = lean_array_uget(v_bs_3326_, v_i_3325_);
v___x_3329_ = lean_unsigned_to_nat(0u);
v_bs_x27_3330_ = lean_array_uset(v_bs_3326_, v_i_3325_, v___x_3329_);
v___x_3331_ = ((size_t)1ULL);
v___x_3332_ = lean_usize_add(v_i_3325_, v___x_3331_);
v___x_3333_ = lean_array_uset(v_bs_x27_3330_, v_i_3325_, v_v_3328_);
v_i_3325_ = v___x_3332_;
v_bs_3326_ = v___x_3333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__3___boxed(lean_object* v_sz_3335_, lean_object* v_i_3336_, lean_object* v_bs_3337_){
_start:
{
size_t v_sz_boxed_3338_; size_t v_i_boxed_3339_; lean_object* v_res_3340_; 
v_sz_boxed_3338_ = lean_unbox_usize(v_sz_3335_);
lean_dec(v_sz_3335_);
v_i_boxed_3339_ = lean_unbox_usize(v_i_3336_);
lean_dec(v_i_3336_);
v_res_3340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__3(v_sz_boxed_3338_, v_i_boxed_3339_, v_bs_3337_);
return v_res_3340_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__0));
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
return v___x_3344_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__2));
v___x_3347_ = l_String_toRawSubstring_x27(v___x_3346_);
return v___x_3347_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__9));
v___x_3364_ = l_String_toRawSubstring_x27(v___x_3363_);
return v___x_3364_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19(void){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__18));
v___x_3385_ = l_String_toRawSubstring_x27(v___x_3384_);
return v___x_3385_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26(void){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__25));
v___x_3400_ = l_String_toRawSubstring_x27(v___x_3399_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0(lean_object* v_numFields_3412_, lean_object* v_indVal_3413_, lean_object* v_ctx_3414_, lean_object* v___x_3415_, lean_object* v___x_3416_, lean_object* v_head_3417_, lean_object* v_xs_3418_, lean_object* v_x_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v_stx_3428_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__1);
lean_inc_ref(v___y_3424_);
v___x_3434_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg(v_numFields_3412_, v_indVal_3413_, v_xs_3418_, v___x_3432_, v___x_3433_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v_fst_3436_; lean_object* v_snd_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3606_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref(v___x_3434_);
v_fst_3436_ = lean_ctor_get(v_a_3435_, 0);
v_snd_3437_ = lean_ctor_get(v_a_3435_, 1);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_a_3435_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3439_ = v_a_3435_;
v_isShared_3440_ = v_isSharedCheck_3606_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_snd_3437_);
lean_inc(v_fst_3436_);
lean_dec(v_a_3435_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3606_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v_auxFunNames_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; size_t v_sz_3444_; size_t v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v_a_3450_; lean_object* v_userNamesOpt_3452_; lean_object* v___y_3453_; lean_object* v___x_3566_; uint8_t v___x_3567_; 
v_auxFunNames_3441_ = lean_ctor_get(v_ctx_3414_, 2);
v___x_3442_ = lean_array_get_borrowed(v___x_3415_, v_auxFunNames_3441_, v___x_3432_);
lean_inc(v___x_3442_);
v___x_3443_ = lean_mk_syntax_ident(v___x_3442_);
v_sz_3444_ = lean_array_size(v_fst_3436_);
v___x_3445_ = ((size_t)0ULL);
lean_inc(v_fst_3436_);
v___x_3446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__0(v_sz_3444_, v___x_3445_, v_fst_3436_);
v___x_3447_ = lean_array_get_size(v_fst_3436_);
v___x_3448_ = lean_mk_empty_array_with_capacity(v___x_3447_);
lean_inc_ref(v___y_3424_);
v___x_3449_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg(v_indVal_3413_, v___x_3443_, v_fst_3436_, v___x_3447_, v___x_3432_, v___x_3448_, v___y_3424_);
lean_dec(v_fst_3436_);
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref(v___x_3449_);
v___x_3566_ = lean_array_get_size(v_snd_3437_);
v___x_3567_ = lean_nat_dec_eq(v___x_3447_, v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v_ref_3568_; lean_object* v_quotContext_3569_; lean_object* v_currMacroScope_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
lean_dec(v_snd_3437_);
v_ref_3568_ = lean_ctor_get(v___y_3424_, 5);
v_quotContext_3569_ = lean_ctor_get(v___y_3424_, 10);
v_currMacroScope_3570_ = lean_ctor_get(v___y_3424_, 11);
v___x_3571_ = l_Lean_SourceInfo_fromRef(v_ref_3568_, v___x_3567_);
v___x_3572_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19);
v___x_3573_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__20));
lean_inc(v_currMacroScope_3570_);
lean_inc(v_quotContext_3569_);
v___x_3574_ = l_Lean_addMacroScope(v_quotContext_3569_, v___x_3573_, v_currMacroScope_3570_);
v___x_3575_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__24));
v___x_3576_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3571_);
lean_ctor_set(v___x_3576_, 1, v___x_3572_);
lean_ctor_set(v___x_3576_, 2, v___x_3574_);
lean_ctor_set(v___x_3576_, 3, v___x_3575_);
v_userNamesOpt_3452_ = v___x_3576_;
v___y_3453_ = v___y_3424_;
goto v___jp_3451_;
}
else
{
lean_object* v_ref_3577_; lean_object* v_quotContext_3578_; lean_object* v_currMacroScope_3579_; uint8_t v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; size_t v_sz_3593_; lean_object* v___x_3594_; size_t v_sz_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v_ref_3577_ = lean_ctor_get(v___y_3424_, 5);
v_quotContext_3578_ = lean_ctor_get(v___y_3424_, 10);
v_currMacroScope_3579_ = lean_ctor_get(v___y_3424_, 11);
v___x_3580_ = 0;
v___x_3581_ = l_Lean_SourceInfo_fromRef(v_ref_3577_, v___x_3580_);
v___x_3582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_3583_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26);
v___x_3584_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__27));
lean_inc(v_currMacroScope_3579_);
lean_inc(v_quotContext_3578_);
v___x_3585_ = l_Lean_addMacroScope(v_quotContext_3578_, v___x_3584_, v_currMacroScope_3579_);
v___x_3586_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__30));
lean_inc(v___x_3581_);
v___x_3587_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3581_);
lean_ctor_set(v___x_3587_, 1, v___x_3583_);
lean_ctor_set(v___x_3587_, 2, v___x_3585_);
lean_ctor_set(v___x_3587_, 3, v___x_3586_);
v___x_3588_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_3589_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__15));
v___x_3590_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__16));
lean_inc(v___x_3581_);
v___x_3591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3581_);
lean_ctor_set(v___x_3591_, 1, v___x_3590_);
v___x_3592_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v_sz_3593_ = lean_array_size(v_snd_3437_);
v___x_3594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__4(v_sz_3593_, v___x_3445_, v_snd_3437_);
v_sz_3595_ = lean_array_size(v___x_3594_);
v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(v_sz_3595_, v___x_3445_, v___x_3594_);
v___x_3597_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6);
v___x_3598_ = l_Lean_mkSepArray(v___x_3596_, v___x_3597_);
lean_dec_ref(v___x_3596_);
v___x_3599_ = l_Array_append___redArg(v___x_3592_, v___x_3598_);
lean_dec_ref(v___x_3598_);
lean_inc(v___x_3581_);
v___x_3600_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3581_);
lean_ctor_set(v___x_3600_, 1, v___x_3588_);
lean_ctor_set(v___x_3600_, 2, v___x_3599_);
v___x_3601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_3581_);
v___x_3602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3581_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
lean_inc(v___x_3581_);
v___x_3603_ = l_Lean_Syntax_node3(v___x_3581_, v___x_3589_, v___x_3591_, v___x_3600_, v___x_3602_);
lean_inc(v___x_3581_);
v___x_3604_ = l_Lean_Syntax_node1(v___x_3581_, v___x_3588_, v___x_3603_);
v___x_3605_ = l_Lean_Syntax_node2(v___x_3581_, v___x_3582_, v___x_3587_, v___x_3604_);
v_userNamesOpt_3452_ = v___x_3605_;
v___y_3453_ = v___y_3424_;
goto v___jp_3451_;
}
v___jp_3451_:
{
uint8_t v___x_3454_; 
v___x_3454_ = lean_nat_dec_eq(v_numFields_3412_, v___x_3432_);
if (v___x_3454_ == 0)
{
lean_object* v_ref_3455_; lean_object* v_quotContext_3456_; lean_object* v_currMacroScope_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v_ref_3455_ = lean_ctor_get(v___y_3453_, 5);
lean_inc(v_ref_3455_);
v_quotContext_3456_ = lean_ctor_get(v___y_3453_, 10);
lean_inc(v_quotContext_3456_);
v_currMacroScope_3457_ = lean_ctor_get(v___y_3453_, 11);
lean_inc(v_currMacroScope_3457_);
lean_dec_ref(v___y_3453_);
v___x_3458_ = l_Lean_SourceInfo_fromRef(v_ref_3455_, v___x_3454_);
lean_dec(v_ref_3455_);
v___x_3459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_3460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39));
v___x_3461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41));
v___x_3462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_3463_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_3458_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set_tag(v___x_3439_, 2);
lean_ctor_set(v___x_3439_, 1, v___x_3463_);
lean_ctor_set(v___x_3439_, 0, v___x_3458_);
v___x_3465_ = v___x_3439_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; size_t v_sz_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; size_t v_sz_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_3467_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
v___x_3468_ = lean_box(0);
lean_inc(v_currMacroScope_3457_);
lean_inc(v_quotContext_3456_);
v___x_3469_ = l_Lean_addMacroScope(v_quotContext_3456_, v___x_3468_, v_currMacroScope_3457_);
v___x_3470_ = lean_box(0);
v___x_3471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__28));
lean_inc(v___x_3458_);
v___x_3472_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3458_);
lean_ctor_set(v___x_3472_, 1, v___x_3467_);
lean_ctor_set(v___x_3472_, 2, v___x_3469_);
lean_ctor_set(v___x_3472_, 3, v___x_3471_);
lean_inc(v___x_3458_);
v___x_3473_ = l_Lean_Syntax_node1(v___x_3458_, v___x_3466_, v___x_3472_);
lean_inc(v___x_3458_);
v___x_3474_ = l_Lean_Syntax_node2(v___x_3458_, v___x_3462_, v___x_3465_, v___x_3473_);
v___x_3475_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__3);
v___x_3476_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__5));
lean_inc(v_currMacroScope_3457_);
lean_inc(v_quotContext_3456_);
v___x_3477_ = l_Lean_addMacroScope(v_quotContext_3456_, v___x_3476_, v_currMacroScope_3457_);
v___x_3478_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__8));
lean_inc(v___x_3458_);
v___x_3479_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3458_);
lean_ctor_set(v___x_3479_, 1, v___x_3475_);
lean_ctor_set(v___x_3479_, 2, v___x_3477_);
lean_ctor_set(v___x_3479_, 3, v___x_3478_);
v___x_3480_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_3481_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10);
v___x_3482_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__11));
lean_inc(v_currMacroScope_3457_);
lean_inc(v_quotContext_3456_);
v___x_3483_ = l_Lean_addMacroScope(v_quotContext_3456_, v___x_3482_, v_currMacroScope_3457_);
v___x_3484_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__15));
lean_inc(v___x_3458_);
v___x_3485_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3458_);
lean_ctor_set(v___x_3485_, 1, v___x_3481_);
lean_ctor_set(v___x_3485_, 2, v___x_3483_);
lean_ctor_set(v___x_3485_, 3, v___x_3484_);
v___x_3486_ = lean_box(2);
lean_inc_ref(v___x_3416_);
v___x_3487_ = l_Lean_Syntax_mkStrLit(v___x_3416_, v___x_3486_);
lean_inc(v_numFields_3412_);
v___x_3488_ = l_Nat_reprFast(v_numFields_3412_);
v___x_3489_ = l_Lean_Syntax_mkNumLit(v___x_3488_, v___x_3486_);
lean_inc(v___x_3458_);
v___x_3490_ = l_Lean_Syntax_node4(v___x_3458_, v___x_3480_, v___x_3485_, v___x_3487_, v___x_3489_, v_userNamesOpt_3452_);
lean_inc(v___x_3458_);
v___x_3491_ = l_Lean_Syntax_node2(v___x_3458_, v___x_3459_, v___x_3479_, v___x_3490_);
v___x_3492_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_3458_);
v___x_3493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3458_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
lean_inc_ref(v___x_3493_);
lean_inc(v___x_3474_);
lean_inc(v___x_3458_);
v___x_3494_ = l_Lean_Syntax_node3(v___x_3458_, v___x_3461_, v___x_3474_, v___x_3491_, v___x_3493_);
v___x_3495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__42));
lean_inc(v___x_3458_);
v___x_3496_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3458_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
v___x_3497_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__10);
v___x_3498_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__11));
lean_inc(v_currMacroScope_3457_);
lean_inc(v_quotContext_3456_);
v___x_3499_ = l_Lean_addMacroScope(v_quotContext_3456_, v___x_3498_, v_currMacroScope_3457_);
v___x_3500_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__15));
lean_inc(v___x_3458_);
v___x_3501_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3458_);
lean_ctor_set(v___x_3501_, 1, v___x_3497_);
lean_ctor_set(v___x_3501_, 2, v___x_3499_);
lean_ctor_set(v___x_3501_, 3, v___x_3500_);
lean_inc(v___x_3458_);
v___x_3502_ = l_Lean_Syntax_node3(v___x_3458_, v___x_3460_, v___x_3494_, v___x_3496_, v___x_3501_);
v___x_3503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__16));
v___x_3504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17));
lean_inc(v___x_3458_);
v___x_3505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3458_);
lean_ctor_set(v___x_3505_, 1, v___x_3503_);
v___x_3506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19));
v___x_3507_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9);
v___x_3508_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__10));
v___x_3509_ = l_Lean_addMacroScope(v_quotContext_3456_, v___x_3508_, v_currMacroScope_3457_);
lean_inc(v___x_3458_);
v___x_3510_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3458_);
lean_ctor_set(v___x_3510_, 1, v___x_3507_);
lean_ctor_set(v___x_3510_, 2, v___x_3509_);
lean_ctor_set(v___x_3510_, 3, v___x_3470_);
lean_inc(v___x_3458_);
v___x_3511_ = l_Lean_Syntax_node1(v___x_3458_, v___x_3480_, v___x_3510_);
v___x_3512_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_3458_);
v___x_3513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3458_);
lean_ctor_set(v___x_3513_, 1, v___x_3480_);
lean_ctor_set(v___x_3513_, 2, v___x_3512_);
v___x_3514_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__7));
lean_inc(v___x_3458_);
v___x_3515_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3458_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
v___x_3516_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__0));
v___x_3517_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1));
lean_inc(v___x_3458_);
v___x_3518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3458_);
lean_ctor_set(v___x_3518_, 1, v___x_3516_);
v___x_3519_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3));
v___x_3520_ = l_Array_zip___redArg(v___x_3446_, v_a_3450_);
lean_dec(v_a_3450_);
v_sz_3521_ = lean_array_size(v___x_3520_);
lean_inc_ref(v___x_3513_);
lean_inc(v___x_3458_);
v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__2(v___x_3458_, v___x_3513_, v_sz_3521_, v___x_3445_, v___x_3520_);
v___x_3523_ = l_Array_append___redArg(v___x_3512_, v___x_3522_);
lean_dec_ref(v___x_3522_);
v___x_3524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1));
v___x_3525_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5));
v___x_3526_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__6));
lean_inc(v___x_3458_);
v___x_3527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3458_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = lean_mk_syntax_ident(v_head_3417_);
v_sz_3529_ = lean_array_size(v___x_3446_);
v___x_3530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__3(v_sz_3529_, v___x_3445_, v___x_3446_);
v___x_3531_ = l_Array_append___redArg(v___x_3512_, v___x_3530_);
lean_dec_ref(v___x_3530_);
lean_inc(v___x_3458_);
v___x_3532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3458_);
lean_ctor_set(v___x_3532_, 1, v___x_3480_);
lean_ctor_set(v___x_3532_, 2, v___x_3531_);
lean_inc(v___x_3458_);
v___x_3533_ = l_Lean_Syntax_node2(v___x_3458_, v___x_3459_, v___x_3528_, v___x_3532_);
lean_inc(v___x_3458_);
v___x_3534_ = l_Lean_Syntax_node1(v___x_3458_, v___x_3480_, v___x_3533_);
lean_inc(v___x_3458_);
v___x_3535_ = l_Lean_Syntax_node2(v___x_3458_, v___x_3525_, v___x_3527_, v___x_3534_);
lean_inc_ref(v___x_3513_);
lean_inc(v___x_3458_);
v___x_3536_ = l_Lean_Syntax_node2(v___x_3458_, v___x_3524_, v___x_3535_, v___x_3513_);
v___x_3537_ = lean_array_push(v___x_3523_, v___x_3536_);
lean_inc(v___x_3458_);
v___x_3538_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3458_);
lean_ctor_set(v___x_3538_, 1, v___x_3480_);
lean_ctor_set(v___x_3538_, 2, v___x_3537_);
lean_inc(v___x_3458_);
v___x_3539_ = l_Lean_Syntax_node1(v___x_3458_, v___x_3519_, v___x_3538_);
lean_inc(v___x_3458_);
v___x_3540_ = l_Lean_Syntax_node2(v___x_3458_, v___x_3517_, v___x_3518_, v___x_3539_);
lean_inc(v___x_3458_);
v___x_3541_ = l_Lean_Syntax_node4(v___x_3458_, v___x_3506_, v___x_3511_, v___x_3513_, v___x_3515_, v___x_3540_);
lean_inc(v___x_3458_);
v___x_3542_ = l_Lean_Syntax_node2(v___x_3458_, v___x_3504_, v___x_3505_, v___x_3541_);
lean_inc(v___x_3458_);
v___x_3543_ = l_Lean_Syntax_node3(v___x_3458_, v___x_3461_, v___x_3474_, v___x_3542_, v___x_3493_);
lean_inc(v___x_3458_);
v___x_3544_ = l_Lean_Syntax_node1(v___x_3458_, v___x_3480_, v___x_3543_);
v___x_3545_ = l_Lean_Syntax_node2(v___x_3458_, v___x_3459_, v___x_3502_, v___x_3544_);
v_stx_3428_ = v___x_3545_;
goto v___jp_3427_;
}
}
else
{
lean_object* v_ref_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3553_; 
lean_dec(v_userNamesOpt_3452_);
lean_dec(v_a_3450_);
v_ref_3547_ = lean_ctor_get(v___y_3453_, 5);
lean_inc(v_ref_3547_);
lean_dec_ref(v___y_3453_);
v___x_3548_ = 0;
v___x_3549_ = l_Lean_SourceInfo_fromRef(v_ref_3547_, v___x_3548_);
lean_dec(v_ref_3547_);
v___x_3550_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__17));
v___x_3551_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__6));
lean_inc(v___x_3549_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set_tag(v___x_3439_, 2);
lean_ctor_set(v___x_3439_, 1, v___x_3551_);
lean_ctor_set(v___x_3439_, 0, v___x_3549_);
v___x_3553_ = v___x_3439_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; size_t v_sz_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3554_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_3555_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_3556_ = lean_mk_syntax_ident(v_head_3417_);
v___x_3557_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v_sz_3558_ = lean_array_size(v___x_3446_);
v___x_3559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__3(v_sz_3558_, v___x_3445_, v___x_3446_);
v___x_3560_ = l_Array_append___redArg(v___x_3557_, v___x_3559_);
lean_dec_ref(v___x_3559_);
lean_inc(v___x_3549_);
v___x_3561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3549_);
lean_ctor_set(v___x_3561_, 1, v___x_3554_);
lean_ctor_set(v___x_3561_, 2, v___x_3560_);
lean_inc(v___x_3549_);
v___x_3562_ = l_Lean_Syntax_node2(v___x_3549_, v___x_3555_, v___x_3556_, v___x_3561_);
lean_inc(v___x_3549_);
v___x_3563_ = l_Lean_Syntax_node1(v___x_3549_, v___x_3554_, v___x_3562_);
v___x_3564_ = l_Lean_Syntax_node2(v___x_3549_, v___x_3550_, v___x_3553_, v___x_3563_);
v_stx_3428_ = v___x_3564_;
goto v___jp_3427_;
}
}
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec_ref(v___y_3424_);
lean_dec(v_head_3417_);
lean_dec_ref(v___x_3416_);
lean_dec(v___x_3415_);
lean_dec_ref(v_indVal_3413_);
lean_dec(v_numFields_3412_);
v_a_3607_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3434_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3434_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
v___jp_3427_:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3416_);
lean_ctor_set(v___x_3429_, 1, v_stx_3428_);
v___x_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
lean_ctor_set(v___x_3430_, 1, v_numFields_3412_);
v___x_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
return v___x_3431_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___boxed(lean_object* v_numFields_3615_, lean_object* v_indVal_3616_, lean_object* v_ctx_3617_, lean_object* v___x_3618_, lean_object* v___x_3619_, lean_object* v_head_3620_, lean_object* v_xs_3621_, lean_object* v_x_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0(v_numFields_3615_, v_indVal_3616_, v_ctx_3617_, v___x_3618_, v___x_3619_, v_head_3620_, v_xs_3621_, v_x_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3626_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec_ref(v_x_3622_);
lean_dec_ref(v_xs_3621_);
lean_dec_ref(v_ctx_3617_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___redArg(lean_object* v_ctx_3631_, lean_object* v_indVal_3632_, lean_object* v_as_x27_3633_, lean_object* v_b_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
if (lean_obj_tag(v_as_x27_3633_) == 0)
{
lean_object* v___x_3642_; 
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v_indVal_3632_);
lean_dec_ref(v_ctx_3631_);
v___x_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3642_, 0, v_b_3634_);
return v___x_3642_;
}
else
{
lean_object* v_head_3643_; lean_object* v_tail_3644_; lean_object* v___x_3645_; 
v_head_3643_ = lean_ctor_get(v_as_x27_3633_, 0);
lean_inc(v_head_3643_);
v_tail_3644_ = lean_ctor_get(v_as_x27_3633_, 1);
lean_inc(v_tail_3644_);
lean_dec_ref(v_as_x27_3633_);
lean_inc(v___y_3640_);
lean_inc_ref(v___y_3639_);
lean_inc(v___y_3638_);
lean_inc_ref(v___y_3637_);
lean_inc(v___y_3636_);
lean_inc_ref(v___y_3635_);
lean_inc(v_head_3643_);
v___x_3645_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0(v_head_3643_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v_toConstantVal_3647_; lean_object* v_numFields_3648_; lean_object* v_type_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___f_3653_; uint8_t v___x_3654_; lean_object* v___x_3655_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref(v___x_3645_);
v_toConstantVal_3647_ = lean_ctor_get(v_a_3646_, 0);
lean_inc_ref(v_toConstantVal_3647_);
v_numFields_3648_ = lean_ctor_get(v_a_3646_, 4);
lean_inc(v_numFields_3648_);
lean_dec(v_a_3646_);
v_type_3649_ = lean_ctor_get(v_toConstantVal_3647_, 2);
lean_inc_ref(v_type_3649_);
lean_dec_ref(v_toConstantVal_3647_);
v___x_3650_ = lean_box(0);
lean_inc(v_head_3643_);
v___x_3651_ = lean_erase_macro_scopes(v_head_3643_);
v___x_3652_ = l_Lean_Name_getString_x21(v___x_3651_);
lean_dec(v___x_3651_);
lean_inc_ref(v_ctx_3631_);
lean_inc_ref(v_indVal_3632_);
v___f_3653_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___boxed), 15, 6);
lean_closure_set(v___f_3653_, 0, v_numFields_3648_);
lean_closure_set(v___f_3653_, 1, v_indVal_3632_);
lean_closure_set(v___f_3653_, 2, v_ctx_3631_);
lean_closure_set(v___f_3653_, 3, v___x_3650_);
lean_closure_set(v___f_3653_, 4, v___x_3652_);
lean_closure_set(v___f_3653_, 5, v_head_3643_);
v___x_3654_ = 0;
lean_inc(v___y_3640_);
lean_inc_ref(v___y_3639_);
lean_inc(v___y_3638_);
lean_inc_ref(v___y_3637_);
lean_inc(v___y_3636_);
lean_inc_ref(v___y_3635_);
v___x_3655_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(v_type_3649_, v___f_3653_, v___x_3654_, v___x_3654_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3657_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref(v___x_3655_);
v___x_3657_ = lean_array_push(v_b_3634_, v_a_3656_);
v_as_x27_3633_ = v_tail_3644_;
v_b_3634_ = v___x_3657_;
goto _start;
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec(v_tail_3644_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v_b_3634_);
lean_dec_ref(v_indVal_3632_);
lean_dec_ref(v_ctx_3631_);
v_a_3659_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3655_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3655_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_dec(v_tail_3644_);
lean_dec(v_head_3643_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v_b_3634_);
lean_dec_ref(v_indVal_3632_);
lean_dec_ref(v_ctx_3631_);
v_a_3667_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3645_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3645_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___redArg___boxed(lean_object* v_ctx_3675_, lean_object* v_indVal_3676_, lean_object* v_as_x27_3677_, lean_object* v_b_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___redArg(v_ctx_3675_, v_indVal_3676_, v_as_x27_3677_, v_b_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg(lean_object* v_indVal_3687_, lean_object* v_ctx_3688_, lean_object* v_as_3689_, lean_object* v_as_x27_3690_, lean_object* v_b_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
if (lean_obj_tag(v_as_x27_3690_) == 0)
{
lean_object* v___x_3699_; 
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_ctx_3688_);
lean_dec_ref(v_indVal_3687_);
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v_b_3691_);
return v___x_3699_;
}
else
{
lean_object* v_head_3700_; lean_object* v_tail_3701_; lean_object* v___x_3702_; 
v_head_3700_ = lean_ctor_get(v_as_x27_3690_, 0);
lean_inc(v_head_3700_);
v_tail_3701_ = lean_ctor_get(v_as_x27_3690_, 1);
lean_inc(v_tail_3701_);
lean_dec_ref(v_as_x27_3690_);
lean_inc(v___y_3697_);
lean_inc_ref(v___y_3696_);
lean_inc(v___y_3695_);
lean_inc_ref(v___y_3694_);
lean_inc(v___y_3693_);
lean_inc_ref(v___y_3692_);
lean_inc(v_head_3700_);
v___x_3702_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0(v_head_3700_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v_toConstantVal_3704_; lean_object* v_numFields_3705_; lean_object* v_type_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___f_3710_; uint8_t v___x_3711_; lean_object* v___x_3712_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_a_3703_);
lean_dec_ref(v___x_3702_);
v_toConstantVal_3704_ = lean_ctor_get(v_a_3703_, 0);
lean_inc_ref(v_toConstantVal_3704_);
v_numFields_3705_ = lean_ctor_get(v_a_3703_, 4);
lean_inc(v_numFields_3705_);
lean_dec(v_a_3703_);
v_type_3706_ = lean_ctor_get(v_toConstantVal_3704_, 2);
lean_inc_ref(v_type_3706_);
lean_dec_ref(v_toConstantVal_3704_);
v___x_3707_ = lean_box(0);
lean_inc(v_head_3700_);
v___x_3708_ = lean_erase_macro_scopes(v_head_3700_);
v___x_3709_ = l_Lean_Name_getString_x21(v___x_3708_);
lean_dec(v___x_3708_);
lean_inc_ref(v_ctx_3688_);
lean_inc_ref(v_indVal_3687_);
v___f_3710_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___boxed), 15, 6);
lean_closure_set(v___f_3710_, 0, v_numFields_3705_);
lean_closure_set(v___f_3710_, 1, v_indVal_3687_);
lean_closure_set(v___f_3710_, 2, v_ctx_3688_);
lean_closure_set(v___f_3710_, 3, v___x_3707_);
lean_closure_set(v___f_3710_, 4, v___x_3709_);
lean_closure_set(v___f_3710_, 5, v_head_3700_);
v___x_3711_ = 0;
lean_inc(v___y_3697_);
lean_inc_ref(v___y_3696_);
lean_inc(v___y_3695_);
lean_inc_ref(v___y_3694_);
lean_inc(v___y_3693_);
lean_inc_ref(v___y_3692_);
v___x_3712_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(v_type_3706_, v___f_3710_, v___x_3711_, v___x_3711_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref(v___x_3712_);
v___x_3714_ = lean_array_push(v_b_3691_, v_a_3713_);
v___x_3715_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___redArg(v_ctx_3688_, v_indVal_3687_, v_tail_3701_, v___x_3714_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
return v___x_3715_;
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec(v_tail_3701_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_b_3691_);
lean_dec_ref(v_ctx_3688_);
lean_dec_ref(v_indVal_3687_);
v_a_3716_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3712_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3712_);
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
lean_dec(v_tail_3701_);
lean_dec(v_head_3700_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_b_3691_);
lean_dec_ref(v_ctx_3688_);
lean_dec_ref(v_indVal_3687_);
v_a_3724_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3702_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3702_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___boxed(lean_object* v_indVal_3732_, lean_object* v_ctx_3733_, lean_object* v_as_3734_, lean_object* v_as_x27_3735_, lean_object* v_b_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg(v_indVal_3732_, v_ctx_3733_, v_as_3734_, v_as_x27_3735_, v_b_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
lean_dec(v_as_3734_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__7(size_t v_sz_3745_, size_t v_i_3746_, lean_object* v_bs_3747_){
_start:
{
uint8_t v___x_3748_; 
v___x_3748_ = lean_usize_dec_lt(v_i_3746_, v_sz_3745_);
if (v___x_3748_ == 0)
{
return v_bs_3747_;
}
else
{
lean_object* v_v_3749_; lean_object* v_fst_3750_; lean_object* v___x_3751_; lean_object* v_bs_x27_3752_; size_t v___x_3753_; size_t v___x_3754_; lean_object* v___x_3755_; 
v_v_3749_ = lean_array_uget_borrowed(v_bs_3747_, v_i_3746_);
v_fst_3750_ = lean_ctor_get(v_v_3749_, 0);
lean_inc(v_fst_3750_);
v___x_3751_ = lean_unsigned_to_nat(0u);
v_bs_x27_3752_ = lean_array_uset(v_bs_3747_, v_i_3746_, v___x_3751_);
v___x_3753_ = ((size_t)1ULL);
v___x_3754_ = lean_usize_add(v_i_3746_, v___x_3753_);
v___x_3755_ = lean_array_uset(v_bs_x27_3752_, v_i_3746_, v_fst_3750_);
v_i_3746_ = v___x_3754_;
v_bs_3747_ = v___x_3755_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__7___boxed(lean_object* v_sz_3757_, lean_object* v_i_3758_, lean_object* v_bs_3759_){
_start:
{
size_t v_sz_boxed_3760_; size_t v_i_boxed_3761_; lean_object* v_res_3762_; 
v_sz_boxed_3760_ = lean_unbox_usize(v_sz_3757_);
lean_dec(v_sz_3757_);
v_i_boxed_3761_ = lean_unbox_usize(v_i_3758_);
lean_dec(v_i_3758_);
v_res_3762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__7(v_sz_boxed_3760_, v_i_boxed_3761_, v_bs_3759_);
return v_res_3762_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___lam__0(lean_object* v_x_3763_, lean_object* v_x_3764_){
_start:
{
lean_object* v_snd_3765_; lean_object* v_snd_3766_; uint8_t v___x_3767_; 
v_snd_3765_ = lean_ctor_get(v_x_3763_, 1);
v_snd_3766_ = lean_ctor_get(v_x_3764_, 1);
v___x_3767_ = lean_nat_dec_lt(v_snd_3765_, v_snd_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___lam__0___boxed(lean_object* v_x_3768_, lean_object* v_x_3769_){
_start:
{
uint8_t v_res_3770_; lean_object* v_r_3771_; 
v_res_3770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___lam__0(v_x_3768_, v_x_3769_);
lean_dec_ref(v_x_3769_);
lean_dec_ref(v_x_3768_);
v_r_3771_ = lean_box(v_res_3770_);
return v_r_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg(lean_object* v_as_3773_, lean_object* v_lo_3774_, lean_object* v_hi_3775_){
_start:
{
uint8_t v___x_3776_; 
v___x_3776_ = lean_nat_dec_lt(v_lo_3774_, v_hi_3775_);
if (v___x_3776_ == 0)
{
lean_dec(v_lo_3774_);
return v_as_3773_;
}
else
{
lean_object* v___f_3777_; lean_object* v___x_3778_; lean_object* v_fst_3779_; lean_object* v_snd_3780_; uint8_t v___x_3781_; 
v___f_3777_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___closed__0));
lean_inc(v_lo_3774_);
v___x_3778_ = l_Array_qpartition___redArg(v_as_3773_, v___f_3777_, v_lo_3774_, v_hi_3775_);
v_fst_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_fst_3779_);
v_snd_3780_ = lean_ctor_get(v___x_3778_, 1);
lean_inc(v_snd_3780_);
lean_dec_ref(v___x_3778_);
v___x_3781_ = lean_nat_dec_le(v_hi_3775_, v_fst_3779_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3782_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg(v_snd_3780_, v_lo_3774_, v_fst_3779_);
v___x_3783_ = lean_unsigned_to_nat(1u);
v___x_3784_ = lean_nat_add(v_fst_3779_, v___x_3783_);
lean_dec(v_fst_3779_);
v_as_3773_ = v___x_3782_;
v_lo_3774_ = v___x_3784_;
goto _start;
}
else
{
lean_dec(v_fst_3779_);
lean_dec(v_lo_3774_);
return v_snd_3780_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___boxed(lean_object* v_as_3786_, lean_object* v_lo_3787_, lean_object* v_hi_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg(v_as_3786_, v_lo_3787_, v_hi_3788_);
lean_dec(v_hi_3788_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts(lean_object* v_ctx_3792_, lean_object* v_indVal_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_){
_start:
{
lean_object* v_ctors_3801_; lean_object* v___x_3802_; lean_object* v_alts_3803_; lean_object* v___x_3804_; 
v_ctors_3801_ = lean_ctor_get(v_indVal_3793_, 4);
lean_inc(v_ctors_3801_);
v___x_3802_ = lean_unsigned_to_nat(0u);
v_alts_3803_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts___closed__0));
lean_inc(v_ctors_3801_);
v___x_3804_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg(v_indVal_3793_, v_ctx_3792_, v_ctors_3801_, v_ctors_3801_, v_alts_3803_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
lean_dec(v_ctors_3801_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3829_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3829_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3829_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___y_3810_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v___x_3821_ = lean_array_get_size(v_a_3805_);
v___x_3822_ = lean_nat_dec_eq(v___x_3821_, v___x_3802_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___y_3826_; uint8_t v___x_3828_; 
v___x_3823_ = lean_unsigned_to_nat(1u);
v___x_3824_ = lean_nat_sub(v___x_3821_, v___x_3823_);
v___x_3828_ = lean_nat_dec_le(v___x_3802_, v___x_3824_);
if (v___x_3828_ == 0)
{
lean_inc(v___x_3824_);
v___y_3826_ = v___x_3824_;
goto v___jp_3825_;
}
else
{
v___y_3826_ = v___x_3802_;
goto v___jp_3825_;
}
v___jp_3825_:
{
uint8_t v___x_3827_; 
v___x_3827_ = lean_nat_dec_le(v___y_3826_, v___x_3824_);
if (v___x_3827_ == 0)
{
lean_dec(v___x_3824_);
lean_inc(v___y_3826_);
v___y_3818_ = v___y_3826_;
v___y_3819_ = v___y_3826_;
goto v___jp_3817_;
}
else
{
v___y_3818_ = v___y_3826_;
v___y_3819_ = v___x_3824_;
goto v___jp_3817_;
}
}
}
else
{
v___y_3810_ = v_a_3805_;
goto v___jp_3809_;
}
v___jp_3809_:
{
size_t v_sz_3811_; size_t v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3815_; 
v_sz_3811_ = lean_array_size(v___y_3810_);
v___x_3812_ = ((size_t)0ULL);
v___x_3813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__7(v_sz_3811_, v___x_3812_, v___y_3810_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3813_);
v___x_3815_ = v___x_3807_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
v___jp_3817_:
{
lean_object* v___x_3820_; 
v___x_3820_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg(v_a_3805_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
v___y_3810_ = v___x_3820_;
goto v___jp_3809_;
}
}
}
else
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
v_a_3830_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3804_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3804_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts___boxed(lean_object* v_ctx_3838_, lean_object* v_indVal_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts(v_ctx_3838_, v_indVal_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1(lean_object* v_indVal_3848_, lean_object* v___x_3849_, lean_object* v_as_3850_, lean_object* v_i_3851_, lean_object* v_j_3852_, lean_object* v_inv_3853_, lean_object* v_bs_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg(v_indVal_3848_, v___x_3849_, v_as_3850_, v_i_3851_, v_j_3852_, v_bs_3854_, v___y_3859_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___boxed(lean_object* v_indVal_3863_, lean_object* v___x_3864_, lean_object* v_as_3865_, lean_object* v_i_3866_, lean_object* v_j_3867_, lean_object* v_inv_3868_, lean_object* v_bs_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1(v_indVal_3863_, v___x_3864_, v_as_3865_, v_i_3866_, v_j_3867_, v_inv_3868_, v_bs_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec_ref(v_as_3865_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5(lean_object* v_upperBound_3878_, lean_object* v_indVal_3879_, lean_object* v_xs_3880_, lean_object* v_inst_3881_, lean_object* v_R_3882_, lean_object* v_a_3883_, lean_object* v_b_3884_, lean_object* v_c_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg(v_upperBound_3878_, v_indVal_3879_, v_xs_3880_, v_a_3883_, v_b_3884_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___boxed(lean_object* v_upperBound_3894_, lean_object* v_indVal_3895_, lean_object* v_xs_3896_, lean_object* v_inst_3897_, lean_object* v_R_3898_, lean_object* v_a_3899_, lean_object* v_b_3900_, lean_object* v_c_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5(v_upperBound_3894_, v_indVal_3895_, v_xs_3896_, v_inst_3897_, v_R_3898_, v_a_3899_, v_b_3900_, v_c_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
lean_dec(v___y_3905_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec_ref(v_xs_3896_);
lean_dec_ref(v_indVal_3895_);
lean_dec(v_upperBound_3894_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6(lean_object* v_indVal_3910_, lean_object* v_ctx_3911_, lean_object* v_as_3912_, lean_object* v_as_x27_3913_, lean_object* v_b_3914_, lean_object* v_a_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg(v_indVal_3910_, v_ctx_3911_, v_as_3912_, v_as_x27_3913_, v_b_3914_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___boxed(lean_object* v_indVal_3924_, lean_object* v_ctx_3925_, lean_object* v_as_3926_, lean_object* v_as_x27_3927_, lean_object* v_b_3928_, lean_object* v_a_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6(v_indVal_3924_, v_ctx_3925_, v_as_3926_, v_as_x27_3927_, v_b_3928_, v_a_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
lean_dec(v_as_3926_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8(lean_object* v_n_3938_, lean_object* v_as_3939_, lean_object* v_lo_3940_, lean_object* v_hi_3941_, lean_object* v_w_3942_, lean_object* v_hlo_3943_, lean_object* v_hhi_3944_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg(v_as_3939_, v_lo_3940_, v_hi_3941_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___boxed(lean_object* v_n_3946_, lean_object* v_as_3947_, lean_object* v_lo_3948_, lean_object* v_hi_3949_, lean_object* v_w_3950_, lean_object* v_hlo_3951_, lean_object* v_hhi_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8(v_n_3946_, v_as_3947_, v_lo_3948_, v_hi_3949_, v_w_3950_, v_hlo_3951_, v_hhi_3952_);
lean_dec(v_hi_3949_);
lean_dec(v_n_3946_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6(lean_object* v_ctx_3954_, lean_object* v_indVal_3955_, lean_object* v_as_3956_, lean_object* v_as_x27_3957_, lean_object* v_b_3958_, lean_object* v_a_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v___x_3967_; 
v___x_3967_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___redArg(v_ctx_3954_, v_indVal_3955_, v_as_x27_3957_, v_b_3958_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___boxed(lean_object* v_ctx_3968_, lean_object* v_indVal_3969_, lean_object* v_as_3970_, lean_object* v_as_x27_3971_, lean_object* v_b_3972_, lean_object* v_a_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6(v_ctx_3968_, v_indVal_3969_, v_as_3970_, v_as_x27_3971_, v_b_3972_, v_a_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v_as_3970_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__1(lean_object* v___x_3982_, lean_object* v___x_3983_, lean_object* v___x_3984_, size_t v_sz_3985_, size_t v_i_3986_, lean_object* v_bs_3987_){
_start:
{
uint8_t v___x_3988_; 
v___x_3988_ = lean_usize_dec_lt(v_i_3986_, v_sz_3985_);
if (v___x_3988_ == 0)
{
lean_dec(v___x_3984_);
lean_dec(v___x_3983_);
lean_dec(v___x_3982_);
return v_bs_3987_;
}
else
{
lean_object* v_v_3989_; lean_object* v_fst_3990_; lean_object* v_snd_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v_bs_x27_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; size_t v___x_3999_; size_t v___x_4000_; lean_object* v___x_4001_; 
v_v_3989_ = lean_array_uget_borrowed(v_bs_3987_, v_i_3986_);
v_fst_3990_ = lean_ctor_get(v_v_3989_, 0);
lean_inc(v_fst_3990_);
v_snd_3991_ = lean_ctor_get(v_v_3989_, 1);
lean_inc(v_snd_3991_);
v___x_3992_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_3993_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4));
v___x_3994_ = lean_unsigned_to_nat(0u);
v_bs_x27_3995_ = lean_array_uset(v_bs_3987_, v_i_3986_, v___x_3994_);
lean_inc(v___x_3982_);
v___x_3996_ = l_Lean_Syntax_node1(v___x_3982_, v___x_3992_, v_fst_3990_);
lean_inc(v___x_3982_);
v___x_3997_ = l_Lean_Syntax_node1(v___x_3982_, v___x_3992_, v___x_3996_);
lean_inc(v___x_3984_);
lean_inc(v___x_3983_);
lean_inc(v___x_3982_);
v___x_3998_ = l_Lean_Syntax_node4(v___x_3982_, v___x_3993_, v___x_3983_, v___x_3997_, v___x_3984_, v_snd_3991_);
v___x_3999_ = ((size_t)1ULL);
v___x_4000_ = lean_usize_add(v_i_3986_, v___x_3999_);
v___x_4001_ = lean_array_uset(v_bs_x27_3995_, v_i_3986_, v___x_3998_);
v_i_3986_ = v___x_4000_;
v_bs_3987_ = v___x_4001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__1___boxed(lean_object* v___x_4003_, lean_object* v___x_4004_, lean_object* v___x_4005_, lean_object* v_sz_4006_, lean_object* v_i_4007_, lean_object* v_bs_4008_){
_start:
{
size_t v_sz_boxed_4009_; size_t v_i_boxed_4010_; lean_object* v_res_4011_; 
v_sz_boxed_4009_ = lean_unbox_usize(v_sz_4006_);
lean_dec(v_sz_4006_);
v_i_boxed_4010_ = lean_unbox_usize(v_i_4007_);
lean_dec(v_i_4007_);
v_res_4011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__1(v___x_4003_, v___x_4004_, v___x_4005_, v_sz_boxed_4009_, v_i_boxed_4010_, v_bs_4008_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__0(size_t v_sz_4012_, size_t v_i_4013_, lean_object* v_bs_4014_){
_start:
{
uint8_t v___x_4015_; 
v___x_4015_ = lean_usize_dec_lt(v_i_4013_, v_sz_4012_);
if (v___x_4015_ == 0)
{
return v_bs_4014_;
}
else
{
lean_object* v_v_4016_; lean_object* v___x_4017_; lean_object* v_bs_x27_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; size_t v___x_4021_; size_t v___x_4022_; lean_object* v___x_4023_; 
v_v_4016_ = lean_array_uget(v_bs_4014_, v_i_4013_);
v___x_4017_ = lean_unsigned_to_nat(0u);
v_bs_x27_4018_ = lean_array_uset(v_bs_4014_, v_i_4013_, v___x_4017_);
v___x_4019_ = lean_box(2);
v___x_4020_ = l_Lean_Syntax_mkStrLit(v_v_4016_, v___x_4019_);
v___x_4021_ = ((size_t)1ULL);
v___x_4022_ = lean_usize_add(v_i_4013_, v___x_4021_);
v___x_4023_ = lean_array_uset(v_bs_x27_4018_, v_i_4013_, v___x_4020_);
v_i_4013_ = v___x_4022_;
v_bs_4014_ = v___x_4023_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__0___boxed(lean_object* v_sz_4025_, lean_object* v_i_4026_, lean_object* v_bs_4027_){
_start:
{
size_t v_sz_boxed_4028_; size_t v_i_boxed_4029_; lean_object* v_res_4030_; 
v_sz_boxed_4028_ = lean_unbox_usize(v_sz_4025_);
lean_dec(v_sz_4025_);
v_i_boxed_4029_ = lean_unbox_usize(v_i_4026_);
lean_dec(v_i_4026_);
v_res_4030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__0(v_sz_boxed_4028_, v_i_boxed_4029_, v_bs_4027_);
return v_res_4030_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__3(void){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__2));
v___x_4039_ = l_String_toRawSubstring_x27(v___x_4038_);
return v___x_4039_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__10(void){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4055_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__9));
v___x_4056_ = l_String_toRawSubstring_x27(v___x_4055_);
return v___x_4056_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__13(void){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__12));
v___x_4061_ = l_String_toRawSubstring_x27(v___x_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct(lean_object* v_ctx_4079_, lean_object* v_indName_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v___x_4088_; 
lean_inc_ref(v_a_4081_);
v___x_4088_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0(v_indName_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4090_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref(v___x_4088_);
lean_inc_ref(v_a_4085_);
v___x_4090_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts(v_ctx_4079_, v_a_4089_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4204_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4093_ = v___x_4090_;
v_isShared_4094_ = v_isSharedCheck_4204_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4090_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4204_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4095_; lean_object* v_fst_4096_; lean_object* v_snd_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4203_; 
v___x_4095_ = l_Array_unzip___redArg(v_a_4091_);
lean_dec(v_a_4091_);
v_fst_4096_ = lean_ctor_get(v___x_4095_, 0);
v_snd_4097_ = lean_ctor_get(v___x_4095_, 1);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4099_ = v___x_4095_;
v_isShared_4100_ = v_isSharedCheck_4203_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_snd_4097_);
lean_inc(v_fst_4096_);
lean_dec(v___x_4095_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4203_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v_ref_4101_; lean_object* v_quotContext_4102_; lean_object* v_currMacroScope_4103_; uint8_t v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4109_; 
v_ref_4101_ = lean_ctor_get(v_a_4085_, 5);
lean_inc(v_ref_4101_);
v_quotContext_4102_ = lean_ctor_get(v_a_4085_, 10);
lean_inc(v_quotContext_4102_);
v_currMacroScope_4103_ = lean_ctor_get(v_a_4085_, 11);
lean_inc(v_currMacroScope_4103_);
lean_dec_ref(v_a_4085_);
v___x_4104_ = 0;
v___x_4105_ = l_Lean_SourceInfo_fromRef(v_ref_4101_, v___x_4104_);
lean_dec(v_ref_4101_);
v___x_4106_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__0));
v___x_4107_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1));
lean_inc(v___x_4105_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set_tag(v___x_4099_, 2);
lean_ctor_set(v___x_4099_, 1, v___x_4106_);
lean_ctor_set(v___x_4099_, 0, v___x_4105_);
v___x_4109_ = v___x_4099_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4105_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v___x_4106_);
v___x_4109_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; size_t v_sz_4153_; size_t v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; size_t v_sz_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4200_; 
v___x_4110_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_4111_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_4105_);
v___x_4112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4105_);
lean_ctor_set(v___x_4112_, 1, v___x_4110_);
lean_ctor_set(v___x_4112_, 2, v___x_4111_);
v___x_4113_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__1));
v___x_4114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_4115_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__3, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__3_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__3);
v___x_4116_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__5));
lean_inc(v_currMacroScope_4103_);
lean_inc(v_quotContext_4102_);
v___x_4117_ = l_Lean_addMacroScope(v_quotContext_4102_, v___x_4116_, v_currMacroScope_4103_);
v___x_4118_ = lean_box(0);
v___x_4119_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__8));
lean_inc(v___x_4105_);
v___x_4120_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4105_);
lean_ctor_set(v___x_4120_, 1, v___x_4115_);
lean_ctor_set(v___x_4120_, 2, v___x_4117_);
lean_ctor_set(v___x_4120_, 3, v___x_4119_);
v___x_4121_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10);
v___x_4122_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__11));
lean_inc(v_currMacroScope_4103_);
lean_inc(v_quotContext_4102_);
v___x_4123_ = l_Lean_addMacroScope(v_quotContext_4102_, v___x_4122_, v_currMacroScope_4103_);
v___x_4124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__6));
lean_inc(v___x_4105_);
v___x_4125_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4105_);
lean_ctor_set(v___x_4125_, 1, v___x_4121_);
lean_ctor_set(v___x_4125_, 2, v___x_4123_);
lean_ctor_set(v___x_4125_, 3, v___x_4124_);
lean_inc(v___x_4105_);
v___x_4126_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4110_, v___x_4125_);
lean_inc(v___x_4105_);
v___x_4127_ = l_Lean_Syntax_node2(v___x_4105_, v___x_4114_, v___x_4120_, v___x_4126_);
lean_inc_ref(v___x_4112_);
lean_inc(v___x_4105_);
v___x_4128_ = l_Lean_Syntax_node2(v___x_4105_, v___x_4113_, v___x_4112_, v___x_4127_);
lean_inc(v___x_4105_);
v___x_4129_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4110_, v___x_4128_);
v___x_4130_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__2));
lean_inc(v___x_4105_);
v___x_4131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4105_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
v___x_4132_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4));
v___x_4133_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4));
v___x_4134_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__5));
lean_inc(v___x_4105_);
v___x_4135_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4105_);
lean_ctor_set(v___x_4135_, 1, v___x_4134_);
v___x_4136_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26);
v___x_4137_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__27));
lean_inc(v_currMacroScope_4103_);
lean_inc(v_quotContext_4102_);
v___x_4138_ = l_Lean_addMacroScope(v_quotContext_4102_, v___x_4137_, v_currMacroScope_4103_);
v___x_4139_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__30));
lean_inc(v___x_4105_);
v___x_4140_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4105_);
lean_ctor_set(v___x_4140_, 1, v___x_4136_);
lean_ctor_set(v___x_4140_, 2, v___x_4138_);
lean_ctor_set(v___x_4140_, 3, v___x_4139_);
v___x_4141_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__10, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__10_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__10);
v___x_4142_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__11));
lean_inc(v_currMacroScope_4103_);
lean_inc(v_quotContext_4102_);
v___x_4143_ = l_Lean_addMacroScope(v_quotContext_4102_, v___x_4142_, v_currMacroScope_4103_);
lean_inc(v___x_4105_);
v___x_4144_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4105_);
lean_ctor_set(v___x_4144_, 1, v___x_4141_);
lean_ctor_set(v___x_4144_, 2, v___x_4143_);
lean_ctor_set(v___x_4144_, 3, v___x_4118_);
lean_inc_ref(v___x_4144_);
lean_inc(v___x_4105_);
v___x_4145_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4110_, v___x_4144_);
lean_inc(v___x_4105_);
v___x_4146_ = l_Lean_Syntax_node2(v___x_4105_, v___x_4114_, v___x_4140_, v___x_4145_);
lean_inc(v___x_4105_);
v___x_4147_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4110_, v___x_4146_);
lean_inc(v___x_4105_);
v___x_4148_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4110_, v___x_4147_);
v___x_4149_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__7));
lean_inc(v___x_4105_);
v___x_4150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4105_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
lean_inc_ref(v___x_4112_);
lean_inc(v___x_4105_);
v___x_4151_ = l_Lean_Syntax_node2(v___x_4105_, v___x_4113_, v___x_4112_, v___x_4144_);
lean_inc(v___x_4105_);
v___x_4152_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4110_, v___x_4151_);
v_sz_4153_ = lean_array_size(v_fst_4096_);
v___x_4154_ = ((size_t)0ULL);
v___x_4155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__0(v_sz_4153_, v___x_4154_, v_fst_4096_);
v___x_4156_ = l_Array_zip___redArg(v___x_4155_, v_snd_4097_);
lean_dec(v_snd_4097_);
lean_dec_ref(v___x_4155_);
v_sz_4157_ = lean_array_size(v___x_4156_);
lean_inc_ref(v___x_4150_);
lean_inc_ref(v___x_4135_);
lean_inc(v___x_4105_);
v___x_4158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__1(v___x_4105_, v___x_4135_, v___x_4150_, v_sz_4157_, v___x_4154_, v___x_4156_);
v___x_4159_ = l_Array_append___redArg(v___x_4111_, v___x_4158_);
lean_dec_ref(v___x_4158_);
v___x_4160_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1));
v___x_4161_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__2));
lean_inc(v___x_4105_);
v___x_4162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4105_);
lean_ctor_set(v___x_4162_, 1, v___x_4161_);
lean_inc(v___x_4105_);
v___x_4163_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4160_, v___x_4162_);
lean_inc(v___x_4105_);
v___x_4164_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4110_, v___x_4163_);
lean_inc(v___x_4105_);
v___x_4165_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4110_, v___x_4164_);
v___x_4166_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__13, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__13_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__13);
v___x_4167_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__15));
lean_inc(v_currMacroScope_4103_);
lean_inc(v_quotContext_4102_);
v___x_4168_ = l_Lean_addMacroScope(v_quotContext_4102_, v___x_4167_, v_currMacroScope_4103_);
v___x_4169_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__19));
lean_inc(v___x_4105_);
v___x_4170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4105_);
lean_ctor_set(v___x_4170_, 1, v___x_4166_);
lean_ctor_set(v___x_4170_, 2, v___x_4168_);
lean_ctor_set(v___x_4170_, 3, v___x_4169_);
v___x_4171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__34));
v___x_4172_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__20));
lean_inc(v___x_4105_);
v___x_4173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4105_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
lean_inc(v___x_4105_);
v___x_4174_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4171_, v___x_4173_);
lean_inc(v___x_4105_);
v___x_4175_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4110_, v___x_4174_);
lean_inc_ref(v___x_4170_);
lean_inc(v___x_4105_);
v___x_4176_ = l_Lean_Syntax_node2(v___x_4105_, v___x_4114_, v___x_4170_, v___x_4175_);
lean_inc_ref(v___x_4150_);
lean_inc_ref(v___x_4135_);
lean_inc(v___x_4105_);
v___x_4177_ = l_Lean_Syntax_node4(v___x_4105_, v___x_4133_, v___x_4135_, v___x_4165_, v___x_4150_, v___x_4176_);
v___x_4178_ = lean_array_push(v___x_4159_, v___x_4177_);
lean_inc(v___x_4105_);
v___x_4179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4105_);
lean_ctor_set(v___x_4179_, 1, v___x_4110_);
lean_ctor_set(v___x_4179_, 2, v___x_4178_);
lean_inc(v___x_4105_);
v___x_4180_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4132_, v___x_4179_);
lean_inc_ref(v___x_4131_);
lean_inc_ref_n(v___x_4112_, 2);
lean_inc_ref(v___x_4109_);
lean_inc(v___x_4105_);
v___x_4181_ = l_Lean_Syntax_node6(v___x_4105_, v___x_4107_, v___x_4109_, v___x_4112_, v___x_4112_, v___x_4152_, v___x_4131_, v___x_4180_);
lean_inc_ref(v___x_4150_);
lean_inc_ref(v___x_4135_);
lean_inc(v___x_4105_);
v___x_4182_ = l_Lean_Syntax_node4(v___x_4105_, v___x_4133_, v___x_4135_, v___x_4148_, v___x_4150_, v___x_4181_);
v___x_4183_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19);
v___x_4184_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__20));
v___x_4185_ = l_Lean_addMacroScope(v_quotContext_4102_, v___x_4184_, v_currMacroScope_4103_);
v___x_4186_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__24));
lean_inc(v___x_4105_);
v___x_4187_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4105_);
lean_ctor_set(v___x_4187_, 1, v___x_4183_);
lean_ctor_set(v___x_4187_, 2, v___x_4185_);
lean_ctor_set(v___x_4187_, 3, v___x_4186_);
lean_inc(v___x_4105_);
v___x_4188_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4110_, v___x_4187_);
lean_inc(v___x_4105_);
v___x_4189_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4110_, v___x_4188_);
v___x_4190_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__21));
lean_inc(v___x_4105_);
v___x_4191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4105_);
lean_ctor_set(v___x_4191_, 1, v___x_4190_);
lean_inc(v___x_4105_);
v___x_4192_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4171_, v___x_4191_);
lean_inc(v___x_4105_);
v___x_4193_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4110_, v___x_4192_);
lean_inc(v___x_4105_);
v___x_4194_ = l_Lean_Syntax_node2(v___x_4105_, v___x_4114_, v___x_4170_, v___x_4193_);
lean_inc(v___x_4105_);
v___x_4195_ = l_Lean_Syntax_node4(v___x_4105_, v___x_4133_, v___x_4135_, v___x_4189_, v___x_4150_, v___x_4194_);
lean_inc(v___x_4105_);
v___x_4196_ = l_Lean_Syntax_node2(v___x_4105_, v___x_4110_, v___x_4182_, v___x_4195_);
lean_inc(v___x_4105_);
v___x_4197_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4132_, v___x_4196_);
lean_inc_ref(v___x_4112_);
v___x_4198_ = l_Lean_Syntax_node6(v___x_4105_, v___x_4107_, v___x_4109_, v___x_4112_, v___x_4112_, v___x_4129_, v___x_4131_, v___x_4197_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 0, v___x_4198_);
v___x_4200_ = v___x_4093_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4198_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_dec_ref(v_a_4085_);
v_a_4205_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4090_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4090_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec(v_a_4086_);
lean_dec_ref(v_a_4085_);
lean_dec(v_a_4084_);
lean_dec_ref(v_a_4083_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec_ref(v_ctx_4079_);
v_a_4213_ = lean_ctor_get(v___x_4088_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4088_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4088_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___boxed(lean_object* v_ctx_4221_, lean_object* v_indName_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct(v_ctx_4221_, v_indName_4222_, v_a_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBody(lean_object* v_ctx_4231_, lean_object* v_header_4232_, lean_object* v_e_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v___x_4241_; lean_object* v_env_4242_; lean_object* v___x_4243_; lean_object* v_indName_4244_; uint8_t v___x_4245_; 
v___x_4241_ = lean_st_ref_get(v_a_4239_);
v_env_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc_ref(v_env_4242_);
lean_dec(v___x_4241_);
v___x_4243_ = l_Lean_Expr_getAppFn(v_e_4233_);
v_indName_4244_ = l_Lean_Expr_constName_x21(v___x_4243_);
lean_dec_ref(v___x_4243_);
lean_inc(v_indName_4244_);
v___x_4245_ = l_Lean_isStructure(v_env_4242_, v_indName_4244_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct(v_ctx_4231_, v_header_4232_, v_indName_4244_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
return v___x_4246_;
}
else
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct(v_header_4232_, v_indName_4244_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
lean_dec(v_a_4239_);
lean_dec(v_a_4237_);
lean_dec_ref(v_a_4236_);
lean_dec(v_a_4235_);
lean_dec_ref(v_a_4234_);
lean_dec_ref(v_header_4232_);
return v___x_4247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBody___boxed(lean_object* v_ctx_4248_, lean_object* v_header_4249_, lean_object* v_e_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBody(v_ctx_4248_, v_header_4249_, v_e_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_);
lean_dec_ref(v_e_4250_);
lean_dec_ref(v_ctx_4248_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0(lean_object* v_targetType_4270_, lean_object* v_ctx_4271_, lean_object* v_a_4272_, uint8_t v_usePartial_4273_, lean_object* v___x_4274_, lean_object* v___x_4275_, lean_object* v_auxFunName_4276_, lean_object* v_binders_4277_, lean_object* v___x_4278_, lean_object* v_argNames_4279_, lean_object* v_x_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v___x_4288_; uint8_t v___x_4289_; lean_object* v___x_4290_; 
v___x_4288_ = lean_box(0);
v___x_4289_ = 1;
lean_inc(v___y_4286_);
lean_inc_ref(v___y_4285_);
lean_inc(v___y_4284_);
lean_inc_ref(v___y_4283_);
lean_inc(v___y_4282_);
lean_inc_ref(v___y_4281_);
v___x_4290_ = l_Lean_Elab_Term_elabTerm(v_targetType_4270_, v___x_4288_, v___x_4289_, v___x_4289_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v___x_4292_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
lean_dec_ref(v___x_4290_);
lean_inc(v___y_4286_);
lean_inc_ref(v___y_4285_);
lean_inc(v___y_4284_);
lean_inc_ref(v___y_4283_);
lean_inc(v___y_4282_);
lean_inc_ref(v___y_4281_);
v___x_4292_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBody(v_ctx_4271_, v_a_4272_, v_a_4291_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
lean_dec(v_a_4291_);
if (lean_obj_tag(v___x_4292_) == 0)
{
if (v_usePartial_4273_ == 0)
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4354_; 
lean_dec(v___y_4286_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec_ref(v_argNames_4279_);
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4295_ = v___x_4292_;
v_isShared_4296_ = v_isSharedCheck_4354_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4292_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4354_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v_ref_4297_; lean_object* v_quotContext_4298_; lean_object* v_currMacroScope_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4352_; 
v_ref_4297_ = lean_ctor_get(v___y_4285_, 5);
lean_inc(v_ref_4297_);
v_quotContext_4298_ = lean_ctor_get(v___y_4285_, 10);
lean_inc(v_quotContext_4298_);
v_currMacroScope_4299_ = lean_ctor_get(v___y_4285_, 11);
lean_inc(v_currMacroScope_4299_);
lean_dec_ref(v___y_4285_);
v___x_4300_ = l_Lean_SourceInfo_fromRef(v_ref_4297_, v_usePartial_4273_);
lean_dec(v_ref_4297_);
v___x_4301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21));
v___x_4302_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__0));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4303_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4301_, v___x_4302_);
v___x_4304_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__1));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4305_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4301_, v___x_4304_);
v___x_4306_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_4307_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_4300_);
v___x_4308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4300_);
lean_ctor_set(v___x_4308_, 1, v___x_4306_);
lean_ctor_set(v___x_4308_, 2, v___x_4307_);
lean_inc_ref_n(v___x_4308_, 7);
lean_inc(v___x_4300_);
v___x_4309_ = l_Lean_Syntax_node7(v___x_4300_, v___x_4305_, v___x_4308_, v___x_4308_, v___x_4308_, v___x_4308_, v___x_4308_, v___x_4308_, v___x_4308_);
v___x_4310_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__2));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4311_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4301_, v___x_4310_);
v___x_4312_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__3));
lean_inc(v___x_4300_);
v___x_4313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4300_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
v___x_4314_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__4));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4315_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4301_, v___x_4314_);
v___x_4316_ = lean_mk_syntax_ident(v_auxFunName_4276_);
lean_inc_ref(v___x_4308_);
lean_inc(v___x_4300_);
v___x_4317_ = l_Lean_Syntax_node2(v___x_4300_, v___x_4315_, v___x_4316_, v___x_4308_);
v___x_4318_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__5));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4319_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4301_, v___x_4318_);
v___x_4320_ = l_Array_append___redArg(v___x_4307_, v_binders_4277_);
lean_inc(v___x_4300_);
v___x_4321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4300_);
lean_ctor_set(v___x_4321_, 1, v___x_4306_);
lean_ctor_set(v___x_4321_, 2, v___x_4320_);
v___x_4322_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__6));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4323_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4278_, v___x_4322_);
v___x_4324_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__16));
lean_inc(v___x_4300_);
v___x_4325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4300_);
lean_ctor_set(v___x_4325_, 1, v___x_4324_);
v___x_4326_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12));
v___x_4327_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17);
v___x_4328_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__18));
v___x_4329_ = l_Lean_addMacroScope(v_quotContext_4298_, v___x_4328_, v_currMacroScope_4299_);
lean_inc_ref(v___x_4274_);
v___x_4330_ = l_Lean_Name_mkStr2(v___x_4274_, v___x_4326_);
v___x_4331_ = lean_box(0);
lean_inc(v___x_4330_);
v___x_4332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4330_);
lean_ctor_set(v___x_4332_, 1, v___x_4331_);
v___x_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4330_);
v___x_4334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
lean_ctor_set(v___x_4334_, 1, v___x_4331_);
v___x_4335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4332_);
lean_ctor_set(v___x_4335_, 1, v___x_4334_);
lean_inc(v___x_4300_);
v___x_4336_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4300_);
lean_ctor_set(v___x_4336_, 1, v___x_4327_);
lean_ctor_set(v___x_4336_, 2, v___x_4329_);
lean_ctor_set(v___x_4336_, 3, v___x_4335_);
lean_inc(v___x_4300_);
v___x_4337_ = l_Lean_Syntax_node2(v___x_4300_, v___x_4323_, v___x_4325_, v___x_4336_);
lean_inc(v___x_4300_);
v___x_4338_ = l_Lean_Syntax_node1(v___x_4300_, v___x_4306_, v___x_4337_);
lean_inc(v___x_4300_);
v___x_4339_ = l_Lean_Syntax_node2(v___x_4300_, v___x_4319_, v___x_4321_, v___x_4338_);
v___x_4340_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__7));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4341_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4301_, v___x_4340_);
v___x_4342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6));
lean_inc(v___x_4300_);
v___x_4343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4300_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
v___x_4344_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__8));
v___x_4345_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__9));
v___x_4346_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4344_, v___x_4345_);
lean_inc_ref_n(v___x_4308_, 2);
lean_inc(v___x_4300_);
v___x_4347_ = l_Lean_Syntax_node2(v___x_4300_, v___x_4346_, v___x_4308_, v___x_4308_);
lean_inc_ref(v___x_4308_);
lean_inc(v___x_4300_);
v___x_4348_ = l_Lean_Syntax_node4(v___x_4300_, v___x_4341_, v___x_4343_, v_a_4293_, v___x_4347_, v___x_4308_);
lean_inc(v___x_4300_);
v___x_4349_ = l_Lean_Syntax_node5(v___x_4300_, v___x_4311_, v___x_4313_, v___x_4317_, v___x_4339_, v___x_4348_, v___x_4308_);
v___x_4350_ = l_Lean_Syntax_node2(v___x_4300_, v___x_4303_, v___x_4309_, v___x_4349_);
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4350_);
v___x_4352_ = v___x_4295_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4350_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
else
{
lean_object* v_a_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v_a_4355_ = lean_ctor_get(v___x_4292_, 0);
lean_inc(v_a_4355_);
lean_dec_ref(v___x_4292_);
v___x_4356_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__1));
lean_inc_ref(v___x_4274_);
v___x_4357_ = l_Lean_Name_mkStr2(v___x_4274_, v___x_4356_);
lean_inc(v___y_4286_);
lean_inc_ref(v___y_4285_);
lean_inc(v___y_4284_);
lean_inc_ref(v___y_4283_);
lean_inc(v___y_4282_);
lean_inc_ref(v___y_4281_);
v___x_4358_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_4271_, v___x_4357_, v_argNames_4279_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4360_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref(v___x_4358_);
v___x_4360_ = l_Lean_Elab_Deriving_mkLet(v_a_4359_, v_a_4355_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
lean_dec(v___y_4286_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec(v_a_4359_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4428_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4363_ = v___x_4360_;
v_isShared_4364_ = v_isSharedCheck_4428_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4360_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4428_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v_ref_4365_; lean_object* v_quotContext_4366_; lean_object* v_currMacroScope_4367_; uint8_t v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4426_; 
v_ref_4365_ = lean_ctor_get(v___y_4285_, 5);
lean_inc(v_ref_4365_);
v_quotContext_4366_ = lean_ctor_get(v___y_4285_, 10);
lean_inc(v_quotContext_4366_);
v_currMacroScope_4367_ = lean_ctor_get(v___y_4285_, 11);
lean_inc(v_currMacroScope_4367_);
lean_dec_ref(v___y_4285_);
v___x_4368_ = 0;
v___x_4369_ = l_Lean_SourceInfo_fromRef(v_ref_4365_, v___x_4368_);
lean_dec(v_ref_4365_);
v___x_4370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21));
v___x_4371_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__0));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4372_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4370_, v___x_4371_);
v___x_4373_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__1));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4374_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4370_, v___x_4373_);
v___x_4375_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_4376_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_4369_);
v___x_4377_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4369_);
lean_ctor_set(v___x_4377_, 1, v___x_4375_);
lean_ctor_set(v___x_4377_, 2, v___x_4376_);
v___x_4378_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__10));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4379_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4370_, v___x_4378_);
lean_inc(v___x_4369_);
v___x_4380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4369_);
lean_ctor_set(v___x_4380_, 1, v___x_4378_);
lean_inc(v___x_4369_);
v___x_4381_ = l_Lean_Syntax_node1(v___x_4369_, v___x_4379_, v___x_4380_);
lean_inc(v___x_4369_);
v___x_4382_ = l_Lean_Syntax_node1(v___x_4369_, v___x_4375_, v___x_4381_);
lean_inc_ref_n(v___x_4377_, 6);
lean_inc(v___x_4369_);
v___x_4383_ = l_Lean_Syntax_node7(v___x_4369_, v___x_4374_, v___x_4377_, v___x_4377_, v___x_4377_, v___x_4377_, v___x_4377_, v___x_4377_, v___x_4382_);
v___x_4384_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__2));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4385_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4370_, v___x_4384_);
v___x_4386_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__3));
lean_inc(v___x_4369_);
v___x_4387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4369_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__4));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4389_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4370_, v___x_4388_);
v___x_4390_ = lean_mk_syntax_ident(v_auxFunName_4276_);
lean_inc_ref(v___x_4377_);
lean_inc(v___x_4369_);
v___x_4391_ = l_Lean_Syntax_node2(v___x_4369_, v___x_4389_, v___x_4390_, v___x_4377_);
v___x_4392_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__5));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4393_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4370_, v___x_4392_);
v___x_4394_ = l_Array_append___redArg(v___x_4376_, v_binders_4277_);
lean_inc(v___x_4369_);
v___x_4395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4369_);
lean_ctor_set(v___x_4395_, 1, v___x_4375_);
lean_ctor_set(v___x_4395_, 2, v___x_4394_);
v___x_4396_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__6));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4397_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4278_, v___x_4396_);
v___x_4398_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__16));
lean_inc(v___x_4369_);
v___x_4399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4369_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
v___x_4400_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12));
v___x_4401_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17);
v___x_4402_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__18));
v___x_4403_ = l_Lean_addMacroScope(v_quotContext_4366_, v___x_4402_, v_currMacroScope_4367_);
lean_inc_ref(v___x_4274_);
v___x_4404_ = l_Lean_Name_mkStr2(v___x_4274_, v___x_4400_);
v___x_4405_ = lean_box(0);
lean_inc(v___x_4404_);
v___x_4406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4404_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4404_);
v___x_4408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4407_);
lean_ctor_set(v___x_4408_, 1, v___x_4405_);
v___x_4409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4406_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
lean_inc(v___x_4369_);
v___x_4410_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4369_);
lean_ctor_set(v___x_4410_, 1, v___x_4401_);
lean_ctor_set(v___x_4410_, 2, v___x_4403_);
lean_ctor_set(v___x_4410_, 3, v___x_4409_);
lean_inc(v___x_4369_);
v___x_4411_ = l_Lean_Syntax_node2(v___x_4369_, v___x_4397_, v___x_4399_, v___x_4410_);
lean_inc(v___x_4369_);
v___x_4412_ = l_Lean_Syntax_node1(v___x_4369_, v___x_4375_, v___x_4411_);
lean_inc(v___x_4369_);
v___x_4413_ = l_Lean_Syntax_node2(v___x_4369_, v___x_4393_, v___x_4395_, v___x_4412_);
v___x_4414_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__7));
lean_inc_ref(v___x_4275_);
lean_inc_ref(v___x_4274_);
v___x_4415_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4370_, v___x_4414_);
v___x_4416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6));
lean_inc(v___x_4369_);
v___x_4417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4369_);
lean_ctor_set(v___x_4417_, 1, v___x_4416_);
v___x_4418_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__8));
v___x_4419_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__9));
v___x_4420_ = l_Lean_Name_mkStr4(v___x_4274_, v___x_4275_, v___x_4418_, v___x_4419_);
lean_inc_ref_n(v___x_4377_, 2);
lean_inc(v___x_4369_);
v___x_4421_ = l_Lean_Syntax_node2(v___x_4369_, v___x_4420_, v___x_4377_, v___x_4377_);
lean_inc_ref(v___x_4377_);
lean_inc(v___x_4369_);
v___x_4422_ = l_Lean_Syntax_node4(v___x_4369_, v___x_4415_, v___x_4417_, v_a_4361_, v___x_4421_, v___x_4377_);
lean_inc(v___x_4369_);
v___x_4423_ = l_Lean_Syntax_node5(v___x_4369_, v___x_4385_, v___x_4387_, v___x_4391_, v___x_4413_, v___x_4422_, v___x_4377_);
v___x_4424_ = l_Lean_Syntax_node2(v___x_4369_, v___x_4372_, v___x_4383_, v___x_4423_);
if (v_isShared_4364_ == 0)
{
lean_ctor_set(v___x_4363_, 0, v___x_4424_);
v___x_4426_ = v___x_4363_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
else
{
lean_dec_ref(v___y_4285_);
lean_dec_ref(v___x_4278_);
lean_dec(v_auxFunName_4276_);
lean_dec_ref(v___x_4275_);
lean_dec_ref(v___x_4274_);
return v___x_4360_;
}
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec(v_a_4355_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec_ref(v___x_4278_);
lean_dec(v_auxFunName_4276_);
lean_dec_ref(v___x_4275_);
lean_dec_ref(v___x_4274_);
v_a_4429_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4358_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4358_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
}
}
else
{
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec_ref(v_argNames_4279_);
lean_dec_ref(v___x_4278_);
lean_dec(v_auxFunName_4276_);
lean_dec_ref(v___x_4275_);
lean_dec_ref(v___x_4274_);
return v___x_4292_;
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec_ref(v_argNames_4279_);
lean_dec_ref(v___x_4278_);
lean_dec(v_auxFunName_4276_);
lean_dec_ref(v___x_4275_);
lean_dec_ref(v___x_4274_);
lean_dec_ref(v_a_4272_);
v_a_4437_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4290_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4290_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___boxed(lean_object** _args){
lean_object* v_targetType_4445_ = _args[0];
lean_object* v_ctx_4446_ = _args[1];
lean_object* v_a_4447_ = _args[2];
lean_object* v_usePartial_4448_ = _args[3];
lean_object* v___x_4449_ = _args[4];
lean_object* v___x_4450_ = _args[5];
lean_object* v_auxFunName_4451_ = _args[6];
lean_object* v_binders_4452_ = _args[7];
lean_object* v___x_4453_ = _args[8];
lean_object* v_argNames_4454_ = _args[9];
lean_object* v_x_4455_ = _args[10];
lean_object* v___y_4456_ = _args[11];
lean_object* v___y_4457_ = _args[12];
lean_object* v___y_4458_ = _args[13];
lean_object* v___y_4459_ = _args[14];
lean_object* v___y_4460_ = _args[15];
lean_object* v___y_4461_ = _args[16];
lean_object* v___y_4462_ = _args[17];
_start:
{
uint8_t v_usePartial_boxed_4463_; lean_object* v_res_4464_; 
v_usePartial_boxed_4463_ = lean_unbox(v_usePartial_4448_);
v_res_4464_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0(v_targetType_4445_, v_ctx_4446_, v_a_4447_, v_usePartial_boxed_4463_, v___x_4449_, v___x_4450_, v_auxFunName_4451_, v_binders_4452_, v___x_4453_, v_argNames_4454_, v_x_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
lean_dec_ref(v_x_4455_);
lean_dec_ref(v_binders_4452_);
lean_dec_ref(v_ctx_4446_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction(lean_object* v_ctx_4465_, lean_object* v_i_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v_typeInfos_4474_; lean_object* v_auxFunNames_4475_; uint8_t v_usePartial_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v_typeInfos_4474_ = lean_ctor_get(v_ctx_4465_, 1);
v_auxFunNames_4475_ = lean_ctor_get(v_ctx_4465_, 2);
v_usePartial_4476_ = lean_ctor_get_uint8(v_ctx_4465_, sizeof(void*)*3);
v___x_4477_ = l_Lean_instInhabitedInductiveVal_default;
v___x_4478_ = lean_array_get_borrowed(v___x_4477_, v_typeInfos_4474_, v_i_4466_);
lean_inc(v_a_4472_);
lean_inc_ref(v_a_4471_);
lean_inc(v_a_4470_);
lean_inc_ref(v_a_4469_);
lean_inc(v_a_4468_);
lean_inc_ref(v_a_4467_);
lean_inc(v___x_4478_);
v___x_4479_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader(v___x_4478_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; lean_object* v_binders_4481_; lean_object* v_argNames_4482_; lean_object* v_targetType_4483_; lean_object* v___x_4484_; lean_object* v_auxFunName_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___f_4490_; lean_object* v___x_4491_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref(v___x_4479_);
v_binders_4481_ = lean_ctor_get(v_a_4480_, 0);
lean_inc_ref(v_binders_4481_);
v_argNames_4482_ = lean_ctor_get(v_a_4480_, 1);
lean_inc_ref(v_argNames_4482_);
v_targetType_4483_ = lean_ctor_get(v_a_4480_, 3);
lean_inc(v_targetType_4483_);
v___x_4484_ = lean_box(0);
v_auxFunName_4485_ = lean_array_get(v___x_4484_, v_auxFunNames_4475_, v_i_4466_);
v___x_4486_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0));
v___x_4487_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2));
v___x_4488_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3));
v___x_4489_ = lean_box(v_usePartial_4476_);
lean_inc_ref(v_binders_4481_);
v___f_4490_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___boxed), 18, 10);
lean_closure_set(v___f_4490_, 0, v_targetType_4483_);
lean_closure_set(v___f_4490_, 1, v_ctx_4465_);
lean_closure_set(v___f_4490_, 2, v_a_4480_);
lean_closure_set(v___f_4490_, 3, v___x_4489_);
lean_closure_set(v___f_4490_, 4, v___x_4486_);
lean_closure_set(v___f_4490_, 5, v___x_4487_);
lean_closure_set(v___f_4490_, 6, v_auxFunName_4485_);
lean_closure_set(v___f_4490_, 7, v_binders_4481_);
lean_closure_set(v___f_4490_, 8, v___x_4488_);
lean_closure_set(v___f_4490_, 9, v_argNames_4482_);
v___x_4491_ = l_Lean_Elab_Term_elabBinders___redArg(v_binders_4481_, v___f_4490_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_);
return v___x_4491_;
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec(v_a_4472_);
lean_dec_ref(v_a_4471_);
lean_dec(v_a_4470_);
lean_dec_ref(v_a_4469_);
lean_dec(v_a_4468_);
lean_dec_ref(v_a_4467_);
lean_dec_ref(v_ctx_4465_);
v_a_4492_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4479_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4479_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___boxed(lean_object* v_ctx_4500_, lean_object* v_i_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_){
_start:
{
lean_object* v_res_4509_; 
v_res_4509_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction(v_ctx_4500_, v_i_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_);
lean_dec(v_i_4501_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBody(lean_object* v_ctx_4510_, lean_object* v_e_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_){
_start:
{
lean_object* v___x_4519_; lean_object* v_env_4520_; lean_object* v___x_4521_; lean_object* v_indName_4522_; uint8_t v___x_4523_; 
v___x_4519_ = lean_st_ref_get(v_a_4517_);
v_env_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc_ref(v_env_4520_);
lean_dec(v___x_4519_);
v___x_4521_ = l_Lean_Expr_getAppFn(v_e_4511_);
v_indName_4522_ = l_Lean_Expr_constName_x21(v___x_4521_);
lean_dec_ref(v___x_4521_);
lean_inc(v_indName_4522_);
v___x_4523_ = l_Lean_isStructure(v_env_4520_, v_indName_4522_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; 
v___x_4524_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct(v_ctx_4510_, v_indName_4522_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
return v___x_4524_;
}
else
{
lean_object* v___x_4525_; 
lean_dec_ref(v_ctx_4510_);
v___x_4525_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct(v_indName_4522_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
lean_dec(v_a_4517_);
lean_dec(v_a_4515_);
lean_dec_ref(v_a_4514_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
return v___x_4525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBody___boxed(lean_object* v_ctx_4526_, lean_object* v_e_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonBody(v_ctx_4526_, v_e_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
lean_dec_ref(v_e_4527_);
return v_res_4535_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__11));
v___x_4537_ = l_String_toRawSubstring_x27(v___x_4536_);
return v___x_4537_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4552_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__6));
v___x_4553_ = l_String_toRawSubstring_x27(v___x_4552_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0(lean_object* v_targetType_4567_, lean_object* v_ctx_4568_, lean_object* v___x_4569_, lean_object* v_argNames_4570_, lean_object* v_indval_4571_, lean_object* v___x_4572_, lean_object* v_auxFunName_4573_, lean_object* v_binders_4574_, lean_object* v___x_4575_, uint8_t v_usePartial_4576_, lean_object* v_x_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
lean_object* v___x_4585_; uint8_t v___x_4586_; lean_object* v___x_4587_; 
v___x_4585_ = lean_box(0);
v___x_4586_ = 1;
lean_inc(v___y_4583_);
lean_inc_ref(v___y_4582_);
lean_inc(v___y_4581_);
lean_inc_ref(v___y_4580_);
lean_inc(v___y_4579_);
lean_inc_ref(v___y_4578_);
v___x_4587_ = l_Lean_Elab_Term_elabTerm(v_targetType_4567_, v___x_4585_, v___x_4586_, v___x_4586_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v___x_4589_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc(v_a_4588_);
lean_dec_ref(v___x_4587_);
lean_inc(v___y_4583_);
lean_inc_ref(v___y_4582_);
lean_inc(v___y_4581_);
lean_inc_ref(v___y_4580_);
lean_inc(v___y_4579_);
lean_inc_ref(v___y_4578_);
lean_inc_ref(v_ctx_4568_);
v___x_4589_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonBody(v_ctx_4568_, v_a_4588_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
lean_dec(v_a_4588_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; 
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
lean_inc(v_a_4590_);
lean_dec_ref(v___x_4589_);
if (v_usePartial_4576_ == 0)
{
uint8_t v_isRec_4678_; 
v_isRec_4678_ = lean_ctor_get_uint8(v_indval_4571_, sizeof(void*)*6);
if (v_isRec_4678_ == 0)
{
lean_object* v___x_4679_; 
lean_dec(v___y_4583_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec_ref(v_ctx_4568_);
v___x_4679_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indval_4571_, v_argNames_4570_, v___y_4582_);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4744_; 
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4682_ = v___x_4679_;
v_isShared_4683_ = v_isSharedCheck_4744_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4679_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4744_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v_ref_4684_; lean_object* v_quotContext_4685_; lean_object* v_currMacroScope_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4742_; 
v_ref_4684_ = lean_ctor_get(v___y_4582_, 5);
lean_inc(v_ref_4684_);
v_quotContext_4685_ = lean_ctor_get(v___y_4582_, 10);
lean_inc(v_quotContext_4685_);
v_currMacroScope_4686_ = lean_ctor_get(v___y_4582_, 11);
lean_inc(v_currMacroScope_4686_);
lean_dec_ref(v___y_4582_);
v___x_4687_ = l_Lean_SourceInfo_fromRef(v_ref_4684_, v_isRec_4678_);
lean_dec(v_ref_4684_);
v___x_4688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21));
v___x_4689_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__0));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4690_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4688_, v___x_4689_);
v___x_4691_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__1));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4692_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4688_, v___x_4691_);
v___x_4693_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_4694_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_4687_);
v___x_4695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4687_);
lean_ctor_set(v___x_4695_, 1, v___x_4693_);
lean_ctor_set(v___x_4695_, 2, v___x_4694_);
lean_inc_ref_n(v___x_4695_, 7);
lean_inc(v___x_4687_);
v___x_4696_ = l_Lean_Syntax_node7(v___x_4687_, v___x_4692_, v___x_4695_, v___x_4695_, v___x_4695_, v___x_4695_, v___x_4695_, v___x_4695_, v___x_4695_);
v___x_4697_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__2));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4698_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4688_, v___x_4697_);
v___x_4699_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__3));
lean_inc(v___x_4687_);
v___x_4700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4687_);
lean_ctor_set(v___x_4700_, 1, v___x_4699_);
v___x_4701_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__4));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4702_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4688_, v___x_4701_);
v___x_4703_ = lean_mk_syntax_ident(v_auxFunName_4573_);
lean_inc_ref(v___x_4695_);
lean_inc(v___x_4687_);
v___x_4704_ = l_Lean_Syntax_node2(v___x_4687_, v___x_4702_, v___x_4703_, v___x_4695_);
v___x_4705_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__5));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4706_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4688_, v___x_4705_);
v___x_4707_ = l_Array_append___redArg(v___x_4694_, v_binders_4574_);
lean_inc(v___x_4687_);
v___x_4708_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4708_, 0, v___x_4687_);
lean_ctor_set(v___x_4708_, 1, v___x_4693_);
lean_ctor_set(v___x_4708_, 2, v___x_4707_);
v___x_4709_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__6));
lean_inc_ref(v___x_4575_);
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4710_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4575_, v___x_4709_);
v___x_4711_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__16));
lean_inc(v___x_4687_);
v___x_4712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4687_);
lean_ctor_set(v___x_4712_, 1, v___x_4711_);
v___x_4713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__30));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4714_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4575_, v___x_4713_);
v___x_4715_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0);
v___x_4716_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__1));
lean_inc(v_currMacroScope_4686_);
lean_inc(v_quotContext_4685_);
v___x_4717_ = l_Lean_addMacroScope(v_quotContext_4685_, v___x_4716_, v_currMacroScope_4686_);
v___x_4718_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__5));
lean_inc(v___x_4687_);
v___x_4719_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4687_);
lean_ctor_set(v___x_4719_, 1, v___x_4715_);
lean_ctor_set(v___x_4719_, 2, v___x_4717_);
lean_ctor_set(v___x_4719_, 3, v___x_4718_);
v___x_4720_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7);
v___x_4721_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__8));
v___x_4722_ = l_Lean_addMacroScope(v_quotContext_4685_, v___x_4721_, v_currMacroScope_4686_);
v___x_4723_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__12));
lean_inc(v___x_4687_);
v___x_4724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4687_);
lean_ctor_set(v___x_4724_, 1, v___x_4720_);
lean_ctor_set(v___x_4724_, 2, v___x_4722_);
lean_ctor_set(v___x_4724_, 3, v___x_4723_);
lean_inc(v___x_4687_);
v___x_4725_ = l_Lean_Syntax_node2(v___x_4687_, v___x_4693_, v___x_4724_, v_a_4680_);
lean_inc(v___x_4687_);
v___x_4726_ = l_Lean_Syntax_node2(v___x_4687_, v___x_4714_, v___x_4719_, v___x_4725_);
lean_inc(v___x_4687_);
v___x_4727_ = l_Lean_Syntax_node2(v___x_4687_, v___x_4710_, v___x_4712_, v___x_4726_);
lean_inc(v___x_4687_);
v___x_4728_ = l_Lean_Syntax_node1(v___x_4687_, v___x_4693_, v___x_4727_);
lean_inc(v___x_4687_);
v___x_4729_ = l_Lean_Syntax_node2(v___x_4687_, v___x_4706_, v___x_4708_, v___x_4728_);
v___x_4730_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__7));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4731_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4688_, v___x_4730_);
v___x_4732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6));
lean_inc(v___x_4687_);
v___x_4733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4687_);
lean_ctor_set(v___x_4733_, 1, v___x_4732_);
v___x_4734_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__8));
v___x_4735_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__9));
v___x_4736_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4734_, v___x_4735_);
lean_inc_ref_n(v___x_4695_, 2);
lean_inc(v___x_4687_);
v___x_4737_ = l_Lean_Syntax_node2(v___x_4687_, v___x_4736_, v___x_4695_, v___x_4695_);
lean_inc_ref(v___x_4695_);
lean_inc(v___x_4687_);
v___x_4738_ = l_Lean_Syntax_node4(v___x_4687_, v___x_4731_, v___x_4733_, v_a_4590_, v___x_4737_, v___x_4695_);
lean_inc(v___x_4687_);
v___x_4739_ = l_Lean_Syntax_node5(v___x_4687_, v___x_4698_, v___x_4700_, v___x_4704_, v___x_4729_, v___x_4738_, v___x_4695_);
v___x_4740_ = l_Lean_Syntax_node2(v___x_4687_, v___x_4690_, v___x_4696_, v___x_4739_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 0, v___x_4740_);
v___x_4742_ = v___x_4682_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4740_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
else
{
lean_dec(v_a_4590_);
lean_dec_ref(v___y_4582_);
lean_dec_ref(v___x_4575_);
lean_dec(v_auxFunName_4573_);
lean_dec_ref(v___x_4572_);
lean_dec_ref(v___x_4569_);
return v___x_4679_;
}
}
else
{
goto v___jp_4591_;
}
}
else
{
goto v___jp_4591_;
}
v___jp_4591_:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4592_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__0));
lean_inc_ref(v___x_4569_);
v___x_4593_ = l_Lean_Name_mkStr2(v___x_4569_, v___x_4592_);
lean_inc(v___y_4583_);
lean_inc_ref(v___y_4582_);
lean_inc(v___y_4581_);
lean_inc_ref(v___y_4580_);
lean_inc(v___y_4579_);
lean_inc_ref(v___y_4578_);
lean_inc_ref(v_argNames_4570_);
v___x_4594_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_4568_, v___x_4593_, v_argNames_4570_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
lean_dec_ref(v_ctx_4568_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_a_4595_; lean_object* v___x_4596_; 
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
lean_inc(v_a_4595_);
lean_dec_ref(v___x_4594_);
v___x_4596_ = l_Lean_Elab_Deriving_mkLet(v_a_4595_, v_a_4590_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
lean_dec(v___y_4583_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v_a_4595_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4598_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
lean_dec_ref(v___x_4596_);
v___x_4598_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indval_4571_, v_argNames_4570_, v___y_4582_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4669_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4601_ = v___x_4598_;
v_isShared_4602_ = v_isSharedCheck_4669_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4598_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4669_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v_ref_4603_; lean_object* v_quotContext_4604_; lean_object* v_currMacroScope_4605_; uint8_t v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4667_; 
v_ref_4603_ = lean_ctor_get(v___y_4582_, 5);
lean_inc(v_ref_4603_);
v_quotContext_4604_ = lean_ctor_get(v___y_4582_, 10);
lean_inc(v_quotContext_4604_);
v_currMacroScope_4605_ = lean_ctor_get(v___y_4582_, 11);
lean_inc(v_currMacroScope_4605_);
lean_dec_ref(v___y_4582_);
v___x_4606_ = 0;
v___x_4607_ = l_Lean_SourceInfo_fromRef(v_ref_4603_, v___x_4606_);
lean_dec(v_ref_4603_);
v___x_4608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21));
v___x_4609_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__0));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4610_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4608_, v___x_4609_);
v___x_4611_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__1));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4612_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4608_, v___x_4611_);
v___x_4613_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_4614_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_4607_);
v___x_4615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4607_);
lean_ctor_set(v___x_4615_, 1, v___x_4613_);
lean_ctor_set(v___x_4615_, 2, v___x_4614_);
v___x_4616_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__10));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4617_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4608_, v___x_4616_);
lean_inc(v___x_4607_);
v___x_4618_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4607_);
lean_ctor_set(v___x_4618_, 1, v___x_4616_);
lean_inc(v___x_4607_);
v___x_4619_ = l_Lean_Syntax_node1(v___x_4607_, v___x_4617_, v___x_4618_);
lean_inc(v___x_4607_);
v___x_4620_ = l_Lean_Syntax_node1(v___x_4607_, v___x_4613_, v___x_4619_);
lean_inc_ref_n(v___x_4615_, 6);
lean_inc(v___x_4607_);
v___x_4621_ = l_Lean_Syntax_node7(v___x_4607_, v___x_4612_, v___x_4615_, v___x_4615_, v___x_4615_, v___x_4615_, v___x_4615_, v___x_4615_, v___x_4620_);
v___x_4622_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__2));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4623_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4608_, v___x_4622_);
v___x_4624_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__3));
lean_inc(v___x_4607_);
v___x_4625_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4607_);
lean_ctor_set(v___x_4625_, 1, v___x_4624_);
v___x_4626_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__4));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4627_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4608_, v___x_4626_);
v___x_4628_ = lean_mk_syntax_ident(v_auxFunName_4573_);
lean_inc_ref(v___x_4615_);
lean_inc(v___x_4607_);
v___x_4629_ = l_Lean_Syntax_node2(v___x_4607_, v___x_4627_, v___x_4628_, v___x_4615_);
v___x_4630_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__5));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4631_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4608_, v___x_4630_);
v___x_4632_ = l_Array_append___redArg(v___x_4614_, v_binders_4574_);
lean_inc(v___x_4607_);
v___x_4633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4607_);
lean_ctor_set(v___x_4633_, 1, v___x_4613_);
lean_ctor_set(v___x_4633_, 2, v___x_4632_);
v___x_4634_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__6));
lean_inc_ref(v___x_4575_);
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4635_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4575_, v___x_4634_);
v___x_4636_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__16));
lean_inc(v___x_4607_);
v___x_4637_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4607_);
lean_ctor_set(v___x_4637_, 1, v___x_4636_);
v___x_4638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__30));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4639_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4575_, v___x_4638_);
v___x_4640_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0);
v___x_4641_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__1));
lean_inc(v_currMacroScope_4605_);
lean_inc(v_quotContext_4604_);
v___x_4642_ = l_Lean_addMacroScope(v_quotContext_4604_, v___x_4641_, v_currMacroScope_4605_);
v___x_4643_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__5));
lean_inc(v___x_4607_);
v___x_4644_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4607_);
lean_ctor_set(v___x_4644_, 1, v___x_4640_);
lean_ctor_set(v___x_4644_, 2, v___x_4642_);
lean_ctor_set(v___x_4644_, 3, v___x_4643_);
v___x_4645_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7);
v___x_4646_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__8));
v___x_4647_ = l_Lean_addMacroScope(v_quotContext_4604_, v___x_4646_, v_currMacroScope_4605_);
v___x_4648_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__12));
lean_inc(v___x_4607_);
v___x_4649_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4607_);
lean_ctor_set(v___x_4649_, 1, v___x_4645_);
lean_ctor_set(v___x_4649_, 2, v___x_4647_);
lean_ctor_set(v___x_4649_, 3, v___x_4648_);
lean_inc(v___x_4607_);
v___x_4650_ = l_Lean_Syntax_node2(v___x_4607_, v___x_4613_, v___x_4649_, v_a_4599_);
lean_inc(v___x_4607_);
v___x_4651_ = l_Lean_Syntax_node2(v___x_4607_, v___x_4639_, v___x_4644_, v___x_4650_);
lean_inc(v___x_4607_);
v___x_4652_ = l_Lean_Syntax_node2(v___x_4607_, v___x_4635_, v___x_4637_, v___x_4651_);
lean_inc(v___x_4607_);
v___x_4653_ = l_Lean_Syntax_node1(v___x_4607_, v___x_4613_, v___x_4652_);
lean_inc(v___x_4607_);
v___x_4654_ = l_Lean_Syntax_node2(v___x_4607_, v___x_4631_, v___x_4633_, v___x_4653_);
v___x_4655_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__7));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
v___x_4656_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4608_, v___x_4655_);
v___x_4657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6));
lean_inc(v___x_4607_);
v___x_4658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4607_);
lean_ctor_set(v___x_4658_, 1, v___x_4657_);
v___x_4659_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__8));
v___x_4660_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__9));
v___x_4661_ = l_Lean_Name_mkStr4(v___x_4569_, v___x_4572_, v___x_4659_, v___x_4660_);
lean_inc_ref_n(v___x_4615_, 2);
lean_inc(v___x_4607_);
v___x_4662_ = l_Lean_Syntax_node2(v___x_4607_, v___x_4661_, v___x_4615_, v___x_4615_);
lean_inc_ref(v___x_4615_);
lean_inc(v___x_4607_);
v___x_4663_ = l_Lean_Syntax_node4(v___x_4607_, v___x_4656_, v___x_4658_, v_a_4597_, v___x_4662_, v___x_4615_);
lean_inc(v___x_4607_);
v___x_4664_ = l_Lean_Syntax_node5(v___x_4607_, v___x_4623_, v___x_4625_, v___x_4629_, v___x_4654_, v___x_4663_, v___x_4615_);
v___x_4665_ = l_Lean_Syntax_node2(v___x_4607_, v___x_4610_, v___x_4621_, v___x_4664_);
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v___x_4665_);
v___x_4667_ = v___x_4601_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v___x_4665_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
else
{
lean_dec(v_a_4597_);
lean_dec_ref(v___y_4582_);
lean_dec_ref(v___x_4575_);
lean_dec(v_auxFunName_4573_);
lean_dec_ref(v___x_4572_);
lean_dec_ref(v___x_4569_);
return v___x_4598_;
}
}
else
{
lean_dec_ref(v___y_4582_);
lean_dec_ref(v___x_4575_);
lean_dec(v_auxFunName_4573_);
lean_dec_ref(v___x_4572_);
lean_dec_ref(v_indval_4571_);
lean_dec_ref(v_argNames_4570_);
lean_dec_ref(v___x_4569_);
return v___x_4596_;
}
}
else
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4677_; 
lean_dec(v_a_4590_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec_ref(v___x_4575_);
lean_dec(v_auxFunName_4573_);
lean_dec_ref(v___x_4572_);
lean_dec_ref(v_indval_4571_);
lean_dec_ref(v_argNames_4570_);
lean_dec_ref(v___x_4569_);
v_a_4670_ = lean_ctor_get(v___x_4594_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4672_ = v___x_4594_;
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v___x_4594_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4675_; 
if (v_isShared_4673_ == 0)
{
v___x_4675_ = v___x_4672_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4670_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
}
}
else
{
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec_ref(v___x_4575_);
lean_dec(v_auxFunName_4573_);
lean_dec_ref(v___x_4572_);
lean_dec_ref(v_indval_4571_);
lean_dec_ref(v_argNames_4570_);
lean_dec_ref(v___x_4569_);
lean_dec_ref(v_ctx_4568_);
return v___x_4589_;
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4752_; 
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec_ref(v___x_4575_);
lean_dec(v_auxFunName_4573_);
lean_dec_ref(v___x_4572_);
lean_dec_ref(v_indval_4571_);
lean_dec_ref(v_argNames_4570_);
lean_dec_ref(v___x_4569_);
lean_dec_ref(v_ctx_4568_);
v_a_4745_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4747_ = v___x_4587_;
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4587_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
if (v_isShared_4748_ == 0)
{
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___boxed(lean_object** _args){
lean_object* v_targetType_4753_ = _args[0];
lean_object* v_ctx_4754_ = _args[1];
lean_object* v___x_4755_ = _args[2];
lean_object* v_argNames_4756_ = _args[3];
lean_object* v_indval_4757_ = _args[4];
lean_object* v___x_4758_ = _args[5];
lean_object* v_auxFunName_4759_ = _args[6];
lean_object* v_binders_4760_ = _args[7];
lean_object* v___x_4761_ = _args[8];
lean_object* v_usePartial_4762_ = _args[9];
lean_object* v_x_4763_ = _args[10];
lean_object* v___y_4764_ = _args[11];
lean_object* v___y_4765_ = _args[12];
lean_object* v___y_4766_ = _args[13];
lean_object* v___y_4767_ = _args[14];
lean_object* v___y_4768_ = _args[15];
lean_object* v___y_4769_ = _args[16];
lean_object* v___y_4770_ = _args[17];
_start:
{
uint8_t v_usePartial_boxed_4771_; lean_object* v_res_4772_; 
v_usePartial_boxed_4771_ = lean_unbox(v_usePartial_4762_);
v_res_4772_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0(v_targetType_4753_, v_ctx_4754_, v___x_4755_, v_argNames_4756_, v_indval_4757_, v___x_4758_, v_auxFunName_4759_, v_binders_4760_, v___x_4761_, v_usePartial_boxed_4771_, v_x_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
lean_dec_ref(v_x_4763_);
lean_dec_ref(v_binders_4760_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction(lean_object* v_ctx_4773_, lean_object* v_i_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_){
_start:
{
lean_object* v_typeInfos_4782_; lean_object* v_auxFunNames_4783_; uint8_t v_usePartial_4784_; lean_object* v___x_4785_; lean_object* v_indval_4786_; lean_object* v___x_4787_; 
v_typeInfos_4782_ = lean_ctor_get(v_ctx_4773_, 1);
v_auxFunNames_4783_ = lean_ctor_get(v_ctx_4773_, 2);
v_usePartial_4784_ = lean_ctor_get_uint8(v_ctx_4773_, sizeof(void*)*3);
v___x_4785_ = l_Lean_instInhabitedInductiveVal_default;
v_indval_4786_ = lean_array_get(v___x_4785_, v_typeInfos_4782_, v_i_4774_);
lean_inc(v_a_4780_);
lean_inc_ref(v_a_4779_);
lean_inc(v_a_4778_);
lean_inc_ref(v_a_4777_);
lean_inc(v_a_4776_);
lean_inc_ref(v_a_4775_);
lean_inc(v_indval_4786_);
v___x_4787_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader(v_indval_4786_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v_binders_4789_; lean_object* v_argNames_4790_; lean_object* v_targetType_4791_; lean_object* v___x_4792_; lean_object* v_auxFunName_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___f_4798_; lean_object* v___x_4799_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc(v_a_4788_);
lean_dec_ref(v___x_4787_);
v_binders_4789_ = lean_ctor_get(v_a_4788_, 0);
lean_inc_ref(v_binders_4789_);
v_argNames_4790_ = lean_ctor_get(v_a_4788_, 1);
lean_inc_ref(v_argNames_4790_);
v_targetType_4791_ = lean_ctor_get(v_a_4788_, 3);
lean_inc(v_targetType_4791_);
lean_dec(v_a_4788_);
v___x_4792_ = lean_box(0);
v_auxFunName_4793_ = lean_array_get(v___x_4792_, v_auxFunNames_4783_, v_i_4774_);
v___x_4794_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0));
v___x_4795_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2));
v___x_4796_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3));
v___x_4797_ = lean_box(v_usePartial_4784_);
lean_inc_ref(v_binders_4789_);
v___f_4798_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___boxed), 18, 10);
lean_closure_set(v___f_4798_, 0, v_targetType_4791_);
lean_closure_set(v___f_4798_, 1, v_ctx_4773_);
lean_closure_set(v___f_4798_, 2, v___x_4794_);
lean_closure_set(v___f_4798_, 3, v_argNames_4790_);
lean_closure_set(v___f_4798_, 4, v_indval_4786_);
lean_closure_set(v___f_4798_, 5, v___x_4795_);
lean_closure_set(v___f_4798_, 6, v_auxFunName_4793_);
lean_closure_set(v___f_4798_, 7, v_binders_4789_);
lean_closure_set(v___f_4798_, 8, v___x_4796_);
lean_closure_set(v___f_4798_, 9, v___x_4797_);
v___x_4799_ = l_Lean_Elab_Term_elabBinders___redArg(v_binders_4789_, v___f_4798_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_);
return v___x_4799_;
}
else
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
lean_dec(v_indval_4786_);
lean_dec(v_a_4780_);
lean_dec_ref(v_a_4779_);
lean_dec(v_a_4778_);
lean_dec_ref(v_a_4777_);
lean_dec(v_a_4776_);
lean_dec_ref(v_a_4775_);
lean_dec_ref(v_ctx_4773_);
v_a_4800_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4802_ = v___x_4787_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4787_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___boxed(lean_object* v_ctx_4808_, lean_object* v_i_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_){
_start:
{
lean_object* v_res_4817_; 
v_res_4817_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction(v_ctx_4808_, v_i_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_);
lean_dec(v_i_4809_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___redArg(lean_object* v_upperBound_4818_, lean_object* v_ctx_4819_, lean_object* v_a_4820_, lean_object* v_b_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
uint8_t v___x_4829_; 
v___x_4829_ = lean_nat_dec_lt(v_a_4820_, v_upperBound_4818_);
if (v___x_4829_ == 0)
{
lean_object* v___x_4830_; 
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
lean_dec(v_a_4820_);
lean_dec_ref(v_ctx_4819_);
v___x_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4830_, 0, v_b_4821_);
return v___x_4830_;
}
else
{
lean_object* v___x_4831_; 
lean_inc(v___y_4827_);
lean_inc_ref(v___y_4826_);
lean_inc(v___y_4825_);
lean_inc_ref(v___y_4824_);
lean_inc(v___y_4823_);
lean_inc_ref(v___y_4822_);
lean_inc_ref(v_ctx_4819_);
v___x_4831_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction(v_ctx_4819_, v_a_4820_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v_a_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
lean_inc(v_a_4832_);
lean_dec_ref(v___x_4831_);
v___x_4833_ = lean_array_push(v_b_4821_, v_a_4832_);
v___x_4834_ = lean_unsigned_to_nat(1u);
v___x_4835_ = lean_nat_add(v_a_4820_, v___x_4834_);
lean_dec(v_a_4820_);
v_a_4820_ = v___x_4835_;
v_b_4821_ = v___x_4833_;
goto _start;
}
else
{
lean_object* v_a_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4844_; 
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
lean_dec_ref(v_b_4821_);
lean_dec(v_a_4820_);
lean_dec_ref(v_ctx_4819_);
v_a_4837_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4839_ = v___x_4831_;
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_a_4837_);
lean_dec(v___x_4831_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4842_; 
if (v_isShared_4840_ == 0)
{
v___x_4842_ = v___x_4839_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_a_4837_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_4845_, lean_object* v_ctx_4846_, lean_object* v_a_4847_, lean_object* v_b_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_){
_start:
{
lean_object* v_res_4856_; 
v_res_4856_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___redArg(v_upperBound_4845_, v_ctx_4846_, v_a_4847_, v_b_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
lean_dec(v_upperBound_4845_);
return v_res_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock(lean_object* v_ctx_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_){
_start:
{
lean_object* v_typeInfos_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v_auxDefs_4875_; lean_object* v___x_4876_; 
v_typeInfos_4872_ = lean_ctor_get(v_ctx_4864_, 1);
v___x_4873_ = lean_array_get_size(v_typeInfos_4872_);
v___x_4874_ = lean_unsigned_to_nat(0u);
v_auxDefs_4875_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___closed__0));
lean_inc_ref(v_a_4869_);
v___x_4876_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___redArg(v___x_4873_, v_ctx_4864_, v___x_4874_, v_auxDefs_4875_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4897_; 
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4879_ = v___x_4876_;
v_isShared_4880_ = v_isSharedCheck_4897_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4876_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4897_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v_ref_4881_; uint8_t v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4895_; 
v_ref_4881_ = lean_ctor_get(v_a_4869_, 5);
lean_inc(v_ref_4881_);
lean_dec_ref(v_a_4869_);
v___x_4882_ = 0;
v___x_4883_ = l_Lean_SourceInfo_fromRef(v_ref_4881_, v___x_4882_);
lean_dec(v_ref_4881_);
v___x_4884_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__0));
v___x_4885_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1));
lean_inc(v___x_4883_);
v___x_4886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4883_);
lean_ctor_set(v___x_4886_, 1, v___x_4884_);
v___x_4887_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_4888_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v___x_4889_ = l_Array_append___redArg(v___x_4888_, v_a_4877_);
lean_dec(v_a_4877_);
lean_inc(v___x_4883_);
v___x_4890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4883_);
lean_ctor_set(v___x_4890_, 1, v___x_4887_);
lean_ctor_set(v___x_4890_, 2, v___x_4889_);
v___x_4891_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__2));
lean_inc(v___x_4883_);
v___x_4892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4892_, 0, v___x_4883_);
lean_ctor_set(v___x_4892_, 1, v___x_4891_);
v___x_4893_ = l_Lean_Syntax_node3(v___x_4883_, v___x_4885_, v___x_4886_, v___x_4890_, v___x_4892_);
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 0, v___x_4893_);
v___x_4895_ = v___x_4879_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
else
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4905_; 
lean_dec_ref(v_a_4869_);
v_a_4898_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4900_ = v___x_4876_;
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4876_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4903_; 
if (v_isShared_4901_ == 0)
{
v___x_4903_ = v___x_4900_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_a_4898_);
v___x_4903_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
return v___x_4903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___boxed(lean_object* v_ctx_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock(v_ctx_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0(lean_object* v_upperBound_4915_, lean_object* v_ctx_4916_, lean_object* v_inst_4917_, lean_object* v_R_4918_, lean_object* v_a_4919_, lean_object* v_b_4920_, lean_object* v_c_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_){
_start:
{
lean_object* v___x_4929_; 
v___x_4929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___redArg(v_upperBound_4915_, v_ctx_4916_, v_a_4919_, v_b_4920_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_);
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___boxed(lean_object* v_upperBound_4930_, lean_object* v_ctx_4931_, lean_object* v_inst_4932_, lean_object* v_R_4933_, lean_object* v_a_4934_, lean_object* v_b_4935_, lean_object* v_c_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_){
_start:
{
lean_object* v_res_4944_; 
v_res_4944_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0(v_upperBound_4930_, v_ctx_4931_, v_inst_4932_, v_R_4933_, v_a_4934_, v_b_4935_, v_c_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
lean_dec(v_upperBound_4930_);
return v_res_4944_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___redArg(lean_object* v_upperBound_4945_, lean_object* v_ctx_4946_, lean_object* v_a_4947_, lean_object* v_b_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
uint8_t v___x_4956_; 
v___x_4956_ = lean_nat_dec_lt(v_a_4947_, v_upperBound_4945_);
if (v___x_4956_ == 0)
{
lean_object* v___x_4957_; 
lean_dec(v___y_4954_);
lean_dec_ref(v___y_4953_);
lean_dec(v___y_4952_);
lean_dec_ref(v___y_4951_);
lean_dec(v___y_4950_);
lean_dec_ref(v___y_4949_);
lean_dec(v_a_4947_);
lean_dec_ref(v_ctx_4946_);
v___x_4957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4957_, 0, v_b_4948_);
return v___x_4957_;
}
else
{
lean_object* v___x_4958_; 
lean_inc(v___y_4954_);
lean_inc_ref(v___y_4953_);
lean_inc(v___y_4952_);
lean_inc_ref(v___y_4951_);
lean_inc(v___y_4950_);
lean_inc_ref(v___y_4949_);
lean_inc_ref(v_ctx_4946_);
v___x_4958_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction(v_ctx_4946_, v_a_4947_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4959_);
lean_dec_ref(v___x_4958_);
v___x_4960_ = lean_array_push(v_b_4948_, v_a_4959_);
v___x_4961_ = lean_unsigned_to_nat(1u);
v___x_4962_ = lean_nat_add(v_a_4947_, v___x_4961_);
lean_dec(v_a_4947_);
v_a_4947_ = v___x_4962_;
v_b_4948_ = v___x_4960_;
goto _start;
}
else
{
lean_object* v_a_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_4971_; 
lean_dec(v___y_4954_);
lean_dec_ref(v___y_4953_);
lean_dec(v___y_4952_);
lean_dec_ref(v___y_4951_);
lean_dec(v___y_4950_);
lean_dec_ref(v___y_4949_);
lean_dec_ref(v_b_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_ctx_4946_);
v_a_4964_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4966_ = v___x_4958_;
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_a_4964_);
lean_dec(v___x_4958_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4969_; 
if (v_isShared_4967_ == 0)
{
v___x_4969_ = v___x_4966_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4964_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
return v___x_4969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_4972_, lean_object* v_ctx_4973_, lean_object* v_a_4974_, lean_object* v_b_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___redArg(v_upperBound_4972_, v_ctx_4973_, v_a_4974_, v_b_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
lean_dec(v_upperBound_4972_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock(lean_object* v_ctx_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_){
_start:
{
lean_object* v_typeInfos_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v_auxDefs_4995_; lean_object* v___x_4996_; 
v_typeInfos_4992_ = lean_ctor_get(v_ctx_4984_, 1);
v___x_4993_ = lean_array_get_size(v_typeInfos_4992_);
v___x_4994_ = lean_unsigned_to_nat(0u);
v_auxDefs_4995_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___closed__0));
lean_inc_ref(v_a_4989_);
v___x_4996_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___redArg(v___x_4993_, v_ctx_4984_, v___x_4994_, v_auxDefs_4995_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_);
if (lean_obj_tag(v___x_4996_) == 0)
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5017_; 
v_a_4997_ = lean_ctor_get(v___x_4996_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_4996_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_4999_ = v___x_4996_;
v_isShared_5000_ = v_isSharedCheck_5017_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v___x_4996_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5017_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v_ref_5001_; uint8_t v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5015_; 
v_ref_5001_ = lean_ctor_get(v_a_4989_, 5);
lean_inc(v_ref_5001_);
lean_dec_ref(v_a_4989_);
v___x_5002_ = 0;
v___x_5003_ = l_Lean_SourceInfo_fromRef(v_ref_5001_, v___x_5002_);
lean_dec(v_ref_5001_);
v___x_5004_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__0));
v___x_5005_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1));
lean_inc(v___x_5003_);
v___x_5006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5003_);
lean_ctor_set(v___x_5006_, 1, v___x_5004_);
v___x_5007_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_5008_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v___x_5009_ = l_Array_append___redArg(v___x_5008_, v_a_4997_);
lean_dec(v_a_4997_);
lean_inc(v___x_5003_);
v___x_5010_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5003_);
lean_ctor_set(v___x_5010_, 1, v___x_5007_);
lean_ctor_set(v___x_5010_, 2, v___x_5009_);
v___x_5011_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__2));
lean_inc(v___x_5003_);
v___x_5012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5003_);
lean_ctor_set(v___x_5012_, 1, v___x_5011_);
v___x_5013_ = l_Lean_Syntax_node3(v___x_5003_, v___x_5005_, v___x_5006_, v___x_5010_, v___x_5012_);
if (v_isShared_5000_ == 0)
{
lean_ctor_set(v___x_4999_, 0, v___x_5013_);
v___x_5015_ = v___x_4999_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5013_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
lean_dec_ref(v_a_4989_);
v_a_5018_ = lean_ctor_get(v___x_4996_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_4996_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_4996_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_4996_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock___boxed(lean_object* v_ctx_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_){
_start:
{
lean_object* v_res_5034_; 
v_res_5034_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock(v_ctx_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
return v_res_5034_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0(lean_object* v_upperBound_5035_, lean_object* v_ctx_5036_, lean_object* v_inst_5037_, lean_object* v_R_5038_, lean_object* v_a_5039_, lean_object* v_b_5040_, lean_object* v_c_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_){
_start:
{
lean_object* v___x_5049_; 
v___x_5049_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___redArg(v_upperBound_5035_, v_ctx_5036_, v_a_5039_, v_b_5040_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___boxed(lean_object* v_upperBound_5050_, lean_object* v_ctx_5051_, lean_object* v_inst_5052_, lean_object* v_R_5053_, lean_object* v_a_5054_, lean_object* v_b_5055_, lean_object* v_c_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_){
_start:
{
lean_object* v_res_5064_; 
v_res_5064_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0(v_upperBound_5050_, v_ctx_5051_, v_inst_5052_, v_R_5053_, v_a_5054_, v_b_5055_, v_c_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_);
lean_dec(v_upperBound_5050_);
return v_res_5064_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg(lean_object* v_cls_5068_, lean_object* v___y_5069_){
_start:
{
lean_object* v_options_5071_; uint8_t v_hasTrace_5072_; 
v_options_5071_ = lean_ctor_get(v___y_5069_, 2);
v_hasTrace_5072_ = lean_ctor_get_uint8(v_options_5071_, sizeof(void*)*1);
if (v_hasTrace_5072_ == 0)
{
lean_object* v___x_5073_; lean_object* v___x_5074_; 
lean_dec(v_cls_5068_);
v___x_5073_ = lean_box(v_hasTrace_5072_);
v___x_5074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5074_, 0, v___x_5073_);
return v___x_5074_;
}
else
{
lean_object* v_inheritedTraceOptions_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; uint8_t v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; 
v_inheritedTraceOptions_5075_ = lean_ctor_get(v___y_5069_, 13);
v___x_5076_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg___closed__1));
v___x_5077_ = l_Lean_Name_append(v___x_5076_, v_cls_5068_);
v___x_5078_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5075_, v_options_5071_, v___x_5077_);
lean_dec(v___x_5077_);
v___x_5079_ = lean_box(v___x_5078_);
v___x_5080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5080_, 0, v___x_5079_);
return v___x_5080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg___boxed(lean_object* v_cls_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_){
_start:
{
lean_object* v_res_5084_; 
v_res_5084_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg(v_cls_5081_, v___y_5082_);
lean_dec_ref(v___y_5082_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0(lean_object* v_cls_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_){
_start:
{
lean_object* v___x_5093_; 
v___x_5093_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg(v_cls_5085_, v___y_5090_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___boxed(lean_object* v_cls_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0(v_cls_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
lean_dec(v___y_5100_);
lean_dec_ref(v___y_5099_);
lean_dec(v___y_5098_);
lean_dec_ref(v___y_5097_);
lean_dec(v___y_5096_);
lean_dec_ref(v___y_5095_);
return v_res_5102_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_5103_; double v___x_5104_; 
v___x_5103_ = lean_unsigned_to_nat(0u);
v___x_5104_ = lean_float_of_nat(v___x_5103_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg(lean_object* v_cls_5107_, lean_object* v_msg_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_){
_start:
{
lean_object* v_ref_5114_; lean_object* v___x_5115_; lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5160_; 
v_ref_5114_ = lean_ctor_get(v___y_5111_, 5);
v___x_5115_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__2(v_msg_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
v_a_5116_ = lean_ctor_get(v___x_5115_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5115_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5118_ = v___x_5115_;
v_isShared_5119_ = v_isSharedCheck_5160_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5115_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5160_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5120_; lean_object* v_traceState_5121_; lean_object* v_env_5122_; lean_object* v_nextMacroScope_5123_; lean_object* v_ngen_5124_; lean_object* v_auxDeclNGen_5125_; lean_object* v_cache_5126_; lean_object* v_messages_5127_; lean_object* v_infoState_5128_; lean_object* v_snapshotTasks_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5159_; 
v___x_5120_ = lean_st_ref_take(v___y_5112_);
v_traceState_5121_ = lean_ctor_get(v___x_5120_, 4);
v_env_5122_ = lean_ctor_get(v___x_5120_, 0);
v_nextMacroScope_5123_ = lean_ctor_get(v___x_5120_, 1);
v_ngen_5124_ = lean_ctor_get(v___x_5120_, 2);
v_auxDeclNGen_5125_ = lean_ctor_get(v___x_5120_, 3);
v_cache_5126_ = lean_ctor_get(v___x_5120_, 5);
v_messages_5127_ = lean_ctor_get(v___x_5120_, 6);
v_infoState_5128_ = lean_ctor_get(v___x_5120_, 7);
v_snapshotTasks_5129_ = lean_ctor_get(v___x_5120_, 8);
v_isSharedCheck_5159_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5159_ == 0)
{
v___x_5131_ = v___x_5120_;
v_isShared_5132_ = v_isSharedCheck_5159_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_snapshotTasks_5129_);
lean_inc(v_infoState_5128_);
lean_inc(v_messages_5127_);
lean_inc(v_cache_5126_);
lean_inc(v_traceState_5121_);
lean_inc(v_auxDeclNGen_5125_);
lean_inc(v_ngen_5124_);
lean_inc(v_nextMacroScope_5123_);
lean_inc(v_env_5122_);
lean_dec(v___x_5120_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5159_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
uint64_t v_tid_5133_; lean_object* v_traces_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5158_; 
v_tid_5133_ = lean_ctor_get_uint64(v_traceState_5121_, sizeof(void*)*1);
v_traces_5134_ = lean_ctor_get(v_traceState_5121_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v_traceState_5121_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5136_ = v_traceState_5121_;
v_isShared_5137_ = v_isSharedCheck_5158_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_traces_5134_);
lean_dec(v_traceState_5121_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5158_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5138_; double v___x_5139_; uint8_t v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5148_; 
v___x_5138_ = lean_box(0);
v___x_5139_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__0);
v___x_5140_ = 0;
v___x_5141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__9));
v___x_5142_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5142_, 0, v_cls_5107_);
lean_ctor_set(v___x_5142_, 1, v___x_5138_);
lean_ctor_set(v___x_5142_, 2, v___x_5141_);
lean_ctor_set_float(v___x_5142_, sizeof(void*)*3, v___x_5139_);
lean_ctor_set_float(v___x_5142_, sizeof(void*)*3 + 8, v___x_5139_);
lean_ctor_set_uint8(v___x_5142_, sizeof(void*)*3 + 16, v___x_5140_);
v___x_5143_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__1));
v___x_5144_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5144_, 0, v___x_5142_);
lean_ctor_set(v___x_5144_, 1, v_a_5116_);
lean_ctor_set(v___x_5144_, 2, v___x_5143_);
lean_inc(v_ref_5114_);
v___x_5145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5145_, 0, v_ref_5114_);
lean_ctor_set(v___x_5145_, 1, v___x_5144_);
v___x_5146_ = l_Lean_PersistentArray_push___redArg(v_traces_5134_, v___x_5145_);
if (v_isShared_5137_ == 0)
{
lean_ctor_set(v___x_5136_, 0, v___x_5146_);
v___x_5148_ = v___x_5136_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v___x_5146_);
lean_ctor_set_uint64(v_reuseFailAlloc_5157_, sizeof(void*)*1, v_tid_5133_);
v___x_5148_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
lean_object* v___x_5150_; 
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 4, v___x_5148_);
v___x_5150_ = v___x_5131_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v_env_5122_);
lean_ctor_set(v_reuseFailAlloc_5156_, 1, v_nextMacroScope_5123_);
lean_ctor_set(v_reuseFailAlloc_5156_, 2, v_ngen_5124_);
lean_ctor_set(v_reuseFailAlloc_5156_, 3, v_auxDeclNGen_5125_);
lean_ctor_set(v_reuseFailAlloc_5156_, 4, v___x_5148_);
lean_ctor_set(v_reuseFailAlloc_5156_, 5, v_cache_5126_);
lean_ctor_set(v_reuseFailAlloc_5156_, 6, v_messages_5127_);
lean_ctor_set(v_reuseFailAlloc_5156_, 7, v_infoState_5128_);
lean_ctor_set(v_reuseFailAlloc_5156_, 8, v_snapshotTasks_5129_);
v___x_5150_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5154_; 
v___x_5151_ = lean_st_ref_set(v___y_5112_, v___x_5150_);
v___x_5152_ = lean_box(0);
if (v_isShared_5119_ == 0)
{
lean_ctor_set(v___x_5118_, 0, v___x_5152_);
v___x_5154_ = v___x_5118_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v___x_5152_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___boxed(lean_object* v_cls_5161_, lean_object* v_msg_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_){
_start:
{
lean_object* v_res_5168_; 
v_res_5168_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg(v_cls_5161_, v_msg_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
lean_dec(v___y_5166_);
lean_dec_ref(v___y_5165_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__1(lean_object* v_a_5169_, lean_object* v_a_5170_){
_start:
{
if (lean_obj_tag(v_a_5169_) == 0)
{
lean_object* v___x_5171_; 
v___x_5171_ = l_List_reverse___redArg(v_a_5170_);
return v___x_5171_;
}
else
{
lean_object* v_head_5172_; lean_object* v_tail_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5182_; 
v_head_5172_ = lean_ctor_get(v_a_5169_, 0);
v_tail_5173_ = lean_ctor_get(v_a_5169_, 1);
v_isSharedCheck_5182_ = !lean_is_exclusive(v_a_5169_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5175_ = v_a_5169_;
v_isShared_5176_ = v_isSharedCheck_5182_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_tail_5173_);
lean_inc(v_head_5172_);
lean_dec(v_a_5169_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5182_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5177_; lean_object* v___x_5179_; 
v___x_5177_ = l_Lean_MessageData_ofSyntax(v_head_5172_);
if (v_isShared_5176_ == 0)
{
lean_ctor_set(v___x_5175_, 1, v_a_5170_);
lean_ctor_set(v___x_5175_, 0, v___x_5177_);
v___x_5179_ = v___x_5175_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v___x_5177_);
lean_ctor_set(v_reuseFailAlloc_5181_, 1, v_a_5170_);
v___x_5179_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
v_a_5169_ = v_tail_5173_;
v_a_5170_ = v___x_5179_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2(void){
_start:
{
lean_object* v___x_5188_; lean_object* v___x_5189_; 
v___x_5188_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__1));
v___x_5189_ = l_Lean_stringToMessageData(v___x_5188_);
return v___x_5189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance(lean_object* v_declName_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_){
_start:
{
lean_object* v___x_5198_; lean_object* v___x_5199_; uint8_t v___x_5200_; lean_object* v___x_5201_; 
v___x_5198_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__2));
v___x_5199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__32));
v___x_5200_ = 1;
lean_inc(v_a_5196_);
lean_inc_ref(v_a_5195_);
lean_inc(v_a_5194_);
lean_inc_ref(v_a_5193_);
lean_inc(v_a_5192_);
lean_inc_ref(v_a_5191_);
lean_inc(v_declName_5190_);
v___x_5201_ = l_Lean_Elab_Deriving_mkContext(v___x_5198_, v___x_5199_, v_declName_5190_, v___x_5200_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v_a_5202_; lean_object* v___x_5203_; 
v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
lean_inc(v_a_5202_);
lean_dec_ref(v___x_5201_);
lean_inc(v_a_5196_);
lean_inc_ref(v_a_5195_);
lean_inc(v_a_5194_);
lean_inc_ref(v_a_5193_);
lean_inc(v_a_5192_);
lean_inc_ref(v_a_5191_);
lean_inc(v_a_5202_);
v___x_5203_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock(v_a_5202_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
if (lean_obj_tag(v___x_5203_) == 0)
{
lean_object* v_a_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
v_a_5204_ = lean_ctor_get(v___x_5203_, 0);
lean_inc(v_a_5204_);
lean_dec_ref(v___x_5203_);
v___x_5205_ = lean_unsigned_to_nat(1u);
v___x_5206_ = lean_mk_empty_array_with_capacity(v___x_5205_);
lean_inc_ref(v___x_5206_);
v___x_5207_ = lean_array_push(v___x_5206_, v_declName_5190_);
lean_inc(v_a_5196_);
lean_inc_ref(v_a_5195_);
lean_inc(v_a_5194_);
lean_inc_ref(v_a_5193_);
v___x_5208_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_5202_, v___x_5198_, v___x_5207_, v___x_5200_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
lean_dec_ref(v___x_5207_);
if (lean_obj_tag(v___x_5208_) == 0)
{
lean_object* v_a_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5245_; 
v_a_5209_ = lean_ctor_get(v___x_5208_, 0);
lean_inc(v_a_5209_);
lean_dec_ref(v___x_5208_);
v___x_5210_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__0));
v___x_5211_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg(v___x_5210_, v_a_5195_);
v_a_5212_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5214_ = v___x_5211_;
v_isShared_5215_ = v_isSharedCheck_5245_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v___x_5211_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5245_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v___x_5216_; lean_object* v___x_5217_; uint8_t v___x_5218_; 
v___x_5216_ = lean_array_push(v___x_5206_, v_a_5204_);
v___x_5217_ = l_Array_append___redArg(v___x_5216_, v_a_5209_);
lean_dec(v_a_5209_);
v___x_5218_ = lean_unbox(v_a_5212_);
lean_dec(v_a_5212_);
if (v___x_5218_ == 0)
{
lean_object* v___x_5220_; 
lean_dec(v_a_5196_);
lean_dec_ref(v_a_5195_);
lean_dec(v_a_5194_);
lean_dec_ref(v_a_5193_);
if (v_isShared_5215_ == 0)
{
lean_ctor_set(v___x_5214_, 0, v___x_5217_);
v___x_5220_ = v___x_5214_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v___x_5217_);
v___x_5220_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
return v___x_5220_;
}
}
else
{
lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; 
lean_del_object(v___x_5214_);
v___x_5222_ = lean_obj_once(&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2, &l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2_once, _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2);
lean_inc_ref(v___x_5217_);
v___x_5223_ = lean_array_to_list(v___x_5217_);
v___x_5224_ = lean_box(0);
v___x_5225_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__1(v___x_5223_, v___x_5224_);
v___x_5226_ = l_Lean_MessageData_ofList(v___x_5225_);
v___x_5227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5222_);
lean_ctor_set(v___x_5227_, 1, v___x_5226_);
v___x_5228_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg(v___x_5210_, v___x_5227_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
lean_dec(v_a_5196_);
lean_dec_ref(v_a_5195_);
lean_dec(v_a_5194_);
lean_dec_ref(v_a_5193_);
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5235_ == 0)
{
lean_object* v_unused_5236_; 
v_unused_5236_ = lean_ctor_get(v___x_5228_, 0);
lean_dec(v_unused_5236_);
v___x_5230_ = v___x_5228_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_dec(v___x_5228_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5233_; 
if (v_isShared_5231_ == 0)
{
lean_ctor_set(v___x_5230_, 0, v___x_5217_);
v___x_5233_ = v___x_5230_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v___x_5217_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
else
{
lean_object* v_a_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5244_; 
lean_dec_ref(v___x_5217_);
v_a_5237_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5239_ = v___x_5228_;
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_a_5237_);
lean_dec(v___x_5228_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v___x_5242_; 
if (v_isShared_5240_ == 0)
{
v___x_5242_ = v___x_5239_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v_a_5237_);
v___x_5242_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
return v___x_5242_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_5206_);
lean_dec(v_a_5204_);
lean_dec(v_a_5196_);
lean_dec_ref(v_a_5195_);
lean_dec(v_a_5194_);
lean_dec_ref(v_a_5193_);
return v___x_5208_;
}
}
else
{
lean_object* v_a_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5253_; 
lean_dec(v_a_5202_);
lean_dec(v_a_5196_);
lean_dec_ref(v_a_5195_);
lean_dec(v_a_5194_);
lean_dec_ref(v_a_5193_);
lean_dec(v_a_5192_);
lean_dec_ref(v_a_5191_);
lean_dec(v_declName_5190_);
v_a_5246_ = lean_ctor_get(v___x_5203_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5203_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5248_ = v___x_5203_;
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_a_5246_);
lean_dec(v___x_5203_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v___x_5251_; 
if (v_isShared_5249_ == 0)
{
v___x_5251_ = v___x_5248_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_a_5246_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
}
else
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5261_; 
lean_dec(v_a_5196_);
lean_dec_ref(v_a_5195_);
lean_dec(v_a_5194_);
lean_dec_ref(v_a_5193_);
lean_dec(v_a_5192_);
lean_dec_ref(v_a_5191_);
lean_dec(v_declName_5190_);
v_a_5254_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5261_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5261_ == 0)
{
v___x_5256_ = v___x_5201_;
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5201_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5259_; 
if (v_isShared_5257_ == 0)
{
v___x_5259_ = v___x_5256_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_a_5254_);
v___x_5259_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
return v___x_5259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___boxed(lean_object* v_declName_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_){
_start:
{
lean_object* v_res_5270_; 
v_res_5270_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance(v_declName_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_);
return v_res_5270_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2(lean_object* v_cls_5271_, lean_object* v_msg_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_){
_start:
{
lean_object* v___x_5280_; 
v___x_5280_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg(v_cls_5271_, v_msg_5272_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_);
return v___x_5280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___boxed(lean_object* v_cls_5281_, lean_object* v_msg_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_){
_start:
{
lean_object* v_res_5290_; 
v_res_5290_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2(v_cls_5281_, v_msg_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
return v_res_5290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance(lean_object* v_declName_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_){
_start:
{
lean_object* v___x_5304_; lean_object* v___x_5305_; uint8_t v___x_5306_; lean_object* v___x_5307_; 
v___x_5304_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__1));
v___x_5305_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__0));
v___x_5306_ = 1;
lean_inc(v_a_5302_);
lean_inc_ref(v_a_5301_);
lean_inc(v_a_5300_);
lean_inc_ref(v_a_5299_);
lean_inc(v_a_5298_);
lean_inc_ref(v_a_5297_);
lean_inc(v_declName_5296_);
v___x_5307_ = l_Lean_Elab_Deriving_mkContext(v___x_5304_, v___x_5305_, v_declName_5296_, v___x_5306_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v___x_5309_; 
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
lean_inc(v_a_5308_);
lean_dec_ref(v___x_5307_);
lean_inc(v_a_5302_);
lean_inc_ref(v_a_5301_);
lean_inc(v_a_5300_);
lean_inc_ref(v_a_5299_);
lean_inc(v_a_5298_);
lean_inc_ref(v_a_5297_);
lean_inc(v_a_5308_);
v___x_5309_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock(v_a_5308_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_);
if (lean_obj_tag(v___x_5309_) == 0)
{
lean_object* v_a_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; 
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
lean_inc(v_a_5310_);
lean_dec_ref(v___x_5309_);
v___x_5311_ = lean_unsigned_to_nat(1u);
v___x_5312_ = lean_mk_empty_array_with_capacity(v___x_5311_);
lean_inc_ref(v___x_5312_);
v___x_5313_ = lean_array_push(v___x_5312_, v_declName_5296_);
lean_inc(v_a_5302_);
lean_inc_ref(v_a_5301_);
lean_inc(v_a_5300_);
lean_inc_ref(v_a_5299_);
v___x_5314_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_5308_, v___x_5304_, v___x_5313_, v___x_5306_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_);
lean_dec_ref(v___x_5313_);
if (lean_obj_tag(v___x_5314_) == 0)
{
lean_object* v_a_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5351_; 
v_a_5315_ = lean_ctor_get(v___x_5314_, 0);
lean_inc(v_a_5315_);
lean_dec_ref(v___x_5314_);
v___x_5316_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__1));
v___x_5317_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg(v___x_5316_, v_a_5301_);
v_a_5318_ = lean_ctor_get(v___x_5317_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5320_ = v___x_5317_;
v_isShared_5321_ = v_isSharedCheck_5351_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v___x_5317_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5351_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5322_; lean_object* v___x_5323_; uint8_t v___x_5324_; 
v___x_5322_ = lean_array_push(v___x_5312_, v_a_5310_);
v___x_5323_ = l_Array_append___redArg(v___x_5322_, v_a_5315_);
lean_dec(v_a_5315_);
v___x_5324_ = lean_unbox(v_a_5318_);
lean_dec(v_a_5318_);
if (v___x_5324_ == 0)
{
lean_object* v___x_5326_; 
lean_dec(v_a_5302_);
lean_dec_ref(v_a_5301_);
lean_dec(v_a_5300_);
lean_dec_ref(v_a_5299_);
if (v_isShared_5321_ == 0)
{
lean_ctor_set(v___x_5320_, 0, v___x_5323_);
v___x_5326_ = v___x_5320_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5323_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
else
{
lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; 
lean_del_object(v___x_5320_);
v___x_5328_ = lean_obj_once(&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2, &l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2_once, _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2);
lean_inc_ref(v___x_5323_);
v___x_5329_ = lean_array_to_list(v___x_5323_);
v___x_5330_ = lean_box(0);
v___x_5331_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__1(v___x_5329_, v___x_5330_);
v___x_5332_ = l_Lean_MessageData_ofList(v___x_5331_);
v___x_5333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5333_, 0, v___x_5328_);
lean_ctor_set(v___x_5333_, 1, v___x_5332_);
v___x_5334_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg(v___x_5316_, v___x_5333_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_);
lean_dec(v_a_5302_);
lean_dec_ref(v_a_5301_);
lean_dec(v_a_5300_);
lean_dec_ref(v_a_5299_);
if (lean_obj_tag(v___x_5334_) == 0)
{
lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5341_; 
v_isSharedCheck_5341_ = !lean_is_exclusive(v___x_5334_);
if (v_isSharedCheck_5341_ == 0)
{
lean_object* v_unused_5342_; 
v_unused_5342_ = lean_ctor_get(v___x_5334_, 0);
lean_dec(v_unused_5342_);
v___x_5336_ = v___x_5334_;
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
else
{
lean_dec(v___x_5334_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
lean_object* v___x_5339_; 
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 0, v___x_5323_);
v___x_5339_ = v___x_5336_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v___x_5323_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
return v___x_5339_;
}
}
}
else
{
lean_object* v_a_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5350_; 
lean_dec_ref(v___x_5323_);
v_a_5343_ = lean_ctor_get(v___x_5334_, 0);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5334_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5345_ = v___x_5334_;
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_a_5343_);
lean_dec(v___x_5334_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v___x_5348_; 
if (v_isShared_5346_ == 0)
{
v___x_5348_ = v___x_5345_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_a_5343_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_5312_);
lean_dec(v_a_5310_);
lean_dec(v_a_5302_);
lean_dec_ref(v_a_5301_);
lean_dec(v_a_5300_);
lean_dec_ref(v_a_5299_);
return v___x_5314_;
}
}
else
{
lean_object* v_a_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5359_; 
lean_dec(v_a_5308_);
lean_dec(v_a_5302_);
lean_dec_ref(v_a_5301_);
lean_dec(v_a_5300_);
lean_dec_ref(v_a_5299_);
lean_dec(v_a_5298_);
lean_dec_ref(v_a_5297_);
lean_dec(v_declName_5296_);
v_a_5352_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5359_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5354_ = v___x_5309_;
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_a_5352_);
lean_dec(v___x_5309_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5357_; 
if (v_isShared_5355_ == 0)
{
v___x_5357_ = v___x_5354_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v_a_5352_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
lean_dec(v_a_5302_);
lean_dec_ref(v_a_5301_);
lean_dec(v_a_5300_);
lean_dec_ref(v_a_5299_);
lean_dec(v_a_5298_);
lean_dec_ref(v_a_5297_);
lean_dec(v_declName_5296_);
v_a_5360_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5307_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5307_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5363_ == 0)
{
v___x_5365_ = v___x_5362_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___boxed(lean_object* v_declName_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance(v_declName_5368_, v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___redArg(lean_object* v_declName_5377_, lean_object* v___y_5378_){
_start:
{
lean_object* v___x_5380_; lean_object* v_env_5381_; uint8_t v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; 
v___x_5380_ = lean_st_ref_get(v___y_5378_);
v_env_5381_ = lean_ctor_get(v___x_5380_, 0);
lean_inc_ref(v_env_5381_);
lean_dec(v___x_5380_);
v___x_5382_ = l_Lean_isInductiveCore(v_env_5381_, v_declName_5377_);
v___x_5383_ = lean_box(v___x_5382_);
v___x_5384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5384_, 0, v___x_5383_);
return v___x_5384_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_){
_start:
{
lean_object* v_res_5388_; 
v_res_5388_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___redArg(v_declName_5385_, v___y_5386_);
lean_dec(v___y_5386_);
return v_res_5388_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0(lean_object* v_declName_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_){
_start:
{
lean_object* v___x_5393_; 
v___x_5393_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___redArg(v_declName_5389_, v___y_5391_);
return v___x_5393_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___boxed(lean_object* v_declName_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_){
_start:
{
lean_object* v_res_5398_; 
v_res_5398_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0(v_declName_5394_, v___y_5395_, v___y_5396_);
lean_dec(v___y_5396_);
lean_dec_ref(v___y_5395_);
return v_res_5398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(uint8_t v_____do__lift_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_){
_start:
{
if (v_____do__lift_5399_ == 0)
{
uint8_t v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; 
v___x_5403_ = 1;
v___x_5404_ = lean_box(v___x_5403_);
v___x_5405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5405_, 0, v___x_5404_);
return v___x_5405_;
}
else
{
uint8_t v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; 
v___x_5406_ = 0;
v___x_5407_ = lean_box(v___x_5406_);
v___x_5408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5408_, 0, v___x_5407_);
return v___x_5408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_){
_start:
{
uint8_t v_____do__lift_2982__boxed_5413_; lean_object* v_res_5414_; 
v_____do__lift_2982__boxed_5413_ = lean_unbox(v_____do__lift_5409_);
v_res_5414_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(v_____do__lift_2982__boxed_5413_, v___y_5410_, v___y_5411_);
lean_dec(v___y_5411_);
lean_dec_ref(v___y_5410_);
return v_res_5414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__3(lean_object* v_as_5415_, size_t v_i_5416_, size_t v_stop_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_){
_start:
{
uint8_t v___x_5421_; 
v___x_5421_ = lean_usize_dec_eq(v_i_5416_, v_stop_5417_);
if (v___x_5421_ == 0)
{
uint8_t v___x_5422_; uint8_t v_a_5424_; lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5422_ = 1;
v___x_5430_ = lean_array_uget_borrowed(v_as_5415_, v_i_5416_);
lean_inc(v___x_5430_);
v___x_5431_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___redArg(v___x_5430_, v___y_5419_);
if (lean_obj_tag(v___x_5431_) == 0)
{
lean_object* v_a_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5441_; 
v_a_5432_ = lean_ctor_get(v___x_5431_, 0);
v_isSharedCheck_5441_ = !lean_is_exclusive(v___x_5431_);
if (v_isSharedCheck_5441_ == 0)
{
v___x_5434_ = v___x_5431_;
v_isShared_5435_ = v_isSharedCheck_5441_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_a_5432_);
lean_dec(v___x_5431_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5441_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
uint8_t v___x_5436_; 
v___x_5436_ = lean_unbox(v_a_5432_);
lean_dec(v_a_5432_);
if (v___x_5436_ == 0)
{
lean_object* v___x_5437_; lean_object* v___x_5439_; 
v___x_5437_ = lean_box(v___x_5422_);
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 0, v___x_5437_);
v___x_5439_ = v___x_5434_;
goto v_reusejp_5438_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v___x_5437_);
v___x_5439_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5438_;
}
v_reusejp_5438_:
{
return v___x_5439_;
}
}
else
{
lean_del_object(v___x_5434_);
v_a_5424_ = v___x_5421_;
goto v___jp_5423_;
}
}
}
else
{
if (lean_obj_tag(v___x_5431_) == 0)
{
lean_object* v_a_5442_; uint8_t v___x_5443_; 
v_a_5442_ = lean_ctor_get(v___x_5431_, 0);
lean_inc(v_a_5442_);
lean_dec_ref(v___x_5431_);
v___x_5443_ = lean_unbox(v_a_5442_);
lean_dec(v_a_5442_);
v_a_5424_ = v___x_5443_;
goto v___jp_5423_;
}
else
{
return v___x_5431_;
}
}
v___jp_5423_:
{
if (v_a_5424_ == 0)
{
size_t v___x_5425_; size_t v___x_5426_; 
v___x_5425_ = ((size_t)1ULL);
v___x_5426_ = lean_usize_add(v_i_5416_, v___x_5425_);
v_i_5416_ = v___x_5426_;
goto _start;
}
else
{
lean_object* v___x_5428_; lean_object* v___x_5429_; 
v___x_5428_ = lean_box(v___x_5422_);
v___x_5429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5429_, 0, v___x_5428_);
return v___x_5429_;
}
}
}
else
{
uint8_t v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
v___x_5444_ = 0;
v___x_5445_ = lean_box(v___x_5444_);
v___x_5446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5446_, 0, v___x_5445_);
return v___x_5446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__3___boxed(lean_object* v_as_5447_, lean_object* v_i_5448_, lean_object* v_stop_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_){
_start:
{
size_t v_i_boxed_5453_; size_t v_stop_boxed_5454_; lean_object* v_res_5455_; 
v_i_boxed_5453_ = lean_unbox_usize(v_i_5448_);
lean_dec(v_i_5448_);
v_stop_boxed_5454_ = lean_unbox_usize(v_stop_5449_);
lean_dec(v_stop_5449_);
v_res_5455_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__3(v_as_5447_, v_i_boxed_5453_, v_stop_boxed_5454_, v___y_5450_, v___y_5451_);
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5450_);
lean_dec_ref(v_as_5447_);
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(lean_object* v_as_5456_, size_t v_i_5457_, size_t v_stop_5458_, lean_object* v_b_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_){
_start:
{
uint8_t v___x_5463_; 
v___x_5463_ = lean_usize_dec_eq(v_i_5457_, v_stop_5458_);
if (v___x_5463_ == 0)
{
lean_object* v___x_5464_; lean_object* v___x_5465_; 
v___x_5464_ = lean_array_uget_borrowed(v_as_5456_, v_i_5457_);
lean_inc(v___y_5461_);
lean_inc_ref(v___y_5460_);
lean_inc(v___x_5464_);
v___x_5465_ = l_Lean_Elab_Command_elabCommand(v___x_5464_, v___y_5460_, v___y_5461_);
if (lean_obj_tag(v___x_5465_) == 0)
{
lean_object* v_a_5466_; size_t v___x_5467_; size_t v___x_5468_; 
v_a_5466_ = lean_ctor_get(v___x_5465_, 0);
lean_inc(v_a_5466_);
lean_dec_ref(v___x_5465_);
v___x_5467_ = ((size_t)1ULL);
v___x_5468_ = lean_usize_add(v_i_5457_, v___x_5467_);
v_i_5457_ = v___x_5468_;
v_b_5459_ = v_a_5466_;
goto _start;
}
else
{
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
return v___x_5465_;
}
}
else
{
lean_object* v___x_5470_; 
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
v___x_5470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5470_, 0, v_b_5459_);
return v___x_5470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1___boxed(lean_object* v_as_5471_, lean_object* v_i_5472_, lean_object* v_stop_5473_, lean_object* v_b_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_){
_start:
{
size_t v_i_boxed_5478_; size_t v_stop_boxed_5479_; lean_object* v_res_5480_; 
v_i_boxed_5478_ = lean_unbox_usize(v_i_5472_);
lean_dec(v_i_5472_);
v_stop_boxed_5479_ = lean_unbox_usize(v_stop_5473_);
lean_dec(v_stop_5473_);
v_res_5480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(v_as_5471_, v_i_boxed_5478_, v_stop_boxed_5479_, v_b_5474_, v___y_5475_, v___y_5476_);
lean_dec_ref(v_as_5471_);
return v_res_5480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__2(lean_object* v_as_5481_, size_t v_sz_5482_, size_t v_i_5483_, lean_object* v_b_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_){
_start:
{
lean_object* v_a_5489_; uint8_t v___x_5493_; 
v___x_5493_ = lean_usize_dec_lt(v_i_5483_, v_sz_5482_);
if (v___x_5493_ == 0)
{
lean_object* v___x_5494_; 
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
v___x_5494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5494_, 0, v_b_5484_);
return v___x_5494_;
}
else
{
lean_object* v_a_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; 
v_a_5495_ = lean_array_uget_borrowed(v_as_5481_, v_i_5483_);
lean_inc(v_a_5495_);
v___x_5496_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___boxed), 8, 1);
lean_closure_set(v___x_5496_, 0, v_a_5495_);
lean_inc_ref(v___y_5485_);
v___x_5497_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_5496_, v___y_5485_, v___y_5486_);
if (lean_obj_tag(v___x_5497_) == 0)
{
lean_object* v_a_5498_; lean_object* v___x_5499_; lean_object* v___y_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; uint8_t v___x_5504_; 
v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
lean_inc(v_a_5498_);
lean_dec_ref(v___x_5497_);
v___x_5499_ = lean_box(0);
v___x_5502_ = lean_unsigned_to_nat(0u);
v___x_5503_ = lean_array_get_size(v_a_5498_);
v___x_5504_ = lean_nat_dec_lt(v___x_5502_, v___x_5503_);
if (v___x_5504_ == 0)
{
lean_dec(v_a_5498_);
v_a_5489_ = v___x_5499_;
goto v___jp_5488_;
}
else
{
uint8_t v___x_5505_; 
v___x_5505_ = lean_nat_dec_le(v___x_5503_, v___x_5503_);
if (v___x_5505_ == 0)
{
if (v___x_5504_ == 0)
{
lean_dec(v_a_5498_);
v_a_5489_ = v___x_5499_;
goto v___jp_5488_;
}
else
{
size_t v___x_5506_; size_t v___x_5507_; lean_object* v___x_5508_; 
v___x_5506_ = ((size_t)0ULL);
v___x_5507_ = lean_usize_of_nat(v___x_5503_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
v___x_5508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(v_a_5498_, v___x_5506_, v___x_5507_, v___x_5499_, v___y_5485_, v___y_5486_);
lean_dec(v_a_5498_);
v___y_5501_ = v___x_5508_;
goto v___jp_5500_;
}
}
else
{
size_t v___x_5509_; size_t v___x_5510_; lean_object* v___x_5511_; 
v___x_5509_ = ((size_t)0ULL);
v___x_5510_ = lean_usize_of_nat(v___x_5503_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
v___x_5511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(v_a_5498_, v___x_5509_, v___x_5510_, v___x_5499_, v___y_5485_, v___y_5486_);
lean_dec(v_a_5498_);
v___y_5501_ = v___x_5511_;
goto v___jp_5500_;
}
}
v___jp_5500_:
{
if (lean_obj_tag(v___y_5501_) == 0)
{
lean_dec_ref(v___y_5501_);
v_a_5489_ = v___x_5499_;
goto v___jp_5488_;
}
else
{
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
return v___y_5501_;
}
}
}
else
{
lean_object* v_a_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5519_; 
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
v_a_5512_ = lean_ctor_get(v___x_5497_, 0);
v_isSharedCheck_5519_ = !lean_is_exclusive(v___x_5497_);
if (v_isSharedCheck_5519_ == 0)
{
v___x_5514_ = v___x_5497_;
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_a_5512_);
lean_dec(v___x_5497_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5517_; 
if (v_isShared_5515_ == 0)
{
v___x_5517_ = v___x_5514_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_a_5512_);
v___x_5517_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
return v___x_5517_;
}
}
}
}
v___jp_5488_:
{
size_t v___x_5490_; size_t v___x_5491_; 
v___x_5490_ = ((size_t)1ULL);
v___x_5491_ = lean_usize_add(v_i_5483_, v___x_5490_);
v_i_5483_ = v___x_5491_;
v_b_5484_ = v_a_5489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__2___boxed(lean_object* v_as_5520_, lean_object* v_sz_5521_, lean_object* v_i_5522_, lean_object* v_b_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_){
_start:
{
size_t v_sz_boxed_5527_; size_t v_i_boxed_5528_; lean_object* v_res_5529_; 
v_sz_boxed_5527_ = lean_unbox_usize(v_sz_5521_);
lean_dec(v_sz_5521_);
v_i_boxed_5528_ = lean_unbox_usize(v_i_5522_);
lean_dec(v_i_5522_);
v_res_5529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__2(v_as_5520_, v_sz_boxed_5527_, v_i_boxed_5528_, v_b_5523_, v___y_5524_, v___y_5525_);
lean_dec_ref(v_as_5520_);
return v_res_5529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler(lean_object* v_declNames_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_){
_start:
{
lean_object* v___x_5534_; lean_object* v___x_5535_; uint8_t v___x_5536_; uint8_t v_a_5538_; lean_object* v___y_5563_; 
v___x_5534_ = lean_unsigned_to_nat(0u);
v___x_5535_ = lean_array_get_size(v_declNames_5530_);
v___x_5536_ = lean_nat_dec_lt(v___x_5534_, v___x_5535_);
if (v___x_5536_ == 0)
{
lean_object* v___x_5567_; 
v___x_5567_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(v___x_5536_, v_a_5531_, v_a_5532_);
v___y_5563_ = v___x_5567_;
goto v___jp_5562_;
}
else
{
if (v___x_5536_ == 0)
{
v_a_5538_ = v___x_5536_;
goto v___jp_5537_;
}
else
{
size_t v___x_5568_; size_t v___x_5569_; lean_object* v___x_5570_; 
v___x_5568_ = ((size_t)0ULL);
v___x_5569_ = lean_usize_of_nat(v___x_5535_);
v___x_5570_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__3(v_declNames_5530_, v___x_5568_, v___x_5569_, v_a_5531_, v_a_5532_);
if (lean_obj_tag(v___x_5570_) == 0)
{
lean_object* v_a_5571_; uint8_t v___x_5572_; lean_object* v___x_5573_; 
v_a_5571_ = lean_ctor_get(v___x_5570_, 0);
lean_inc(v_a_5571_);
lean_dec_ref(v___x_5570_);
v___x_5572_ = lean_unbox(v_a_5571_);
lean_dec(v_a_5571_);
v___x_5573_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(v___x_5572_, v_a_5531_, v_a_5532_);
v___y_5563_ = v___x_5573_;
goto v___jp_5562_;
}
else
{
v___y_5563_ = v___x_5570_;
goto v___jp_5562_;
}
}
}
v___jp_5537_:
{
if (v___x_5536_ == 0)
{
lean_object* v___x_5539_; lean_object* v___x_5540_; 
lean_dec(v_a_5532_);
lean_dec_ref(v_a_5531_);
v___x_5539_ = lean_box(v___x_5536_);
v___x_5540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5540_, 0, v___x_5539_);
return v___x_5540_;
}
else
{
lean_object* v___x_5541_; size_t v_sz_5542_; size_t v___x_5543_; lean_object* v___x_5544_; 
v___x_5541_ = lean_box(0);
v_sz_5542_ = lean_array_size(v_declNames_5530_);
v___x_5543_ = ((size_t)0ULL);
v___x_5544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__2(v_declNames_5530_, v_sz_5542_, v___x_5543_, v___x_5541_, v_a_5531_, v_a_5532_);
if (lean_obj_tag(v___x_5544_) == 0)
{
lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5552_; 
v_isSharedCheck_5552_ = !lean_is_exclusive(v___x_5544_);
if (v_isSharedCheck_5552_ == 0)
{
lean_object* v_unused_5553_; 
v_unused_5553_ = lean_ctor_get(v___x_5544_, 0);
lean_dec(v_unused_5553_);
v___x_5546_ = v___x_5544_;
v_isShared_5547_ = v_isSharedCheck_5552_;
goto v_resetjp_5545_;
}
else
{
lean_dec(v___x_5544_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5552_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___x_5548_; lean_object* v___x_5550_; 
v___x_5548_ = lean_box(v_a_5538_);
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 0, v___x_5548_);
v___x_5550_ = v___x_5546_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v___x_5548_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
return v___x_5550_;
}
}
}
else
{
lean_object* v_a_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5561_; 
v_a_5554_ = lean_ctor_get(v___x_5544_, 0);
v_isSharedCheck_5561_ = !lean_is_exclusive(v___x_5544_);
if (v_isSharedCheck_5561_ == 0)
{
v___x_5556_ = v___x_5544_;
v_isShared_5557_ = v_isSharedCheck_5561_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_a_5554_);
lean_dec(v___x_5544_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5561_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v___x_5559_; 
if (v_isShared_5557_ == 0)
{
v___x_5559_ = v___x_5556_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v_a_5554_);
v___x_5559_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
return v___x_5559_;
}
}
}
}
}
v___jp_5562_:
{
if (lean_obj_tag(v___y_5563_) == 0)
{
lean_object* v_a_5564_; uint8_t v___x_5565_; 
v_a_5564_ = lean_ctor_get(v___y_5563_, 0);
v___x_5565_ = lean_unbox(v_a_5564_);
if (v___x_5565_ == 0)
{
lean_dec(v_a_5532_);
lean_dec_ref(v_a_5531_);
return v___y_5563_;
}
else
{
uint8_t v___x_5566_; 
lean_inc(v_a_5564_);
lean_dec_ref(v___y_5563_);
v___x_5566_ = lean_unbox(v_a_5564_);
lean_dec(v_a_5564_);
v_a_5538_ = v___x_5566_;
goto v___jp_5537_;
}
}
else
{
lean_dec(v_a_5532_);
lean_dec_ref(v_a_5531_);
return v___y_5563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___boxed(lean_object* v_declNames_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_){
_start:
{
lean_object* v_res_5578_; 
v_res_5578_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler(v_declNames_5574_, v_a_5575_, v_a_5576_);
lean_dec_ref(v_declNames_5574_);
return v_res_5578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler_spec__0(lean_object* v_as_5579_, size_t v_sz_5580_, size_t v_i_5581_, lean_object* v_b_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_){
_start:
{
lean_object* v_a_5587_; uint8_t v___x_5591_; 
v___x_5591_ = lean_usize_dec_lt(v_i_5581_, v_sz_5580_);
if (v___x_5591_ == 0)
{
lean_object* v___x_5592_; 
lean_dec(v___y_5584_);
lean_dec_ref(v___y_5583_);
v___x_5592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5592_, 0, v_b_5582_);
return v___x_5592_;
}
else
{
lean_object* v_a_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; 
v_a_5593_ = lean_array_uget_borrowed(v_as_5579_, v_i_5581_);
lean_inc(v_a_5593_);
v___x_5594_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___boxed), 8, 1);
lean_closure_set(v___x_5594_, 0, v_a_5593_);
lean_inc_ref(v___y_5583_);
v___x_5595_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_5594_, v___y_5583_, v___y_5584_);
if (lean_obj_tag(v___x_5595_) == 0)
{
lean_object* v_a_5596_; lean_object* v___x_5597_; lean_object* v___y_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; uint8_t v___x_5602_; 
v_a_5596_ = lean_ctor_get(v___x_5595_, 0);
lean_inc(v_a_5596_);
lean_dec_ref(v___x_5595_);
v___x_5597_ = lean_box(0);
v___x_5600_ = lean_unsigned_to_nat(0u);
v___x_5601_ = lean_array_get_size(v_a_5596_);
v___x_5602_ = lean_nat_dec_lt(v___x_5600_, v___x_5601_);
if (v___x_5602_ == 0)
{
lean_dec(v_a_5596_);
v_a_5587_ = v___x_5597_;
goto v___jp_5586_;
}
else
{
uint8_t v___x_5603_; 
v___x_5603_ = lean_nat_dec_le(v___x_5601_, v___x_5601_);
if (v___x_5603_ == 0)
{
if (v___x_5602_ == 0)
{
lean_dec(v_a_5596_);
v_a_5587_ = v___x_5597_;
goto v___jp_5586_;
}
else
{
size_t v___x_5604_; size_t v___x_5605_; lean_object* v___x_5606_; 
v___x_5604_ = ((size_t)0ULL);
v___x_5605_ = lean_usize_of_nat(v___x_5601_);
lean_inc(v___y_5584_);
lean_inc_ref(v___y_5583_);
v___x_5606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(v_a_5596_, v___x_5604_, v___x_5605_, v___x_5597_, v___y_5583_, v___y_5584_);
lean_dec(v_a_5596_);
v___y_5599_ = v___x_5606_;
goto v___jp_5598_;
}
}
else
{
size_t v___x_5607_; size_t v___x_5608_; lean_object* v___x_5609_; 
v___x_5607_ = ((size_t)0ULL);
v___x_5608_ = lean_usize_of_nat(v___x_5601_);
lean_inc(v___y_5584_);
lean_inc_ref(v___y_5583_);
v___x_5609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(v_a_5596_, v___x_5607_, v___x_5608_, v___x_5597_, v___y_5583_, v___y_5584_);
lean_dec(v_a_5596_);
v___y_5599_ = v___x_5609_;
goto v___jp_5598_;
}
}
v___jp_5598_:
{
if (lean_obj_tag(v___y_5599_) == 0)
{
lean_dec_ref(v___y_5599_);
v_a_5587_ = v___x_5597_;
goto v___jp_5586_;
}
else
{
lean_dec(v___y_5584_);
lean_dec_ref(v___y_5583_);
return v___y_5599_;
}
}
}
else
{
lean_object* v_a_5610_; lean_object* v___x_5612_; uint8_t v_isShared_5613_; uint8_t v_isSharedCheck_5617_; 
lean_dec(v___y_5584_);
lean_dec_ref(v___y_5583_);
v_a_5610_ = lean_ctor_get(v___x_5595_, 0);
v_isSharedCheck_5617_ = !lean_is_exclusive(v___x_5595_);
if (v_isSharedCheck_5617_ == 0)
{
v___x_5612_ = v___x_5595_;
v_isShared_5613_ = v_isSharedCheck_5617_;
goto v_resetjp_5611_;
}
else
{
lean_inc(v_a_5610_);
lean_dec(v___x_5595_);
v___x_5612_ = lean_box(0);
v_isShared_5613_ = v_isSharedCheck_5617_;
goto v_resetjp_5611_;
}
v_resetjp_5611_:
{
lean_object* v___x_5615_; 
if (v_isShared_5613_ == 0)
{
v___x_5615_ = v___x_5612_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5616_; 
v_reuseFailAlloc_5616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5616_, 0, v_a_5610_);
v___x_5615_ = v_reuseFailAlloc_5616_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
return v___x_5615_;
}
}
}
}
v___jp_5586_:
{
size_t v___x_5588_; size_t v___x_5589_; 
v___x_5588_ = ((size_t)1ULL);
v___x_5589_ = lean_usize_add(v_i_5581_, v___x_5588_);
v_i_5581_ = v___x_5589_;
v_b_5582_ = v_a_5587_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler_spec__0___boxed(lean_object* v_as_5618_, lean_object* v_sz_5619_, lean_object* v_i_5620_, lean_object* v_b_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_){
_start:
{
size_t v_sz_boxed_5625_; size_t v_i_boxed_5626_; lean_object* v_res_5627_; 
v_sz_boxed_5625_ = lean_unbox_usize(v_sz_5619_);
lean_dec(v_sz_5619_);
v_i_boxed_5626_ = lean_unbox_usize(v_i_5620_);
lean_dec(v_i_5620_);
v_res_5627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler_spec__0(v_as_5618_, v_sz_boxed_5625_, v_i_boxed_5626_, v_b_5621_, v___y_5622_, v___y_5623_);
lean_dec_ref(v_as_5618_);
return v_res_5627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler(lean_object* v_declNames_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_){
_start:
{
lean_object* v___x_5632_; lean_object* v___x_5633_; uint8_t v___x_5634_; uint8_t v_a_5636_; lean_object* v___y_5661_; 
v___x_5632_ = lean_unsigned_to_nat(0u);
v___x_5633_ = lean_array_get_size(v_declNames_5628_);
v___x_5634_ = lean_nat_dec_lt(v___x_5632_, v___x_5633_);
if (v___x_5634_ == 0)
{
lean_object* v___x_5665_; 
v___x_5665_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(v___x_5634_, v_a_5629_, v_a_5630_);
v___y_5661_ = v___x_5665_;
goto v___jp_5660_;
}
else
{
if (v___x_5634_ == 0)
{
v_a_5636_ = v___x_5634_;
goto v___jp_5635_;
}
else
{
size_t v___x_5666_; size_t v___x_5667_; lean_object* v___x_5668_; 
v___x_5666_ = ((size_t)0ULL);
v___x_5667_ = lean_usize_of_nat(v___x_5633_);
v___x_5668_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__3(v_declNames_5628_, v___x_5666_, v___x_5667_, v_a_5629_, v_a_5630_);
if (lean_obj_tag(v___x_5668_) == 0)
{
lean_object* v_a_5669_; uint8_t v___x_5670_; lean_object* v___x_5671_; 
v_a_5669_ = lean_ctor_get(v___x_5668_, 0);
lean_inc(v_a_5669_);
lean_dec_ref(v___x_5668_);
v___x_5670_ = lean_unbox(v_a_5669_);
lean_dec(v_a_5669_);
v___x_5671_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(v___x_5670_, v_a_5629_, v_a_5630_);
v___y_5661_ = v___x_5671_;
goto v___jp_5660_;
}
else
{
v___y_5661_ = v___x_5668_;
goto v___jp_5660_;
}
}
}
v___jp_5635_:
{
if (v___x_5634_ == 0)
{
lean_object* v___x_5637_; lean_object* v___x_5638_; 
lean_dec(v_a_5630_);
lean_dec_ref(v_a_5629_);
v___x_5637_ = lean_box(v___x_5634_);
v___x_5638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5637_);
return v___x_5638_;
}
else
{
lean_object* v___x_5639_; size_t v_sz_5640_; size_t v___x_5641_; lean_object* v___x_5642_; 
v___x_5639_ = lean_box(0);
v_sz_5640_ = lean_array_size(v_declNames_5628_);
v___x_5641_ = ((size_t)0ULL);
v___x_5642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler_spec__0(v_declNames_5628_, v_sz_5640_, v___x_5641_, v___x_5639_, v_a_5629_, v_a_5630_);
if (lean_obj_tag(v___x_5642_) == 0)
{
lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5650_; 
v_isSharedCheck_5650_ = !lean_is_exclusive(v___x_5642_);
if (v_isSharedCheck_5650_ == 0)
{
lean_object* v_unused_5651_; 
v_unused_5651_ = lean_ctor_get(v___x_5642_, 0);
lean_dec(v_unused_5651_);
v___x_5644_ = v___x_5642_;
v_isShared_5645_ = v_isSharedCheck_5650_;
goto v_resetjp_5643_;
}
else
{
lean_dec(v___x_5642_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5650_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v___x_5646_; lean_object* v___x_5648_; 
v___x_5646_ = lean_box(v_a_5636_);
if (v_isShared_5645_ == 0)
{
lean_ctor_set(v___x_5644_, 0, v___x_5646_);
v___x_5648_ = v___x_5644_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v___x_5646_);
v___x_5648_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
return v___x_5648_;
}
}
}
else
{
lean_object* v_a_5652_; lean_object* v___x_5654_; uint8_t v_isShared_5655_; uint8_t v_isSharedCheck_5659_; 
v_a_5652_ = lean_ctor_get(v___x_5642_, 0);
v_isSharedCheck_5659_ = !lean_is_exclusive(v___x_5642_);
if (v_isSharedCheck_5659_ == 0)
{
v___x_5654_ = v___x_5642_;
v_isShared_5655_ = v_isSharedCheck_5659_;
goto v_resetjp_5653_;
}
else
{
lean_inc(v_a_5652_);
lean_dec(v___x_5642_);
v___x_5654_ = lean_box(0);
v_isShared_5655_ = v_isSharedCheck_5659_;
goto v_resetjp_5653_;
}
v_resetjp_5653_:
{
lean_object* v___x_5657_; 
if (v_isShared_5655_ == 0)
{
v___x_5657_ = v___x_5654_;
goto v_reusejp_5656_;
}
else
{
lean_object* v_reuseFailAlloc_5658_; 
v_reuseFailAlloc_5658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_a_5652_);
v___x_5657_ = v_reuseFailAlloc_5658_;
goto v_reusejp_5656_;
}
v_reusejp_5656_:
{
return v___x_5657_;
}
}
}
}
}
v___jp_5660_:
{
if (lean_obj_tag(v___y_5661_) == 0)
{
lean_object* v_a_5662_; uint8_t v___x_5663_; 
v_a_5662_ = lean_ctor_get(v___y_5661_, 0);
v___x_5663_ = lean_unbox(v_a_5662_);
if (v___x_5663_ == 0)
{
lean_dec(v_a_5630_);
lean_dec_ref(v_a_5629_);
return v___y_5661_;
}
else
{
uint8_t v___x_5664_; 
lean_inc(v_a_5662_);
lean_dec_ref(v___y_5661_);
v___x_5664_ = lean_unbox(v_a_5662_);
lean_dec(v_a_5662_);
v_a_5636_ = v___x_5664_;
goto v___jp_5635_;
}
}
else
{
lean_dec(v_a_5630_);
lean_dec_ref(v_a_5629_);
return v___y_5661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler___boxed(lean_object* v_declNames_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_){
_start:
{
lean_object* v_res_5676_; 
v_res_5676_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler(v_declNames_5672_, v_a_5673_, v_a_5674_);
lean_dec_ref(v_declNames_5672_);
return v_res_5676_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__21_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; 
v___x_5730_ = lean_unsigned_to_nat(2304768170u);
v___x_5731_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__20_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_));
v___x_5732_ = l_Lean_Name_num___override(v___x_5731_, v___x_5730_);
return v___x_5732_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__23_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; 
v___x_5734_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__22_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_));
v___x_5735_ = lean_obj_once(&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__21_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__21_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__21_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_);
v___x_5736_ = l_Lean_Name_str___override(v___x_5735_, v___x_5734_);
return v___x_5736_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__25_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; 
v___x_5738_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__24_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_));
v___x_5739_ = lean_obj_once(&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__23_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__23_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__23_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_);
v___x_5740_ = l_Lean_Name_str___override(v___x_5739_, v___x_5738_);
return v___x_5740_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__26_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; 
v___x_5741_ = lean_unsigned_to_nat(2u);
v___x_5742_ = lean_obj_once(&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__25_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__25_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__25_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_);
v___x_5743_ = l_Lean_Name_num___override(v___x_5742_, v___x_5741_);
return v___x_5743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; 
v___x_5745_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__2));
v___x_5746_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__0_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_));
v___x_5747_ = l_Lean_Elab_registerDerivingHandler(v___x_5745_, v___x_5746_);
if (lean_obj_tag(v___x_5747_) == 0)
{
lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; 
lean_dec_ref(v___x_5747_);
v___x_5748_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__1));
v___x_5749_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__1_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_));
v___x_5750_ = l_Lean_Elab_registerDerivingHandler(v___x_5748_, v___x_5749_);
if (lean_obj_tag(v___x_5750_) == 0)
{
lean_object* v___x_5751_; uint8_t v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; 
lean_dec_ref(v___x_5750_);
v___x_5751_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__0));
v___x_5752_ = 0;
v___x_5753_ = lean_obj_once(&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__26_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__26_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__26_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_);
v___x_5754_ = l_Lean_registerTraceClass(v___x_5751_, v___x_5752_, v___x_5753_);
if (lean_obj_tag(v___x_5754_) == 0)
{
lean_object* v___x_5755_; lean_object* v___x_5756_; 
lean_dec_ref(v___x_5754_);
v___x_5755_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__1));
v___x_5756_ = l_Lean_registerTraceClass(v___x_5755_, v___x_5752_, v___x_5753_);
return v___x_5756_;
}
else
{
return v___x_5754_;
}
}
else
{
return v___x_5750_;
}
}
else
{
return v___x_5747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2____boxed(lean_object* v_a_5757_){
_start:
{
lean_object* v_res_5758_; 
v_res_5758_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_();
return v_res_5758_;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_FromToJson(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_FromToJson(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_FromToJson(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_FromToJson(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_FromToJson(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_FromToJson(builtin);
}
#ifdef __cplusplus
}
#endif
