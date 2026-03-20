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
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__1(lean_object* v_s_202_, lean_object* v_pos_203_){
_start:
{
lean_object* v_str_204_; lean_object* v_startInclusive_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_str_204_ = lean_ctor_get(v_s_202_, 0);
v_startInclusive_205_ = lean_ctor_get(v_s_202_, 1);
v___x_206_ = lean_nat_add(v_startInclusive_205_, v_pos_203_);
v___x_207_ = lean_nat_sub(v___x_206_, v_startInclusive_205_);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_nat_dec_eq(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint32_t v___x_215_; uint32_t v___x_216_; uint8_t v___x_217_; 
lean_inc(v_startInclusive_205_);
lean_inc_ref(v_str_204_);
v___x_210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_210_, 0, v_str_204_);
lean_ctor_set(v___x_210_, 1, v_startInclusive_205_);
lean_ctor_set(v___x_210_, 2, v___x_206_);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_sub(v___x_207_, v___x_211_);
lean_dec(v___x_207_);
v___x_213_ = l_String_Slice_posLE(v___x_210_, v___x_212_);
lean_dec_ref(v___x_210_);
v___x_214_ = lean_nat_add(v_startInclusive_205_, v___x_213_);
v___x_215_ = lean_string_utf8_get_fast(v_str_204_, v___x_214_);
lean_dec(v___x_214_);
v___x_216_ = 63;
v___x_217_ = lean_uint32_dec_eq(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v___x_213_);
return v_pos_203_;
}
else
{
uint8_t v___x_218_; 
v___x_218_ = lean_nat_dec_lt(v___x_213_, v_pos_203_);
if (v___x_218_ == 0)
{
lean_dec(v___x_213_);
return v_pos_203_;
}
else
{
lean_dec(v_pos_203_);
v_pos_203_ = v___x_213_;
goto _start;
}
}
}
else
{
lean_dec(v___x_207_);
lean_dec(v___x_206_);
return v_pos_203_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__1___boxed(lean_object* v_s_220_, lean_object* v_pos_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__1(v_s_220_, v_pos_221_);
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
lean_object* v_str_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v_s_u2081_243_; uint8_t v___y_245_; uint8_t v___x_251_; 
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
v___x_242_ = l_String_Slice_Pos_revSkipWhile___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__1(v___x_241_, v___x_240_);
lean_dec_ref(v___x_241_);
v_s_u2081_243_ = lean_string_utf8_extract(v_str_238_, v___x_239_, v___x_242_);
lean_dec(v___x_242_);
v___x_251_ = lean_string_dec_eq(v_str_238_, v_s_u2081_243_);
lean_dec_ref(v_str_238_);
if (v___x_251_ == 0)
{
uint8_t v___x_252_; 
v___x_252_ = 1;
v___y_245_ = v___x_252_;
goto v___jp_244_;
}
else
{
uint8_t v___x_253_; 
v___x_253_ = 0;
v___y_245_ = v___x_253_;
goto v___jp_244_;
}
v___jp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_246_ = lean_box(2);
v___x_247_ = l_Lean_Syntax_mkStrLit(v_s_u2081_243_, v___x_246_);
v___x_248_ = lean_box(v___y_245_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkJsonField___boxed(lean_object* v_n_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Elab_Deriving_FromToJson_mkJsonField(v_n_254_, v_a_255_, v_a_256_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0(lean_object* v_00_u03b1_259_, lean_object* v_msg_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0___redArg(v_msg_260_, v___y_261_, v___y_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0___boxed(lean_object* v_00_u03b1_265_, lean_object* v_msg_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_throwError___at___00Lean_Elab_Deriving_FromToJson_mkJsonField_spec__0(v_00_u03b1_265_, v_msg_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_270_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__9));
v___x_292_ = l_String_toRawSubstring_x27(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__32));
v___x_346_ = l_String_toRawSubstring_x27(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__45(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__44));
v___x_375_ = l_String_toRawSubstring_x27(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg(lean_object* v_header_388_, size_t v_sz_389_, size_t v_i_390_, lean_object* v_bs_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_lt(v_i_390_, v_sz_389_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
lean_dec_ref(v___y_392_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v_bs_391_);
return v___x_396_;
}
else
{
lean_object* v_v_397_; lean_object* v___x_398_; 
v_v_397_ = lean_array_uget(v_bs_391_, v_i_390_);
lean_inc(v_v_397_);
v___x_398_ = l_Lean_Elab_Deriving_FromToJson_mkJsonField(v_v_397_, v___y_392_, v___y_393_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v_fst_400_; lean_object* v_snd_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_487_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref(v___x_398_);
v_fst_400_ = lean_ctor_get(v_a_399_, 0);
v_snd_401_ = lean_ctor_get(v_a_399_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_a_399_);
if (v_isSharedCheck_487_ == 0)
{
v___x_403_ = v_a_399_;
v_isShared_404_ = v_isSharedCheck_487_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_snd_401_);
lean_inc(v_fst_400_);
lean_dec(v_a_399_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_487_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_targetNames_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_bs_x27_408_; lean_object* v_a_410_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_targetNames_405_ = lean_ctor_get(v_header_388_, 2);
v___x_406_ = lean_box(0);
v___x_407_ = lean_unsigned_to_nat(0u);
v_bs_x27_408_ = lean_array_uset(v_bs_391_, v_i_390_, v___x_407_);
v___x_415_ = lean_array_get_borrowed(v___x_406_, v_targetNames_405_, v___x_407_);
lean_inc(v___x_415_);
v___x_416_ = lean_mk_syntax_ident(v___x_415_);
v___x_417_ = lean_unbox(v_fst_400_);
if (v___x_417_ == 0)
{
lean_object* v_ref_418_; lean_object* v_quotContext_419_; lean_object* v_currMacroScope_420_; uint8_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v_ref_418_ = lean_ctor_get(v___y_392_, 5);
v_quotContext_419_ = lean_ctor_get(v___y_392_, 10);
v_currMacroScope_420_ = lean_ctor_get(v___y_392_, 11);
v___x_421_ = lean_unbox(v_fst_400_);
lean_dec(v_fst_400_);
v___x_422_ = l_Lean_SourceInfo_fromRef(v_ref_418_, v___x_421_);
v___x_423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1));
v___x_424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_422_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 2);
lean_ctor_set(v___x_403_, 1, v___x_424_);
lean_ctor_set(v___x_403_, 0, v___x_422_);
v___x_426_ = v___x_403_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_424_);
v___x_426_ = v_reuseFailAlloc_465_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_427_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4));
v___x_429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_430_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_422_);
v___x_431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_422_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_433_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
lean_inc(v_currMacroScope_420_);
lean_inc(v_quotContext_419_);
v___x_434_ = l_Lean_addMacroScope(v_quotContext_419_, v___x_406_, v_currMacroScope_420_);
v___x_435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__28));
lean_inc(v___x_422_);
v___x_436_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_436_, 0, v___x_422_);
lean_ctor_set(v___x_436_, 1, v___x_433_);
lean_ctor_set(v___x_436_, 2, v___x_434_);
lean_ctor_set(v___x_436_, 3, v___x_435_);
lean_inc(v___x_422_);
v___x_437_ = l_Lean_Syntax_node1(v___x_422_, v___x_432_, v___x_436_);
lean_inc(v___x_422_);
v___x_438_ = l_Lean_Syntax_node2(v___x_422_, v___x_429_, v___x_431_, v___x_437_);
v___x_439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
lean_inc(v___x_422_);
v___x_440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_422_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_442_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
lean_inc(v_currMacroScope_420_);
lean_inc(v_quotContext_419_);
v___x_444_ = l_Lean_addMacroScope(v_quotContext_419_, v___x_443_, v_currMacroScope_420_);
v___x_445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__37));
lean_inc(v___x_422_);
v___x_446_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_446_, 0, v___x_422_);
lean_ctor_set(v___x_446_, 1, v___x_442_);
lean_ctor_set(v___x_446_, 2, v___x_444_);
lean_ctor_set(v___x_446_, 3, v___x_445_);
v___x_447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39));
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41));
v___x_449_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_422_);
v___x_450_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_422_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
lean_inc_ref(v___x_450_);
lean_inc(v___x_438_);
lean_inc(v___x_422_);
v___x_451_ = l_Lean_Syntax_node3(v___x_422_, v___x_448_, v___x_438_, v___x_416_, v___x_450_);
v___x_452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__42));
lean_inc(v___x_422_);
v___x_453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_422_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = lean_mk_syntax_ident(v_v_397_);
lean_inc(v___x_422_);
v___x_455_ = l_Lean_Syntax_node3(v___x_422_, v___x_447_, v___x_451_, v___x_453_, v___x_454_);
lean_inc(v___x_422_);
v___x_456_ = l_Lean_Syntax_node1(v___x_422_, v___x_427_, v___x_455_);
lean_inc(v___x_422_);
v___x_457_ = l_Lean_Syntax_node2(v___x_422_, v___x_441_, v___x_446_, v___x_456_);
lean_inc(v___x_422_);
v___x_458_ = l_Lean_Syntax_node1(v___x_422_, v___x_427_, v___x_457_);
lean_inc(v___x_422_);
v___x_459_ = l_Lean_Syntax_node3(v___x_422_, v___x_427_, v_snd_401_, v___x_440_, v___x_458_);
lean_inc(v___x_422_);
v___x_460_ = l_Lean_Syntax_node3(v___x_422_, v___x_428_, v___x_438_, v___x_459_, v___x_450_);
lean_inc(v___x_422_);
v___x_461_ = l_Lean_Syntax_node1(v___x_422_, v___x_427_, v___x_460_);
v___x_462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_422_);
v___x_463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_422_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = l_Lean_Syntax_node3(v___x_422_, v___x_423_, v___x_426_, v___x_461_, v___x_463_);
v_a_410_ = v___x_464_;
goto v___jp_409_;
}
}
else
{
lean_object* v_ref_466_; lean_object* v_quotContext_467_; lean_object* v_currMacroScope_468_; uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
lean_dec(v_fst_400_);
v_ref_466_ = lean_ctor_get(v___y_392_, 5);
v_quotContext_467_ = lean_ctor_get(v___y_392_, 10);
v_currMacroScope_468_ = lean_ctor_get(v___y_392_, 11);
v___x_469_ = 0;
v___x_470_ = l_Lean_SourceInfo_fromRef(v_ref_466_, v___x_469_);
v___x_471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_472_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__45, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__45_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__45);
v___x_473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__46));
lean_inc(v_currMacroScope_468_);
lean_inc(v_quotContext_467_);
v___x_474_ = l_Lean_addMacroScope(v_quotContext_467_, v___x_473_, v_currMacroScope_468_);
v___x_475_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__49));
lean_inc(v___x_470_);
v___x_476_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_476_, 0, v___x_470_);
lean_ctor_set(v___x_476_, 1, v___x_472_);
lean_ctor_set(v___x_476_, 2, v___x_474_);
lean_ctor_set(v___x_476_, 3, v___x_475_);
v___x_477_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39));
v___x_479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__42));
lean_inc(v___x_470_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 2);
lean_ctor_set(v___x_403_, 1, v___x_479_);
lean_ctor_set(v___x_403_, 0, v___x_470_);
v___x_481_ = v___x_403_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_479_);
v___x_481_ = v_reuseFailAlloc_486_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_482_ = lean_mk_syntax_ident(v_v_397_);
lean_inc(v___x_470_);
v___x_483_ = l_Lean_Syntax_node3(v___x_470_, v___x_478_, v___x_416_, v___x_481_, v___x_482_);
lean_inc(v___x_470_);
v___x_484_ = l_Lean_Syntax_node2(v___x_470_, v___x_477_, v_snd_401_, v___x_483_);
v___x_485_ = l_Lean_Syntax_node2(v___x_470_, v___x_471_, v___x_476_, v___x_484_);
v_a_410_ = v___x_485_;
goto v___jp_409_;
}
}
v___jp_409_:
{
size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((size_t)1ULL);
v___x_412_ = lean_usize_add(v_i_390_, v___x_411_);
v___x_413_ = lean_array_uset(v_bs_x27_408_, v_i_390_, v_a_410_);
v_i_390_ = v___x_412_;
v_bs_391_ = v___x_413_;
goto _start;
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v_v_397_);
lean_dec_ref(v___y_392_);
lean_dec_ref(v_bs_391_);
v_a_488_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_398_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_398_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___boxed(lean_object* v_header_496_, lean_object* v_sz_497_, lean_object* v_i_498_, lean_object* v_bs_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
size_t v_sz_boxed_503_; size_t v_i_boxed_504_; lean_object* v_res_505_; 
v_sz_boxed_503_ = lean_unbox_usize(v_sz_497_);
lean_dec(v_sz_497_);
v_i_boxed_504_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg(v_header_496_, v_sz_boxed_503_, v_i_boxed_504_, v_bs_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v_header_496_);
return v_res_505_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__2));
v___x_511_ = l_String_toRawSubstring_x27(v___x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__10(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__9));
v___x_527_ = l_String_toRawSubstring_x27(v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct(lean_object* v_header_544_, lean_object* v_indName_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_553_; lean_object* v_env_554_; uint8_t v___x_555_; lean_object* v___x_556_; size_t v_sz_557_; size_t v___x_558_; lean_object* v___x_559_; 
v___x_553_ = lean_st_ref_get(v_a_551_);
v_env_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc_ref(v_env_554_);
lean_dec(v___x_553_);
v___x_555_ = 0;
v___x_556_ = l_Lean_getStructureFieldsFlattened(v_env_554_, v_indName_545_, v___x_555_);
v_sz_557_ = lean_array_size(v___x_556_);
v___x_558_ = ((size_t)0ULL);
lean_inc_ref(v_a_550_);
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg(v_header_544_, v_sz_557_, v___x_558_, v___x_556_, v_a_550_, v_a_551_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_600_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_600_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_600_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_600_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_ref_564_; lean_object* v_quotContext_565_; lean_object* v_currMacroScope_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v_ref_564_ = lean_ctor_get(v_a_550_, 5);
lean_inc(v_ref_564_);
v_quotContext_565_ = lean_ctor_get(v_a_550_, 10);
lean_inc(v_quotContext_565_);
v_currMacroScope_566_ = lean_ctor_get(v_a_550_, 11);
lean_inc(v_currMacroScope_566_);
lean_dec_ref(v_a_550_);
v___x_567_ = l_Lean_SourceInfo_fromRef(v_ref_564_, v___x_555_);
lean_dec(v_ref_564_);
v___x_568_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__1));
v___x_569_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3, &l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3_once, _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3);
v___x_570_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__4));
lean_inc(v_currMacroScope_566_);
lean_inc(v_quotContext_565_);
v___x_571_ = l_Lean_addMacroScope(v_quotContext_565_, v___x_570_, v_currMacroScope_566_);
v___x_572_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__7));
lean_inc(v___x_567_);
v___x_573_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_573_, 0, v___x_567_);
lean_ctor_set(v___x_573_, 1, v___x_569_);
lean_ctor_set(v___x_573_, 2, v___x_571_);
lean_ctor_set(v___x_573_, 3, v___x_572_);
v___x_574_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__8));
lean_inc(v___x_567_);
v___x_575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_567_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_577_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__10, &l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__10_once, _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__10);
v___x_578_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__13));
v___x_579_ = l_Lean_addMacroScope(v_quotContext_565_, v___x_578_, v_currMacroScope_566_);
v___x_580_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__17));
lean_inc(v___x_567_);
v___x_581_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_581_, 0, v___x_567_);
lean_ctor_set(v___x_581_, 1, v___x_577_);
lean_ctor_set(v___x_581_, 2, v___x_579_);
lean_ctor_set(v___x_581_, 3, v___x_580_);
v___x_582_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1));
v___x_584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_567_);
v___x_585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_567_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v___x_587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
v___x_588_ = l_Lean_Syntax_SepArray_ofElems(v___x_587_, v_a_560_);
lean_dec(v_a_560_);
v___x_589_ = l_Array_append___redArg(v___x_586_, v___x_588_);
lean_dec_ref(v___x_588_);
lean_inc(v___x_567_);
v___x_590_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_590_, 0, v___x_567_);
lean_ctor_set(v___x_590_, 1, v___x_582_);
lean_ctor_set(v___x_590_, 2, v___x_589_);
v___x_591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_567_);
v___x_592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_567_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
lean_inc(v___x_567_);
v___x_593_ = l_Lean_Syntax_node3(v___x_567_, v___x_583_, v___x_585_, v___x_590_, v___x_592_);
lean_inc(v___x_567_);
v___x_594_ = l_Lean_Syntax_node1(v___x_567_, v___x_582_, v___x_593_);
lean_inc(v___x_567_);
v___x_595_ = l_Lean_Syntax_node2(v___x_567_, v___x_576_, v___x_581_, v___x_594_);
v___x_596_ = l_Lean_Syntax_node3(v___x_567_, v___x_568_, v___x_573_, v___x_575_, v___x_595_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_596_);
v___x_598_ = v___x_562_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_a_550_);
v_a_601_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_559_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_559_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___boxed(lean_object* v_header_609_, lean_object* v_indName_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct(v_header_609_, v_indName_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
lean_dec(v_a_616_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec_ref(v_header_609_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0(lean_object* v_header_619_, size_t v_sz_620_, size_t v_i_621_, lean_object* v_bs_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg(v_header_619_, v_sz_620_, v_i_621_, v_bs_622_, v___y_627_, v___y_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___boxed(lean_object* v_header_631_, lean_object* v_sz_632_, lean_object* v_i_633_, lean_object* v_bs_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
size_t v_sz_boxed_642_; size_t v_i_boxed_643_; lean_object* v_res_644_; 
v_sz_boxed_642_ = lean_unbox_usize(v_sz_632_);
lean_dec(v_sz_632_);
v_i_boxed_643_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0(v_header_631_, v_sz_boxed_642_, v_i_boxed_643_, v_bs_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v_header_631_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___lam__0(lean_object* v_k_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v_b_648_, lean_object* v_c_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = lean_apply_9(v_k_645_, v_b_648_, v_c_649_, v___y_646_, v___y_647_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, lean_box(0));
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___lam__0___boxed(lean_object* v_k_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v_b_659_, lean_object* v_c_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___lam__0(v_k_656_, v___y_657_, v___y_658_, v_b_659_, v_c_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(lean_object* v_type_667_, lean_object* v_k_668_, uint8_t v_cleanupAnnotations_669_, uint8_t v_whnfType_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___f_678_; lean_object* v___x_679_; 
v___f_678_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_678_, 0, v_k_668_);
lean_closure_set(v___f_678_, 1, v___y_671_);
lean_closure_set(v___f_678_, 2, v___y_672_);
v___x_679_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_667_, v___f_678_, v_cleanupAnnotations_669_, v_whnfType_670_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_679_) == 0)
{
return v___x_679_;
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg___boxed(lean_object* v_type_688_, lean_object* v_k_689_, lean_object* v_cleanupAnnotations_690_, lean_object* v_whnfType_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_699_; uint8_t v_whnfType_boxed_700_; lean_object* v_res_701_; 
v_cleanupAnnotations_boxed_699_ = lean_unbox(v_cleanupAnnotations_690_);
v_whnfType_boxed_700_ = lean_unbox(v_whnfType_691_);
v_res_701_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(v_type_688_, v_k_689_, v_cleanupAnnotations_boxed_699_, v_whnfType_boxed_700_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4(lean_object* v_00_u03b1_702_, lean_object* v_type_703_, lean_object* v_k_704_, uint8_t v_cleanupAnnotations_705_, uint8_t v_whnfType_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(v_type_703_, v_k_704_, v_cleanupAnnotations_705_, v_whnfType_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___boxed(lean_object* v_00_u03b1_715_, lean_object* v_type_716_, lean_object* v_k_717_, lean_object* v_cleanupAnnotations_718_, lean_object* v_whnfType_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_727_; uint8_t v_whnfType_boxed_728_; lean_object* v_res_729_; 
v_cleanupAnnotations_boxed_727_ = lean_unbox(v_cleanupAnnotations_718_);
v_whnfType_boxed_728_ = lean_unbox(v_whnfType_719_);
v_res_729_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4(v_00_u03b1_715_, v_type_716_, v_k_717_, v_cleanupAnnotations_boxed_727_, v_whnfType_boxed_728_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
return v_res_729_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1(lean_object* v_msg_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v_toApplicative_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_838_; 
v___x_745_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__0);
v___x_746_ = l_ReaderT_instMonad___redArg(v___x_745_);
v_toApplicative_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v___x_746_, 1);
lean_dec(v_unused_839_);
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_838_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_toApplicative_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_838_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_toFunctor_751_; lean_object* v_toSeq_752_; lean_object* v_toSeqLeft_753_; lean_object* v_toSeqRight_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_836_; 
v_toFunctor_751_ = lean_ctor_get(v_toApplicative_747_, 0);
v_toSeq_752_ = lean_ctor_get(v_toApplicative_747_, 2);
v_toSeqLeft_753_ = lean_ctor_get(v_toApplicative_747_, 3);
v_toSeqRight_754_ = lean_ctor_get(v_toApplicative_747_, 4);
v_isSharedCheck_836_ = !lean_is_exclusive(v_toApplicative_747_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v_toApplicative_747_, 1);
lean_dec(v_unused_837_);
v___x_756_ = v_toApplicative_747_;
v_isShared_757_ = v_isSharedCheck_836_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_toSeqRight_754_);
lean_inc(v_toSeqLeft_753_);
lean_inc(v_toSeq_752_);
lean_inc(v_toFunctor_751_);
lean_dec(v_toApplicative_747_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_836_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___f_765_; lean_object* v___x_767_; 
v___f_758_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__1));
v___f_759_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_751_);
v___f_760_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_760_, 0, v_toFunctor_751_);
v___f_761_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_761_, 0, v_toFunctor_751_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v___f_760_);
lean_ctor_set(v___x_762_, 1, v___f_761_);
v___f_763_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_763_, 0, v_toSeqRight_754_);
v___f_764_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_764_, 0, v_toSeqLeft_753_);
v___f_765_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_765_, 0, v_toSeq_752_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v___f_763_);
lean_ctor_set(v___x_756_, 3, v___f_764_);
lean_ctor_set(v___x_756_, 2, v___f_765_);
lean_ctor_set(v___x_756_, 1, v___f_758_);
lean_ctor_set(v___x_756_, 0, v___x_762_);
v___x_767_ = v___x_756_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v___f_758_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v___f_765_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v___f_764_);
lean_ctor_set(v_reuseFailAlloc_835_, 4, v___f_763_);
v___x_767_ = v_reuseFailAlloc_835_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___f_759_);
lean_ctor_set(v___x_749_, 0, v___x_767_);
v___x_769_ = v___x_749_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v___f_759_);
v___x_769_ = v_reuseFailAlloc_834_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v_toApplicative_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_832_; 
v___x_770_ = l_ReaderT_instMonad___redArg(v___x_769_);
v_toApplicative_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v___x_770_, 1);
lean_dec(v_unused_833_);
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_832_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_toApplicative_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_832_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_toFunctor_775_; lean_object* v_toSeq_776_; lean_object* v_toSeqLeft_777_; lean_object* v_toSeqRight_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_830_; 
v_toFunctor_775_ = lean_ctor_get(v_toApplicative_771_, 0);
v_toSeq_776_ = lean_ctor_get(v_toApplicative_771_, 2);
v_toSeqLeft_777_ = lean_ctor_get(v_toApplicative_771_, 3);
v_toSeqRight_778_ = lean_ctor_get(v_toApplicative_771_, 4);
v_isSharedCheck_830_ = !lean_is_exclusive(v_toApplicative_771_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v_toApplicative_771_, 1);
lean_dec(v_unused_831_);
v___x_780_ = v_toApplicative_771_;
v_isShared_781_ = v_isSharedCheck_830_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_toSeqRight_778_);
lean_inc(v_toSeqLeft_777_);
lean_inc(v_toSeq_776_);
lean_inc(v_toFunctor_775_);
lean_dec(v_toApplicative_771_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_830_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___f_789_; lean_object* v___x_791_; 
v___f_782_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__3));
v___f_783_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_775_);
v___f_784_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_784_, 0, v_toFunctor_775_);
v___f_785_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_785_, 0, v_toFunctor_775_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___f_784_);
lean_ctor_set(v___x_786_, 1, v___f_785_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_787_, 0, v_toSeqRight_778_);
v___f_788_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_788_, 0, v_toSeqLeft_777_);
v___f_789_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_789_, 0, v_toSeq_776_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 4, v___f_787_);
lean_ctor_set(v___x_780_, 3, v___f_788_);
lean_ctor_set(v___x_780_, 2, v___f_789_);
lean_ctor_set(v___x_780_, 1, v___f_782_);
lean_ctor_set(v___x_780_, 0, v___x_786_);
v___x_791_ = v___x_780_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___f_782_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v___f_789_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v___f_788_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v___f_787_);
v___x_791_ = v_reuseFailAlloc_829_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_793_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___f_783_);
lean_ctor_set(v___x_773_, 0, v___x_791_);
v___x_793_ = v___x_773_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v___f_783_);
v___x_793_ = v_reuseFailAlloc_828_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; lean_object* v_toApplicative_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_826_; 
v___x_794_ = l_ReaderT_instMonad___redArg(v___x_793_);
v_toApplicative_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v___x_794_, 1);
lean_dec(v_unused_827_);
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_826_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_toApplicative_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_826_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_toFunctor_799_; lean_object* v_toSeq_800_; lean_object* v_toSeqLeft_801_; lean_object* v_toSeqRight_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_824_; 
v_toFunctor_799_ = lean_ctor_get(v_toApplicative_795_, 0);
v_toSeq_800_ = lean_ctor_get(v_toApplicative_795_, 2);
v_toSeqLeft_801_ = lean_ctor_get(v_toApplicative_795_, 3);
v_toSeqRight_802_ = lean_ctor_get(v_toApplicative_795_, 4);
v_isSharedCheck_824_ = !lean_is_exclusive(v_toApplicative_795_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v_toApplicative_795_, 1);
lean_dec(v_unused_825_);
v___x_804_ = v_toApplicative_795_;
v_isShared_805_ = v_isSharedCheck_824_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_toSeqRight_802_);
lean_inc(v_toSeqLeft_801_);
lean_inc(v_toSeq_800_);
lean_inc(v_toFunctor_799_);
lean_dec(v_toApplicative_795_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_824_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___f_811_; lean_object* v___f_812_; lean_object* v___f_813_; lean_object* v___x_815_; 
v___f_806_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__5));
v___f_807_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_799_);
v___f_808_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_808_, 0, v_toFunctor_799_);
v___f_809_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_809_, 0, v_toFunctor_799_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___f_808_);
lean_ctor_set(v___x_810_, 1, v___f_809_);
v___f_811_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_811_, 0, v_toSeqRight_802_);
v___f_812_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_812_, 0, v_toSeqLeft_801_);
v___f_813_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_813_, 0, v_toSeq_800_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 4, v___f_811_);
lean_ctor_set(v___x_804_, 3, v___f_812_);
lean_ctor_set(v___x_804_, 2, v___f_813_);
lean_ctor_set(v___x_804_, 1, v___f_806_);
lean_ctor_set(v___x_804_, 0, v___x_810_);
v___x_815_ = v___x_804_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___f_806_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v___f_813_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v___f_812_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v___f_811_);
v___x_815_ = v_reuseFailAlloc_823_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___f_807_);
lean_ctor_set(v___x_797_, 0, v___x_815_);
v___x_817_ = v___x_797_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___f_807_);
v___x_817_ = v_reuseFailAlloc_822_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_16637__overap_820_; lean_object* v___x_821_; 
v___x_818_ = lean_box(0);
v___x_819_ = l_instInhabitedOfMonad___redArg(v___x_817_, v___x_818_);
v___x_16637__overap_820_ = lean_panic_fn(v___x_819_, v_msg_737_);
v___x_821_ = lean_apply_7(v___x_16637__overap_820_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, lean_box(0));
return v___x_821_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1___boxed(lean_object* v_msg_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1(v_msg_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
return v_res_848_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__10(lean_object* v_opts_849_, lean_object* v_opt_850_){
_start:
{
lean_object* v_name_851_; lean_object* v_defValue_852_; lean_object* v_map_853_; lean_object* v___x_854_; 
v_name_851_ = lean_ctor_get(v_opt_850_, 0);
v_defValue_852_ = lean_ctor_get(v_opt_850_, 1);
v_map_853_ = lean_ctor_get(v_opts_849_, 0);
v___x_854_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_853_, v_name_851_);
if (lean_obj_tag(v___x_854_) == 0)
{
uint8_t v___x_855_; 
v___x_855_ = lean_unbox(v_defValue_852_);
return v___x_855_;
}
else
{
lean_object* v_val_856_; 
v_val_856_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_val_856_);
lean_dec_ref(v___x_854_);
if (lean_obj_tag(v_val_856_) == 1)
{
uint8_t v_v_857_; 
v_v_857_ = lean_ctor_get_uint8(v_val_856_, 0);
lean_dec_ref(v_val_856_);
return v_v_857_;
}
else
{
uint8_t v___x_858_; 
lean_dec(v_val_856_);
v___x_858_ = lean_unbox(v_defValue_852_);
return v___x_858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_opts_859_, lean_object* v_opt_860_){
_start:
{
uint8_t v_res_861_; lean_object* v_r_862_; 
v_res_861_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__10(v_opts_859_, v_opt_860_);
lean_dec_ref(v_opt_860_);
lean_dec_ref(v_opts_859_);
v_r_862_ = lean_box(v_res_861_);
return v_r_862_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_box(1);
v___x_864_ = l_Lean_MessageData_ofFormat(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__2));
v___x_869_ = l_Lean_MessageData_ofFormat(v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
return v_x_870_;
}
else
{
lean_object* v_head_872_; lean_object* v_tail_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_895_; 
v_head_872_ = lean_ctor_get(v_x_871_, 0);
v_tail_873_ = lean_ctor_get(v_x_871_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_x_871_);
if (v_isSharedCheck_895_ == 0)
{
v___x_875_ = v_x_871_;
v_isShared_876_ = v_isSharedCheck_895_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_tail_873_);
lean_inc(v_head_872_);
lean_dec(v_x_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_895_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_before_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_893_; 
v_before_877_ = lean_ctor_get(v_head_872_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v_head_872_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v_head_872_, 1);
lean_dec(v_unused_894_);
v___x_879_ = v_head_872_;
v_isShared_880_ = v_isSharedCheck_893_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_before_877_);
lean_dec(v_head_872_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_893_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 7);
lean_ctor_set(v___x_879_, 1, v___x_881_);
lean_ctor_set(v___x_879_, 0, v_x_870_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_x_870_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_881_);
v___x_883_ = v_reuseFailAlloc_892_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__3);
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 7);
lean_ctor_set(v___x_875_, 1, v___x_884_);
lean_ctor_set(v___x_875_, 0, v___x_883_);
v___x_886_ = v___x_875_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_891_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = l_Lean_MessageData_ofSyntax(v_before_877_);
v___x_888_ = l_Lean_indentD(v___x_887_);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_886_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v_x_870_ = v___x_889_;
v_x_871_ = v_tail_873_;
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
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_900_ = l_Lean_MessageData_ofFormat(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_901_, lean_object* v_macroStack_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_options_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_options_905_ = lean_ctor_get(v___y_903_, 2);
v___x_906_ = l_Lean_Elab_pp_macroStack;
v___x_907_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__10(v_options_905_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
lean_dec(v_macroStack_902_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v_msgData_901_);
return v___x_908_;
}
else
{
if (lean_obj_tag(v_macroStack_902_) == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v_msgData_901_);
return v___x_909_;
}
else
{
lean_object* v_head_910_; lean_object* v_after_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_926_; 
v_head_910_ = lean_ctor_get(v_macroStack_902_, 0);
lean_inc(v_head_910_);
v_after_911_ = lean_ctor_get(v_head_910_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_head_910_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_head_910_, 0);
lean_dec(v_unused_927_);
v___x_913_ = v_head_910_;
v_isShared_914_ = v_isSharedCheck_926_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_after_911_);
lean_dec(v_head_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_926_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11___closed__0);
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 7);
lean_ctor_set(v___x_913_, 1, v___x_915_);
lean_ctor_set(v___x_913_, 0, v_msgData_901_);
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_msgData_901_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_915_);
v___x_917_ = v_reuseFailAlloc_925_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_msgData_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_918_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = l_Lean_MessageData_ofSyntax(v_after_911_);
v___x_921_ = l_Lean_indentD(v___x_920_);
v_msgData_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_922_, 0, v___x_919_);
lean_ctor_set(v_msgData_922_, 1, v___x_921_);
v___x_923_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3_spec__11(v_msgData_922_, v_macroStack_902_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_928_, lean_object* v_macroStack_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_928_, v_macroStack_929_, v___y_930_);
lean_dec_ref(v___y_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__2(lean_object* v_msgData_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; lean_object* v_env_940_; lean_object* v___x_941_; lean_object* v_mctx_942_; lean_object* v_lctx_943_; lean_object* v_options_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_939_ = lean_st_ref_get(v___y_937_);
v_env_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc_ref(v_env_940_);
lean_dec(v___x_939_);
v___x_941_ = lean_st_ref_get(v___y_935_);
v_mctx_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc_ref(v_mctx_942_);
lean_dec(v___x_941_);
v_lctx_943_ = lean_ctor_get(v___y_934_, 2);
v_options_944_ = lean_ctor_get(v___y_936_, 2);
lean_inc_ref(v_options_944_);
lean_inc_ref(v_lctx_943_);
v___x_945_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_945_, 0, v_env_940_);
lean_ctor_set(v___x_945_, 1, v_mctx_942_);
lean_ctor_set(v___x_945_, 2, v_lctx_943_);
lean_ctor_set(v___x_945_, 3, v_options_944_);
v___x_946_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v_msgData_933_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__2(v_msgData_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_ref_963_; lean_object* v___x_964_; lean_object* v_a_965_; lean_object* v_macroStack_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_977_; 
v_ref_963_ = lean_ctor_get(v___y_960_, 5);
v___x_964_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__2(v_msg_955_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref(v___x_964_);
v_macroStack_966_ = lean_ctor_get(v___y_956_, 1);
lean_inc(v_macroStack_966_);
lean_dec_ref(v___y_956_);
lean_inc(v_macroStack_966_);
v___x_967_ = l_Lean_Elab_getBetterRef(v_ref_963_, v_macroStack_966_);
v___x_968_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_965_, v_macroStack_966_, v___y_960_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_977_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_967_);
lean_ctor_set(v___x_973_, 1, v_a_969_);
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 1);
lean_ctor_set(v___x_971_, 0, v___x_973_);
v___x_975_ = v___x_971_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg(v_msg_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
return v_res_986_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__0));
v___x_989_ = l_Lean_stringToMessageData(v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__2));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_996_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__6));
v___x_997_ = lean_unsigned_to_nat(11u);
v___x_998_ = lean_unsigned_to_nat(122u);
v___x_999_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__5));
v___x_1000_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__4));
v___x_1001_ = l_mkPanicMessageWithDecl(v___x_1000_, v___x_999_, v___x_998_, v___x_997_, v___x_996_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0(lean_object* v_constName_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1018_; lean_object* v_env_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1018_ = lean_st_ref_get(v___y_1008_);
v_env_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc_ref(v_env_1019_);
lean_dec(v___x_1018_);
v___x_1020_ = 0;
lean_inc(v_constName_1002_);
v___x_1021_ = l_Lean_Environment_findAsync_x3f(v_env_1019_, v_constName_1002_, v___x_1020_);
if (lean_obj_tag(v___x_1021_) == 1)
{
lean_object* v_val_1022_; uint8_t v_kind_1023_; 
v_val_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_val_1022_);
lean_dec_ref(v___x_1021_);
v_kind_1023_ = lean_ctor_get_uint8(v_val_1022_, sizeof(void*)*3);
if (v_kind_1023_ == 6)
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1022_);
if (lean_obj_tag(v___x_1024_) == 6)
{
lean_object* v_val_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v_constName_1002_);
v_val_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_val_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 0);
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_val_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_dec_ref(v___x_1024_);
v___x_1033_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__7);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
v___x_1034_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__1(v___x_1033_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1043_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
if (lean_obj_tag(v_a_1035_) == 0)
{
lean_del_object(v___x_1037_);
goto v___jp_1010_;
}
else
{
lean_object* v_val_1039_; lean_object* v___x_1041_; 
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v_constName_1002_);
v_val_1039_ = lean_ctor_get(v_a_1035_, 0);
lean_inc(v_val_1039_);
lean_dec_ref(v_a_1035_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v_val_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_val_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v_constName_1002_);
v_a_1044_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1034_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1034_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
else
{
lean_dec(v_val_1022_);
goto v___jp_1010_;
}
}
else
{
lean_dec(v___x_1021_);
goto v___jp_1010_;
}
v___jp_1010_:
{
lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1011_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1);
v___x_1012_ = 0;
v___x_1013_ = l_Lean_MessageData_ofConstName(v_constName_1002_, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1011_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__3);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg(v___x_1016_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___boxed(lean_object* v_constName_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0(v_constName_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg(lean_object* v_upperBound_1068_, lean_object* v_a_1069_, lean_object* v_b_1070_, lean_object* v___y_1071_){
_start:
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_nat_dec_lt(v_a_1069_, v_upperBound_1068_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
lean_dec(v_a_1069_);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_b_1070_);
return v___x_1074_;
}
else
{
lean_object* v_ref_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_ref_1075_ = lean_ctor_get(v___y_1071_, 5);
v___x_1076_ = 0;
v___x_1077_ = l_Lean_SourceInfo_fromRef(v_ref_1075_, v___x_1076_);
v___x_1078_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1));
v___x_1079_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__2));
lean_inc(v___x_1077_);
v___x_1080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1077_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_Syntax_node1(v___x_1077_, v___x_1078_, v___x_1080_);
v___x_1082_ = lean_array_push(v_b_1070_, v___x_1081_);
v___x_1083_ = lean_unsigned_to_nat(1u);
v___x_1084_ = lean_nat_add(v_a_1069_, v___x_1083_);
lean_dec(v_a_1069_);
v_a_1069_ = v___x_1084_;
v_b_1070_ = v___x_1082_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_1086_, lean_object* v_a_1087_, lean_object* v_b_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg(v_upperBound_1086_, v_a_1087_, v_b_1088_, v___y_1089_);
lean_dec_ref(v___y_1089_);
lean_dec(v_upperBound_1086_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0(lean_object* v_a_1095_, lean_object* v_fst_1096_, lean_object* v_fst_1097_, lean_object* v_____r_1098_, lean_object* v_userNames_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___closed__1));
v___x_1108_ = l_Lean_Core_mkFreshUserName(v___x_1107_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1124_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1124_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1124_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1113_ = lean_mk_syntax_ident(v_a_1109_);
v___x_1114_ = l_Lean_LocalDecl_type(v_a_1095_);
lean_inc(v___x_1113_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1113_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = lean_array_push(v_fst_1096_, v___x_1115_);
v___x_1117_ = lean_array_push(v_fst_1097_, v___x_1113_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v_userNames_1099_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1120_);
v___x_1122_ = v___x_1111_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v_userNames_1099_);
lean_dec(v_fst_1097_);
lean_dec(v_fst_1096_);
v_a_1125_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1108_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1108_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___boxed(lean_object* v_a_1133_, lean_object* v_fst_1134_, lean_object* v_fst_1135_, lean_object* v_____r_1136_, lean_object* v_userNames_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0(v_a_1133_, v_fst_1134_, v_fst_1135_, v_____r_1136_, v_userNames_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec_ref(v_a_1133_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg(lean_object* v_upperBound_1146_, lean_object* v___x_1147_, lean_object* v_xs_1148_, lean_object* v_a_1149_, lean_object* v_b_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___y_1159_; uint8_t v___x_1181_; 
v___x_1181_ = lean_nat_dec_lt(v_a_1149_, v_upperBound_1146_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec_ref(v___y_1153_);
lean_dec(v_a_1149_);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_b_1150_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1183_ = l_Lean_instInhabitedExpr;
v___x_1184_ = lean_nat_add(v___x_1147_, v_a_1149_);
v___x_1185_ = lean_array_get_borrowed(v___x_1183_, v_xs_1148_, v___x_1184_);
lean_dec(v___x_1184_);
v___x_1186_ = l_Lean_Expr_fvarId_x21(v___x_1185_);
lean_inc_ref(v___y_1153_);
v___x_1187_ = l_Lean_FVarId_getDecl___redArg(v___x_1186_, v___y_1153_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_snd_1188_; lean_object* v_a_1189_; lean_object* v_fst_1190_; lean_object* v_fst_1191_; lean_object* v_snd_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v_snd_1188_ = lean_ctor_get(v_b_1150_, 1);
lean_inc(v_snd_1188_);
v_a_1189_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1189_);
lean_dec_ref(v___x_1187_);
v_fst_1190_ = lean_ctor_get(v_b_1150_, 0);
lean_inc(v_fst_1190_);
lean_dec_ref(v_b_1150_);
v_fst_1191_ = lean_ctor_get(v_snd_1188_, 0);
lean_inc(v_fst_1191_);
v_snd_1192_ = lean_ctor_get(v_snd_1188_, 1);
lean_inc(v_snd_1192_);
lean_dec(v_snd_1188_);
v___x_1193_ = l_Lean_LocalDecl_userName(v_a_1189_);
v___x_1194_ = l_Lean_Name_hasMacroScopes(v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_array_push(v_snd_1192_, v___x_1193_);
v___x_1196_ = lean_box(0);
lean_inc(v___y_1156_);
lean_inc_ref(v___y_1155_);
v___x_1197_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0(v_a_1189_, v_fst_1191_, v_fst_1190_, v___x_1196_, v___x_1195_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v_a_1189_);
v___y_1159_ = v___x_1197_;
goto v___jp_1158_;
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec(v___x_1193_);
v___x_1198_ = lean_box(0);
lean_inc(v___y_1156_);
lean_inc_ref(v___y_1155_);
v___x_1199_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0(v_a_1189_, v_fst_1191_, v_fst_1190_, v___x_1198_, v_snd_1192_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v_a_1189_);
v___y_1159_ = v___x_1199_;
goto v___jp_1158_;
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec_ref(v___y_1153_);
lean_dec_ref(v_b_1150_);
lean_dec(v_a_1149_);
v_a_1200_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1187_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1187_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
v___jp_1158_:
{
if (lean_obj_tag(v___y_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1172_; 
v_a_1160_ = lean_ctor_get(v___y_1159_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___y_1159_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1162_ = v___y_1159_;
v_isShared_1163_ = v_isSharedCheck_1172_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___y_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1172_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
if (lean_obj_tag(v_a_1160_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; 
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec_ref(v___y_1153_);
lean_dec(v_a_1149_);
v_a_1164_ = lean_ctor_get(v_a_1160_, 0);
lean_inc(v_a_1164_);
lean_dec_ref(v_a_1160_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v_a_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_del_object(v___x_1162_);
v_a_1168_ = lean_ctor_get(v_a_1160_, 0);
lean_inc(v_a_1168_);
lean_dec_ref(v_a_1160_);
v___x_1169_ = lean_unsigned_to_nat(1u);
v___x_1170_ = lean_nat_add(v_a_1149_, v___x_1169_);
lean_dec(v_a_1149_);
v_a_1149_ = v___x_1170_;
v_b_1150_ = v_a_1168_;
goto _start;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec_ref(v___y_1153_);
lean_dec(v_a_1149_);
v_a_1173_ = lean_ctor_get(v___y_1159_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___y_1159_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___y_1159_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___y_1159_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___boxed(lean_object* v_upperBound_1208_, lean_object* v___x_1209_, lean_object* v_xs_1210_, lean_object* v_a_1211_, lean_object* v_b_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_1208_, v___x_1209_, v_xs_1210_, v_a_1211_, v_b_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1216_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v_xs_1210_);
lean_dec(v___x_1209_);
lean_dec(v_upperBound_1208_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(size_t v_sz_1221_, size_t v_i_1222_, lean_object* v_bs_1223_){
_start:
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_usize_dec_lt(v_i_1222_, v_sz_1221_);
if (v___x_1224_ == 0)
{
return v_bs_1223_;
}
else
{
lean_object* v_v_1225_; lean_object* v___x_1226_; lean_object* v_bs_x27_1227_; size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v_v_1225_ = lean_array_uget(v_bs_1223_, v_i_1222_);
v___x_1226_ = lean_unsigned_to_nat(0u);
v_bs_x27_1227_ = lean_array_uset(v_bs_1223_, v_i_1222_, v___x_1226_);
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_add(v_i_1222_, v___x_1228_);
v___x_1230_ = lean_array_uset(v_bs_x27_1227_, v_i_1222_, v_v_1225_);
v_i_1222_ = v___x_1229_;
v_bs_1223_ = v___x_1230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1___boxed(lean_object* v_sz_1232_, lean_object* v_i_1233_, lean_object* v_bs_1234_){
_start:
{
size_t v_sz_boxed_1235_; size_t v_i_boxed_1236_; lean_object* v_res_1237_; 
v_sz_boxed_1235_ = lean_unbox_usize(v_sz_1232_);
lean_dec(v_sz_1232_);
v_i_boxed_1236_ = lean_unbox_usize(v_i_1233_);
lean_dec(v_i_1233_);
v_res_1237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(v_sz_boxed_1235_, v_i_boxed_1236_, v_bs_1234_);
return v_res_1237_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
v___x_1253_ = l_Lean_mkAtom(v___x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(lean_object* v_indVal_1255_, lean_object* v___x_1256_, lean_object* v_alts_1257_, lean_object* v_numFields_1258_, lean_object* v_name_1259_, lean_object* v_rhs_1260_, lean_object* v_a_1261_, lean_object* v_xs_1262_, lean_object* v_x_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_numParams_1271_; lean_object* v_numIndices_1272_; lean_object* v___x_1273_; 
v_numParams_1271_ = lean_ctor_get(v_indVal_1255_, 1);
v_numIndices_1272_ = lean_ctor_get(v_indVal_1255_, 2);
lean_inc_ref(v_alts_1257_);
lean_inc(v___x_1256_);
v___x_1273_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg(v_numIndices_1272_, v___x_1256_, v_alts_1257_, v___y_1268_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1275_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref(v___x_1273_);
lean_inc(v___x_1256_);
v___x_1275_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg(v_numParams_1271_, v___x_1256_, v_alts_1257_, v___y_1268_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = lean_mk_empty_array_with_capacity(v___x_1256_);
lean_inc_ref(v___x_1277_);
v___x_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_a_1276_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc_ref(v___y_1266_);
v___x_1280_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg(v_numFields_1258_, v_numParams_1271_, v_xs_1262_, v___x_1256_, v___x_1279_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_snd_1282_; lean_object* v_fst_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1342_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1280_);
v_snd_1282_ = lean_ctor_get(v_a_1281_, 1);
v_fst_1283_ = lean_ctor_get(v_a_1281_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_a_1281_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1285_ = v_a_1281_;
v_isShared_1286_ = v_isSharedCheck_1342_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snd_1282_);
lean_inc(v_fst_1283_);
lean_dec(v_a_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1342_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_fst_1287_; lean_object* v_snd_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1341_; 
v_fst_1287_ = lean_ctor_get(v_snd_1282_, 0);
v_snd_1288_ = lean_ctor_get(v_snd_1282_, 1);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_snd_1282_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1290_ = v_snd_1282_;
v_isShared_1291_ = v_isSharedCheck_1341_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_snd_1288_);
lean_inc(v_fst_1287_);
lean_dec(v_snd_1282_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1341_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_ref_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
v_ref_1292_ = lean_ctor_get(v___y_1268_, 5);
v___x_1293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1294_ = 0;
v___x_1295_ = l_Lean_SourceInfo_fromRef(v_ref_1292_, v___x_1294_);
v___x_1296_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__1));
v___x_1297_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__2));
lean_inc(v___x_1295_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set_tag(v___x_1290_, 2);
lean_ctor_set(v___x_1290_, 1, v___x_1297_);
lean_ctor_set(v___x_1290_, 0, v___x_1295_);
v___x_1299_ = v___x_1290_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___y_1309_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1300_ = lean_mk_syntax_ident(v_name_1259_);
lean_inc(v___x_1295_);
v___x_1301_ = l_Lean_Syntax_node2(v___x_1295_, v___x_1296_, v___x_1299_, v___x_1300_);
v___x_1302_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_1303_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v___x_1304_ = l_Array_append___redArg(v___x_1303_, v_fst_1283_);
lean_dec(v_fst_1283_);
lean_inc(v___x_1295_);
v___x_1305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1295_);
lean_ctor_set(v___x_1305_, 1, v___x_1302_);
lean_ctor_set(v___x_1305_, 2, v___x_1304_);
lean_inc(v___x_1295_);
v___x_1306_ = l_Lean_Syntax_node2(v___x_1295_, v___x_1293_, v___x_1301_, v___x_1305_);
v___x_1307_ = lean_array_push(v_a_1274_, v___x_1306_);
v___x_1335_ = lean_array_get_size(v_snd_1288_);
v___x_1336_ = lean_array_get_size(v_fst_1287_);
v___x_1337_ = lean_nat_dec_eq(v___x_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
lean_dec(v_snd_1288_);
v___x_1338_ = lean_box(0);
v___y_1309_ = v___x_1338_;
goto v___jp_1308_;
}
else
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_snd_1288_);
v___y_1309_ = v___x_1339_;
goto v___jp_1308_;
}
v___jp_1308_:
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_apply_10(v_rhs_1260_, v_a_1261_, v_fst_1287_, v___y_1309_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, lean_box(0));
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1334_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1334_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1334_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1315_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4));
v___x_1316_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__5));
lean_inc(v___x_1295_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set_tag(v___x_1285_, 2);
lean_ctor_set(v___x_1285_, 1, v___x_1316_);
lean_ctor_set(v___x_1285_, 0, v___x_1295_);
v___x_1318_ = v___x_1285_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
size_t v_sz_1319_; size_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v_sz_1319_ = lean_array_size(v___x_1307_);
v___x_1320_ = ((size_t)0ULL);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(v_sz_1319_, v___x_1320_, v___x_1307_);
v___x_1322_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6);
v___x_1323_ = l_Lean_mkSepArray(v___x_1321_, v___x_1322_);
lean_dec_ref(v___x_1321_);
v___x_1324_ = l_Array_append___redArg(v___x_1303_, v___x_1323_);
lean_dec_ref(v___x_1323_);
lean_inc(v___x_1295_);
v___x_1325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1295_);
lean_ctor_set(v___x_1325_, 1, v___x_1302_);
lean_ctor_set(v___x_1325_, 2, v___x_1324_);
lean_inc(v___x_1295_);
v___x_1326_ = l_Lean_Syntax_node1(v___x_1295_, v___x_1302_, v___x_1325_);
v___x_1327_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__7));
lean_inc(v___x_1295_);
v___x_1328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1295_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = l_Lean_Syntax_node4(v___x_1295_, v___x_1315_, v___x_1318_, v___x_1326_, v___x_1328_, v_a_1311_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1329_);
v___x_1331_ = v___x_1313_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_dec_ref(v___x_1307_);
lean_dec(v___x_1295_);
lean_del_object(v___x_1285_);
return v___x_1310_;
}
}
}
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec(v_a_1274_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec_ref(v_a_1261_);
lean_dec_ref(v_rhs_1260_);
lean_dec(v_name_1259_);
v_a_1343_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1280_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1280_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec(v_a_1274_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec_ref(v_a_1261_);
lean_dec_ref(v_rhs_1260_);
lean_dec(v_name_1259_);
lean_dec(v___x_1256_);
v_a_1351_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1275_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1275_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec_ref(v_a_1261_);
lean_dec_ref(v_rhs_1260_);
lean_dec(v_name_1259_);
lean_dec_ref(v_alts_1257_);
lean_dec(v___x_1256_);
v_a_1359_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1273_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1273_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___boxed(lean_object* v_indVal_1367_, lean_object* v___x_1368_, lean_object* v_alts_1369_, lean_object* v_numFields_1370_, lean_object* v_name_1371_, lean_object* v_rhs_1372_, lean_object* v_a_1373_, lean_object* v_xs_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(v_indVal_1367_, v___x_1368_, v_alts_1369_, v_numFields_1370_, v_name_1371_, v_rhs_1372_, v_a_1373_, v_xs_1374_, v_x_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec_ref(v_x_1375_);
lean_dec_ref(v_xs_1374_);
lean_dec(v_numFields_1370_);
lean_dec_ref(v_indVal_1367_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg(lean_object* v_indVal_1386_, lean_object* v_rhs_1387_, lean_object* v_as_x27_1388_, lean_object* v_b_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
if (lean_obj_tag(v_as_x27_1388_) == 0)
{
lean_object* v___x_1397_; 
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec_ref(v_rhs_1387_);
lean_dec_ref(v_indVal_1386_);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_b_1389_);
return v___x_1397_;
}
else
{
lean_object* v_head_1398_; lean_object* v_tail_1399_; lean_object* v___x_1400_; 
v_head_1398_ = lean_ctor_get(v_as_x27_1388_, 0);
lean_inc(v_head_1398_);
v_tail_1399_ = lean_ctor_get(v_as_x27_1388_, 1);
lean_inc(v_tail_1399_);
lean_dec_ref(v_as_x27_1388_);
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc_ref(v___y_1390_);
v___x_1400_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0(v_head_1398_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v_toConstantVal_1402_; lean_object* v_numFields_1403_; lean_object* v_name_1404_; lean_object* v_type_1405_; lean_object* v___x_1406_; lean_object* v_alts_1407_; lean_object* v___f_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref(v___x_1400_);
v_toConstantVal_1402_ = lean_ctor_get(v_a_1401_, 0);
v_numFields_1403_ = lean_ctor_get(v_a_1401_, 4);
lean_inc(v_numFields_1403_);
v_name_1404_ = lean_ctor_get(v_toConstantVal_1402_, 0);
lean_inc(v_name_1404_);
v_type_1405_ = lean_ctor_get(v_toConstantVal_1402_, 2);
lean_inc_ref(v_type_1405_);
v___x_1406_ = lean_unsigned_to_nat(0u);
v_alts_1407_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___closed__0));
lean_inc_ref(v_rhs_1387_);
lean_inc_ref(v_indVal_1386_);
v___f_1408_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___boxed), 16, 7);
lean_closure_set(v___f_1408_, 0, v_indVal_1386_);
lean_closure_set(v___f_1408_, 1, v___x_1406_);
lean_closure_set(v___f_1408_, 2, v_alts_1407_);
lean_closure_set(v___f_1408_, 3, v_numFields_1403_);
lean_closure_set(v___f_1408_, 4, v_name_1404_);
lean_closure_set(v___f_1408_, 5, v_rhs_1387_);
lean_closure_set(v___f_1408_, 6, v_a_1401_);
v___x_1409_ = 0;
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc_ref(v___y_1390_);
v___x_1410_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(v_type_1405_, v___f_1408_, v___x_1409_, v___x_1409_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref(v___x_1410_);
v___x_1412_ = lean_array_push(v_b_1389_, v_a_1411_);
v_as_x27_1388_ = v_tail_1399_;
v_b_1389_ = v___x_1412_;
goto _start;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_tail_1399_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec_ref(v_b_1389_);
lean_dec_ref(v_rhs_1387_);
lean_dec_ref(v_indVal_1386_);
v_a_1414_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1410_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1410_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v_tail_1399_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec_ref(v_b_1389_);
lean_dec_ref(v_rhs_1387_);
lean_dec_ref(v_indVal_1386_);
v_a_1422_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1400_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1400_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___boxed(lean_object* v_indVal_1430_, lean_object* v_rhs_1431_, lean_object* v_as_x27_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg(v_indVal_1430_, v_rhs_1431_, v_as_x27_1432_, v_b_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__6(size_t v_sz_1442_, size_t v_i_1443_, lean_object* v_bs_1444_){
_start:
{
uint8_t v___x_1445_; 
v___x_1445_ = lean_usize_dec_lt(v_i_1443_, v_sz_1442_);
if (v___x_1445_ == 0)
{
return v_bs_1444_;
}
else
{
lean_object* v_v_1446_; lean_object* v___x_1447_; lean_object* v_bs_x27_1448_; size_t v___x_1449_; size_t v___x_1450_; lean_object* v___x_1451_; 
v_v_1446_ = lean_array_uget(v_bs_1444_, v_i_1443_);
v___x_1447_ = lean_unsigned_to_nat(0u);
v_bs_x27_1448_ = lean_array_uset(v_bs_1444_, v_i_1443_, v___x_1447_);
v___x_1449_ = ((size_t)1ULL);
v___x_1450_ = lean_usize_add(v_i_1443_, v___x_1449_);
v___x_1451_ = lean_array_uset(v_bs_x27_1448_, v_i_1443_, v_v_1446_);
v_i_1443_ = v___x_1450_;
v_bs_1444_ = v___x_1451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__6___boxed(lean_object* v_sz_1453_, lean_object* v_i_1454_, lean_object* v_bs_1455_){
_start:
{
size_t v_sz_boxed_1456_; size_t v_i_boxed_1457_; lean_object* v_res_1458_; 
v_sz_boxed_1456_ = lean_unbox_usize(v_sz_1453_);
lean_dec(v_sz_1453_);
v_i_boxed_1457_ = lean_unbox_usize(v_i_1454_);
lean_dec(v_i_1454_);
v_res_1458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__6(v_sz_boxed_1456_, v_i_boxed_1457_, v_bs_1455_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts(lean_object* v_indVal_1459_, lean_object* v_rhs_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_ctors_1468_; lean_object* v_alts_1469_; lean_object* v___x_1470_; 
v_ctors_1468_ = lean_ctor_get(v_indVal_1459_, 4);
lean_inc(v_ctors_1468_);
v_alts_1469_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___closed__0));
v___x_1470_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg(v_indVal_1459_, v_rhs_1460_, v_ctors_1468_, v_alts_1469_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1481_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
size_t v_sz_1475_; size_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v_sz_1475_ = lean_array_size(v_a_1471_);
v___x_1476_ = ((size_t)0ULL);
v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__6(v_sz_1475_, v___x_1476_, v_a_1471_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1477_);
v___x_1479_ = v___x_1473_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
else
{
return v___x_1470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts___boxed(lean_object* v_indVal_1482_, lean_object* v_rhs_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts(v_indVal_1482_, v_rhs_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2(lean_object* v_upperBound_1492_, lean_object* v___x_1493_, lean_object* v_xs_1494_, lean_object* v_inst_1495_, lean_object* v_R_1496_, lean_object* v_a_1497_, lean_object* v_b_1498_, lean_object* v_c_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_1492_, v___x_1493_, v_xs_1494_, v_a_1497_, v_b_1498_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___boxed(lean_object* v_upperBound_1508_, lean_object* v___x_1509_, lean_object* v_xs_1510_, lean_object* v_inst_1511_, lean_object* v_R_1512_, lean_object* v_a_1513_, lean_object* v_b_1514_, lean_object* v_c_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2(v_upperBound_1508_, v___x_1509_, v_xs_1510_, v_inst_1511_, v_R_1512_, v_a_1513_, v_b_1514_, v_c_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1519_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec_ref(v_xs_1510_);
lean_dec(v___x_1509_);
lean_dec(v_upperBound_1508_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3(lean_object* v_upperBound_1524_, lean_object* v_inst_1525_, lean_object* v_R_1526_, lean_object* v_a_1527_, lean_object* v_b_1528_, lean_object* v_c_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg(v_upperBound_1524_, v_a_1527_, v_b_1528_, v___y_1534_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___boxed(lean_object* v_upperBound_1538_, lean_object* v_inst_1539_, lean_object* v_R_1540_, lean_object* v_a_1541_, lean_object* v_b_1542_, lean_object* v_c_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3(v_upperBound_1538_, v_inst_1539_, v_R_1540_, v_a_1541_, v_b_1542_, v_c_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v_upperBound_1538_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5(lean_object* v_indVal_1552_, lean_object* v_rhs_1553_, lean_object* v_as_1554_, lean_object* v_as_x27_1555_, lean_object* v_b_1556_, lean_object* v_a_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg(v_indVal_1552_, v_rhs_1553_, v_as_x27_1555_, v_b_1556_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___boxed(lean_object* v_indVal_1566_, lean_object* v_rhs_1567_, lean_object* v_as_1568_, lean_object* v_as_x27_1569_, lean_object* v_b_1570_, lean_object* v_a_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5(v_indVal_1566_, v_rhs_1567_, v_as_1568_, v_as_x27_1569_, v_b_1570_, v_a_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v_as_1568_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1580_, lean_object* v_msg_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg(v_msg_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1590_, lean_object* v_msg_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0(v_00_u03b1_1590_, v_msg_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1600_, lean_object* v_macroStack_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1600_, v_macroStack_1601_, v___y_1606_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1610_, lean_object* v_macroStack_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__3(v_msgData_1610_, v_macroStack_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg(lean_object* v_a_1626_, lean_object* v___x_1627_, size_t v_sz_1628_, size_t v_i_1629_, lean_object* v_bs_1630_, lean_object* v___y_1631_){
_start:
{
uint8_t v___x_1633_; 
v___x_1633_ = lean_usize_dec_lt(v_i_1629_, v_sz_1628_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec_ref(v___y_1631_);
lean_dec(v___x_1627_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v_bs_1630_);
return v___x_1634_;
}
else
{
lean_object* v_v_1635_; lean_object* v_toConstantVal_1636_; lean_object* v_fst_1637_; lean_object* v_snd_1638_; lean_object* v_name_1639_; lean_object* v___x_1640_; lean_object* v_bs_x27_1641_; lean_object* v_a_1643_; uint8_t v___x_1648_; 
v_v_1635_ = lean_array_uget_borrowed(v_bs_1630_, v_i_1629_);
v_toConstantVal_1636_ = lean_ctor_get(v_a_1626_, 0);
v_fst_1637_ = lean_ctor_get(v_v_1635_, 0);
lean_inc(v_fst_1637_);
v_snd_1638_ = lean_ctor_get(v_v_1635_, 1);
lean_inc(v_snd_1638_);
v_name_1639_ = lean_ctor_get(v_toConstantVal_1636_, 0);
v___x_1640_ = lean_unsigned_to_nat(0u);
v_bs_x27_1641_ = lean_array_uset(v_bs_1630_, v_i_1629_, v___x_1640_);
v___x_1648_ = l_Lean_Expr_isAppOf(v_snd_1638_, v_name_1639_);
lean_dec(v_snd_1638_);
if (v___x_1648_ == 0)
{
lean_object* v_ref_1649_; lean_object* v_quotContext_1650_; lean_object* v_currMacroScope_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_ref_1649_ = lean_ctor_get(v___y_1631_, 5);
v_quotContext_1650_ = lean_ctor_get(v___y_1631_, 10);
v_currMacroScope_1651_ = lean_ctor_get(v___y_1631_, 11);
v___x_1652_ = l_Lean_SourceInfo_fromRef(v_ref_1649_, v___x_1648_);
v___x_1653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1654_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_1655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
lean_inc(v_currMacroScope_1651_);
lean_inc(v_quotContext_1650_);
v___x_1656_ = l_Lean_addMacroScope(v_quotContext_1650_, v___x_1655_, v_currMacroScope_1651_);
v___x_1657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1));
lean_inc(v___x_1652_);
v___x_1658_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1652_);
lean_ctor_set(v___x_1658_, 1, v___x_1654_);
lean_ctor_set(v___x_1658_, 2, v___x_1656_);
lean_ctor_set(v___x_1658_, 3, v___x_1657_);
v___x_1659_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1652_);
v___x_1660_ = l_Lean_Syntax_node1(v___x_1652_, v___x_1659_, v_fst_1637_);
v___x_1661_ = l_Lean_Syntax_node2(v___x_1652_, v___x_1653_, v___x_1658_, v___x_1660_);
v_a_1643_ = v___x_1661_;
goto v___jp_1642_;
}
else
{
lean_object* v_ref_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_ref_1662_ = lean_ctor_get(v___y_1631_, 5);
v___x_1663_ = 0;
v___x_1664_ = l_Lean_SourceInfo_fromRef(v_ref_1662_, v___x_1663_);
v___x_1665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1666_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1664_);
v___x_1667_ = l_Lean_Syntax_node1(v___x_1664_, v___x_1666_, v_fst_1637_);
lean_inc(v___x_1627_);
v___x_1668_ = l_Lean_Syntax_node2(v___x_1664_, v___x_1665_, v___x_1627_, v___x_1667_);
v_a_1643_ = v___x_1668_;
goto v___jp_1642_;
}
v___jp_1642_:
{
size_t v___x_1644_; size_t v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = ((size_t)1ULL);
v___x_1645_ = lean_usize_add(v_i_1629_, v___x_1644_);
v___x_1646_ = lean_array_uset(v_bs_x27_1641_, v_i_1629_, v_a_1643_);
v_i_1629_ = v___x_1645_;
v_bs_1630_ = v___x_1646_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___boxed(lean_object* v_a_1669_, lean_object* v___x_1670_, lean_object* v_sz_1671_, lean_object* v_i_1672_, lean_object* v_bs_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
size_t v_sz_boxed_1676_; size_t v_i_boxed_1677_; lean_object* v_res_1678_; 
v_sz_boxed_1676_ = lean_unbox_usize(v_sz_1671_);
lean_dec(v_sz_1671_);
v_i_boxed_1677_ = lean_unbox_usize(v_i_1672_);
lean_dec(v_i_1672_);
v_res_1678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg(v_a_1669_, v___x_1670_, v_sz_boxed_1676_, v_i_boxed_1677_, v_bs_1673_, v___y_1674_);
lean_dec_ref(v_a_1669_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2(lean_object* v_a_1679_, lean_object* v___x_1680_, size_t v_sz_1681_, size_t v_i_1682_, lean_object* v_bs_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
uint8_t v___x_1691_; 
v___x_1691_ = lean_usize_dec_lt(v_i_1682_, v_sz_1681_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
lean_dec_ref(v___y_1688_);
lean_dec(v___x_1680_);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_bs_1683_);
return v___x_1692_;
}
else
{
lean_object* v_v_1693_; lean_object* v_toConstantVal_1694_; lean_object* v_fst_1695_; lean_object* v_snd_1696_; lean_object* v_name_1697_; lean_object* v___x_1698_; lean_object* v_bs_x27_1699_; lean_object* v_a_1701_; uint8_t v___x_1706_; 
v_v_1693_ = lean_array_uget_borrowed(v_bs_1683_, v_i_1682_);
v_toConstantVal_1694_ = lean_ctor_get(v_a_1679_, 0);
v_fst_1695_ = lean_ctor_get(v_v_1693_, 0);
lean_inc(v_fst_1695_);
v_snd_1696_ = lean_ctor_get(v_v_1693_, 1);
lean_inc(v_snd_1696_);
v_name_1697_ = lean_ctor_get(v_toConstantVal_1694_, 0);
v___x_1698_ = lean_unsigned_to_nat(0u);
v_bs_x27_1699_ = lean_array_uset(v_bs_1683_, v_i_1682_, v___x_1698_);
v___x_1706_ = l_Lean_Expr_isAppOf(v_snd_1696_, v_name_1697_);
lean_dec(v_snd_1696_);
if (v___x_1706_ == 0)
{
lean_object* v_ref_1707_; lean_object* v_quotContext_1708_; lean_object* v_currMacroScope_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_ref_1707_ = lean_ctor_get(v___y_1688_, 5);
v_quotContext_1708_ = lean_ctor_get(v___y_1688_, 10);
v_currMacroScope_1709_ = lean_ctor_get(v___y_1688_, 11);
v___x_1710_ = l_Lean_SourceInfo_fromRef(v_ref_1707_, v___x_1706_);
v___x_1711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1712_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_1713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
lean_inc(v_currMacroScope_1709_);
lean_inc(v_quotContext_1708_);
v___x_1714_ = l_Lean_addMacroScope(v_quotContext_1708_, v___x_1713_, v_currMacroScope_1709_);
v___x_1715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1));
lean_inc(v___x_1710_);
v___x_1716_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1710_);
lean_ctor_set(v___x_1716_, 1, v___x_1712_);
lean_ctor_set(v___x_1716_, 2, v___x_1714_);
lean_ctor_set(v___x_1716_, 3, v___x_1715_);
v___x_1717_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1710_);
v___x_1718_ = l_Lean_Syntax_node1(v___x_1710_, v___x_1717_, v_fst_1695_);
v___x_1719_ = l_Lean_Syntax_node2(v___x_1710_, v___x_1711_, v___x_1716_, v___x_1718_);
v_a_1701_ = v___x_1719_;
goto v___jp_1700_;
}
else
{
lean_object* v_ref_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_ref_1720_ = lean_ctor_get(v___y_1688_, 5);
v___x_1721_ = 0;
v___x_1722_ = l_Lean_SourceInfo_fromRef(v_ref_1720_, v___x_1721_);
v___x_1723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1724_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1722_);
v___x_1725_ = l_Lean_Syntax_node1(v___x_1722_, v___x_1724_, v_fst_1695_);
lean_inc(v___x_1680_);
v___x_1726_ = l_Lean_Syntax_node2(v___x_1722_, v___x_1723_, v___x_1680_, v___x_1725_);
v_a_1701_ = v___x_1726_;
goto v___jp_1700_;
}
v___jp_1700_:
{
size_t v___x_1702_; size_t v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1702_ = ((size_t)1ULL);
v___x_1703_ = lean_usize_add(v_i_1682_, v___x_1702_);
v___x_1704_ = lean_array_uset(v_bs_x27_1699_, v_i_1682_, v_a_1701_);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg(v_a_1679_, v___x_1680_, v_sz_1681_, v___x_1703_, v___x_1704_, v___y_1688_);
return v___x_1705_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2___boxed(lean_object* v_a_1727_, lean_object* v___x_1728_, lean_object* v_sz_1729_, lean_object* v_i_1730_, lean_object* v_bs_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
size_t v_sz_boxed_1739_; size_t v_i_boxed_1740_; lean_object* v_res_1741_; 
v_sz_boxed_1739_ = lean_unbox_usize(v_sz_1729_);
lean_dec(v_sz_1729_);
v_i_boxed_1740_ = lean_unbox_usize(v_i_1730_);
lean_dec(v_i_1730_);
v_res_1741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2(v_a_1727_, v___x_1728_, v_sz_boxed_1739_, v_i_boxed_1740_, v_bs_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec_ref(v_a_1727_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___redArg(lean_object* v_userNames_1742_, lean_object* v_a_1743_, lean_object* v___x_1744_, lean_object* v_as_1745_, lean_object* v_i_1746_, lean_object* v_j_1747_, lean_object* v_bs_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_zero_1751_; uint8_t v_isZero_1752_; 
v_zero_1751_ = lean_unsigned_to_nat(0u);
v_isZero_1752_ = lean_nat_dec_eq(v_i_1746_, v_zero_1751_);
if (v_isZero_1752_ == 1)
{
lean_object* v___x_1753_; 
lean_dec_ref(v___y_1749_);
lean_dec(v_j_1747_);
lean_dec(v_i_1746_);
lean_dec(v___x_1744_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_bs_1748_);
return v___x_1753_;
}
else
{
lean_object* v___x_1754_; lean_object* v_toConstantVal_1755_; lean_object* v_fst_1756_; lean_object* v_snd_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1820_; 
v___x_1754_ = lean_array_fget(v_as_1745_, v_j_1747_);
v_toConstantVal_1755_ = lean_ctor_get(v_a_1743_, 0);
v_fst_1756_ = lean_ctor_get(v___x_1754_, 0);
v_snd_1757_ = lean_ctor_get(v___x_1754_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1759_ = v___x_1754_;
v_isShared_1760_ = v_isSharedCheck_1820_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_snd_1757_);
lean_inc(v_fst_1756_);
lean_dec(v___x_1754_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1820_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v_name_1761_; lean_object* v___x_1762_; lean_object* v_one_1763_; lean_object* v_n_1764_; lean_object* v_a_1766_; uint8_t v___x_1800_; 
v_name_1761_ = lean_ctor_get(v_toConstantVal_1755_, 0);
v___x_1762_ = lean_box(0);
v_one_1763_ = lean_unsigned_to_nat(1u);
v_n_1764_ = lean_nat_sub(v_i_1746_, v_one_1763_);
lean_dec(v_i_1746_);
v___x_1800_ = l_Lean_Expr_isAppOf(v_snd_1757_, v_name_1761_);
lean_dec(v_snd_1757_);
if (v___x_1800_ == 0)
{
lean_object* v_ref_1801_; lean_object* v_quotContext_1802_; lean_object* v_currMacroScope_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_ref_1801_ = lean_ctor_get(v___y_1749_, 5);
v_quotContext_1802_ = lean_ctor_get(v___y_1749_, 10);
v_currMacroScope_1803_ = lean_ctor_get(v___y_1749_, 11);
v___x_1804_ = l_Lean_SourceInfo_fromRef(v_ref_1801_, v___x_1800_);
v___x_1805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1806_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_1807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
lean_inc(v_currMacroScope_1803_);
lean_inc(v_quotContext_1802_);
v___x_1808_ = l_Lean_addMacroScope(v_quotContext_1802_, v___x_1807_, v_currMacroScope_1803_);
v___x_1809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1));
lean_inc(v___x_1804_);
v___x_1810_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1804_);
lean_ctor_set(v___x_1810_, 1, v___x_1806_);
lean_ctor_set(v___x_1810_, 2, v___x_1808_);
lean_ctor_set(v___x_1810_, 3, v___x_1809_);
v___x_1811_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1804_);
v___x_1812_ = l_Lean_Syntax_node1(v___x_1804_, v___x_1811_, v_fst_1756_);
v___x_1813_ = l_Lean_Syntax_node2(v___x_1804_, v___x_1805_, v___x_1810_, v___x_1812_);
v_a_1766_ = v___x_1813_;
goto v___jp_1765_;
}
else
{
lean_object* v_ref_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_ref_1814_ = lean_ctor_get(v___y_1749_, 5);
v___x_1815_ = l_Lean_SourceInfo_fromRef(v_ref_1814_, v_isZero_1752_);
v___x_1816_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1817_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1815_);
v___x_1818_ = l_Lean_Syntax_node1(v___x_1815_, v___x_1817_, v_fst_1756_);
lean_inc(v___x_1744_);
v___x_1819_ = l_Lean_Syntax_node2(v___x_1815_, v___x_1816_, v___x_1744_, v___x_1818_);
v_a_1766_ = v___x_1819_;
goto v___jp_1765_;
}
v___jp_1765_:
{
lean_object* v_ref_1767_; lean_object* v_quotContext_1768_; lean_object* v_currMacroScope_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v_ref_1767_ = lean_ctor_get(v___y_1749_, 5);
v_quotContext_1768_ = lean_ctor_get(v___y_1749_, 10);
v_currMacroScope_1769_ = lean_ctor_get(v___y_1749_, 11);
v___x_1770_ = l_Lean_SourceInfo_fromRef(v_ref_1767_, v_isZero_1752_);
v___x_1771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4));
v___x_1772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_1773_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_1770_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set_tag(v___x_1759_, 2);
lean_ctor_set(v___x_1759_, 1, v___x_1773_);
lean_ctor_set(v___x_1759_, 0, v___x_1770_);
v___x_1775_ = v___x_1759_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_1777_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
lean_inc(v_currMacroScope_1769_);
lean_inc(v_quotContext_1768_);
v___x_1778_ = l_Lean_addMacroScope(v_quotContext_1768_, v___x_1762_, v_currMacroScope_1769_);
v___x_1779_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__28));
lean_inc(v___x_1770_);
v___x_1780_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1770_);
lean_ctor_set(v___x_1780_, 1, v___x_1777_);
lean_ctor_set(v___x_1780_, 2, v___x_1778_);
lean_ctor_set(v___x_1780_, 3, v___x_1779_);
lean_inc(v___x_1770_);
v___x_1781_ = l_Lean_Syntax_node1(v___x_1770_, v___x_1776_, v___x_1780_);
lean_inc(v___x_1770_);
v___x_1782_ = l_Lean_Syntax_node2(v___x_1770_, v___x_1772_, v___x_1775_, v___x_1781_);
v___x_1783_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_1784_ = lean_array_get_borrowed(v___x_1762_, v_userNames_1742_, v_j_1747_);
lean_inc(v___x_1784_);
v___x_1785_ = lean_erase_macro_scopes(v___x_1784_);
v___x_1786_ = l_Lean_Name_getString_x21(v___x_1785_);
lean_dec(v___x_1785_);
v___x_1787_ = lean_box(2);
v___x_1788_ = l_Lean_Syntax_mkStrLit(v___x_1786_, v___x_1787_);
v___x_1789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
lean_inc(v___x_1770_);
v___x_1790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1770_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
lean_inc(v___x_1770_);
v___x_1791_ = l_Lean_Syntax_node1(v___x_1770_, v___x_1783_, v_a_1766_);
lean_inc(v___x_1770_);
v___x_1792_ = l_Lean_Syntax_node3(v___x_1770_, v___x_1783_, v___x_1788_, v___x_1790_, v___x_1791_);
v___x_1793_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_1770_);
v___x_1794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1770_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = l_Lean_Syntax_node3(v___x_1770_, v___x_1771_, v___x_1782_, v___x_1792_, v___x_1794_);
v___x_1796_ = lean_nat_add(v_j_1747_, v_one_1763_);
lean_dec(v_j_1747_);
v___x_1797_ = lean_array_push(v_bs_1748_, v___x_1795_);
v_i_1746_ = v_n_1764_;
v_j_1747_ = v___x_1796_;
v_bs_1748_ = v___x_1797_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___redArg___boxed(lean_object* v_userNames_1821_, lean_object* v_a_1822_, lean_object* v___x_1823_, lean_object* v_as_1824_, lean_object* v_i_1825_, lean_object* v_j_1826_, lean_object* v_bs_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___redArg(v_userNames_1821_, v_a_1822_, v___x_1823_, v_as_1824_, v_i_1825_, v_j_1826_, v_bs_1827_, v___y_1828_);
lean_dec_ref(v_as_1824_);
lean_dec_ref(v_a_1822_);
lean_dec_ref(v_userNames_1821_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___redArg(lean_object* v_a_1831_, lean_object* v___x_1832_, lean_object* v_userNames_1833_, lean_object* v_as_1834_, lean_object* v_i_1835_, lean_object* v_j_1836_, lean_object* v_bs_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_zero_1845_; uint8_t v_isZero_1846_; 
v_zero_1845_ = lean_unsigned_to_nat(0u);
v_isZero_1846_ = lean_nat_dec_eq(v_i_1835_, v_zero_1845_);
if (v_isZero_1846_ == 1)
{
lean_object* v___x_1847_; 
lean_dec_ref(v___y_1842_);
lean_dec(v___x_1832_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_bs_1837_);
return v___x_1847_;
}
else
{
lean_object* v___x_1848_; lean_object* v_toConstantVal_1849_; lean_object* v_fst_1850_; lean_object* v_snd_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1914_; 
v___x_1848_ = lean_array_fget(v_as_1834_, v_j_1836_);
v_toConstantVal_1849_ = lean_ctor_get(v_a_1831_, 0);
v_fst_1850_ = lean_ctor_get(v___x_1848_, 0);
v_snd_1851_ = lean_ctor_get(v___x_1848_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1853_ = v___x_1848_;
v_isShared_1854_ = v_isSharedCheck_1914_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_snd_1851_);
lean_inc(v_fst_1850_);
lean_dec(v___x_1848_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1914_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_name_1855_; lean_object* v___x_1856_; lean_object* v_one_1857_; lean_object* v_n_1858_; lean_object* v_a_1860_; uint8_t v___x_1894_; 
v_name_1855_ = lean_ctor_get(v_toConstantVal_1849_, 0);
v___x_1856_ = lean_box(0);
v_one_1857_ = lean_unsigned_to_nat(1u);
v_n_1858_ = lean_nat_sub(v_i_1835_, v_one_1857_);
v___x_1894_ = l_Lean_Expr_isAppOf(v_snd_1851_, v_name_1855_);
lean_dec(v_snd_1851_);
if (v___x_1894_ == 0)
{
lean_object* v_ref_1895_; lean_object* v_quotContext_1896_; lean_object* v_currMacroScope_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v_ref_1895_ = lean_ctor_get(v___y_1842_, 5);
v_quotContext_1896_ = lean_ctor_get(v___y_1842_, 10);
v_currMacroScope_1897_ = lean_ctor_get(v___y_1842_, 11);
v___x_1898_ = l_Lean_SourceInfo_fromRef(v_ref_1895_, v___x_1894_);
v___x_1899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1900_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_1901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
lean_inc(v_currMacroScope_1897_);
lean_inc(v_quotContext_1896_);
v___x_1902_ = l_Lean_addMacroScope(v_quotContext_1896_, v___x_1901_, v_currMacroScope_1897_);
v___x_1903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1));
lean_inc(v___x_1898_);
v___x_1904_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1898_);
lean_ctor_set(v___x_1904_, 1, v___x_1900_);
lean_ctor_set(v___x_1904_, 2, v___x_1902_);
lean_ctor_set(v___x_1904_, 3, v___x_1903_);
v___x_1905_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1898_);
v___x_1906_ = l_Lean_Syntax_node1(v___x_1898_, v___x_1905_, v_fst_1850_);
v___x_1907_ = l_Lean_Syntax_node2(v___x_1898_, v___x_1899_, v___x_1904_, v___x_1906_);
v_a_1860_ = v___x_1907_;
goto v___jp_1859_;
}
else
{
lean_object* v_ref_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_ref_1908_ = lean_ctor_get(v___y_1842_, 5);
v___x_1909_ = l_Lean_SourceInfo_fromRef(v_ref_1908_, v_isZero_1846_);
v___x_1910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_1911_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_1909_);
v___x_1912_ = l_Lean_Syntax_node1(v___x_1909_, v___x_1911_, v_fst_1850_);
lean_inc(v___x_1832_);
v___x_1913_ = l_Lean_Syntax_node2(v___x_1909_, v___x_1910_, v___x_1832_, v___x_1912_);
v_a_1860_ = v___x_1913_;
goto v___jp_1859_;
}
v___jp_1859_:
{
lean_object* v_ref_1861_; lean_object* v_quotContext_1862_; lean_object* v_currMacroScope_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v_ref_1861_ = lean_ctor_get(v___y_1842_, 5);
v_quotContext_1862_ = lean_ctor_get(v___y_1842_, 10);
v_currMacroScope_1863_ = lean_ctor_get(v___y_1842_, 11);
v___x_1864_ = l_Lean_SourceInfo_fromRef(v_ref_1861_, v_isZero_1846_);
v___x_1865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4));
v___x_1866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_1867_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_1864_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 2);
lean_ctor_set(v___x_1853_, 1, v___x_1867_);
lean_ctor_set(v___x_1853_, 0, v___x_1864_);
v___x_1869_ = v___x_1853_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_1871_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
lean_inc(v_currMacroScope_1863_);
lean_inc(v_quotContext_1862_);
v___x_1872_ = l_Lean_addMacroScope(v_quotContext_1862_, v___x_1856_, v_currMacroScope_1863_);
v___x_1873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__28));
lean_inc(v___x_1864_);
v___x_1874_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1864_);
lean_ctor_set(v___x_1874_, 1, v___x_1871_);
lean_ctor_set(v___x_1874_, 2, v___x_1872_);
lean_ctor_set(v___x_1874_, 3, v___x_1873_);
lean_inc(v___x_1864_);
v___x_1875_ = l_Lean_Syntax_node1(v___x_1864_, v___x_1870_, v___x_1874_);
lean_inc(v___x_1864_);
v___x_1876_ = l_Lean_Syntax_node2(v___x_1864_, v___x_1866_, v___x_1869_, v___x_1875_);
v___x_1877_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_1878_ = lean_array_get_borrowed(v___x_1856_, v_userNames_1833_, v_j_1836_);
lean_inc(v___x_1878_);
v___x_1879_ = lean_erase_macro_scopes(v___x_1878_);
v___x_1880_ = l_Lean_Name_getString_x21(v___x_1879_);
lean_dec(v___x_1879_);
v___x_1881_ = lean_box(2);
v___x_1882_ = l_Lean_Syntax_mkStrLit(v___x_1880_, v___x_1881_);
v___x_1883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
lean_inc(v___x_1864_);
v___x_1884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1864_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
lean_inc(v___x_1864_);
v___x_1885_ = l_Lean_Syntax_node1(v___x_1864_, v___x_1877_, v_a_1860_);
lean_inc(v___x_1864_);
v___x_1886_ = l_Lean_Syntax_node3(v___x_1864_, v___x_1877_, v___x_1882_, v___x_1884_, v___x_1885_);
v___x_1887_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_1864_);
v___x_1888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1864_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = l_Lean_Syntax_node3(v___x_1864_, v___x_1865_, v___x_1876_, v___x_1886_, v___x_1888_);
v___x_1890_ = lean_nat_add(v_j_1836_, v_one_1857_);
v___x_1891_ = lean_array_push(v_bs_1837_, v___x_1889_);
v___x_1892_ = l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___redArg(v_userNames_1833_, v_a_1831_, v___x_1832_, v_as_1834_, v_n_1858_, v___x_1890_, v___x_1891_, v___y_1842_);
return v___x_1892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___redArg___boxed(lean_object* v_a_1915_, lean_object* v___x_1916_, lean_object* v_userNames_1917_, lean_object* v_as_1918_, lean_object* v_i_1919_, lean_object* v_j_1920_, lean_object* v_bs_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___redArg(v_a_1915_, v___x_1916_, v_userNames_1917_, v_as_1918_, v_i_1919_, v_j_1920_, v_bs_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v_j_1920_);
lean_dec(v_i_1919_);
lean_dec_ref(v_as_1918_);
lean_dec_ref(v_userNames_1917_);
lean_dec_ref(v_a_1915_);
return v_res_1929_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__5));
v___x_1947_ = l_String_toRawSubstring_x27(v___x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0(lean_object* v___x_1971_, lean_object* v_a_1972_, lean_object* v___x_1973_, lean_object* v_ctor_1974_, lean_object* v_args_1975_, lean_object* v_userNames_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_toConstantVal_1984_; lean_object* v_name_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2237_; 
v_toConstantVal_1984_ = lean_ctor_get(v_ctor_1974_, 0);
lean_inc_ref(v_toConstantVal_1984_);
lean_dec_ref(v_ctor_1974_);
v_name_1985_ = lean_ctor_get(v_toConstantVal_1984_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_toConstantVal_1984_);
if (v_isSharedCheck_2237_ == 0)
{
lean_object* v_unused_2238_; lean_object* v_unused_2239_; 
v_unused_2238_ = lean_ctor_get(v_toConstantVal_1984_, 2);
lean_dec(v_unused_2238_);
v_unused_2239_ = lean_ctor_get(v_toConstantVal_1984_, 1);
lean_dec(v_unused_2239_);
v___x_1987_ = v_toConstantVal_1984_;
v_isShared_1988_ = v_isSharedCheck_2237_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_name_1985_);
lean_dec(v_toConstantVal_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2237_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; lean_object* v_a_1994_; lean_object* v_xs_2038_; lean_object* v_userNames_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; 
v___x_1989_ = lean_erase_macro_scopes(v_name_1985_);
v___x_1990_ = l_Lean_Name_getString_x21(v___x_1989_);
lean_dec(v___x_1989_);
v___x_1991_ = lean_array_get_size(v_args_1975_);
v___x_1992_ = lean_nat_dec_eq(v___x_1991_, v___x_1971_);
if (v___x_1992_ == 0)
{
lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2111_ = lean_unsigned_to_nat(1u);
v___x_2112_ = lean_nat_dec_eq(v___x_1991_, v___x_2111_);
if (v___x_2112_ == 0)
{
if (lean_obj_tag(v_userNames_1976_) == 0)
{
size_t v_sz_2113_; size_t v___x_2114_; lean_object* v___x_2115_; 
lean_del_object(v___x_1987_);
v_sz_2113_ = lean_array_size(v_args_1975_);
v___x_2114_ = ((size_t)0ULL);
lean_inc_ref(v___y_1981_);
v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2(v_a_1972_, v___x_1973_, v_sz_2113_, v___x_2114_, v_args_1975_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2182_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2182_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2182_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_ref_2120_; lean_object* v_quotContext_2121_; lean_object* v_currMacroScope_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; size_t v_sz_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2180_; 
v_ref_2120_ = lean_ctor_get(v___y_1981_, 5);
lean_inc(v_ref_2120_);
v_quotContext_2121_ = lean_ctor_get(v___y_1981_, 10);
lean_inc(v_quotContext_2121_);
v_currMacroScope_2122_ = lean_ctor_get(v___y_1981_, 11);
lean_inc(v_currMacroScope_2122_);
lean_dec_ref(v___y_1981_);
v___x_2123_ = l_Lean_SourceInfo_fromRef(v_ref_2120_, v___x_2112_);
lean_dec(v_ref_2120_);
v___x_2124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2125_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3, &l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3_once, _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3);
v___x_2126_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__4));
lean_inc(v_currMacroScope_2122_);
lean_inc(v_quotContext_2121_);
v___x_2127_ = l_Lean_addMacroScope(v_quotContext_2121_, v___x_2126_, v_currMacroScope_2122_);
v___x_2128_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__7));
lean_inc(v___x_2123_);
v___x_2129_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2123_);
lean_ctor_set(v___x_2129_, 1, v___x_2125_);
lean_ctor_set(v___x_2129_, 2, v___x_2127_);
lean_ctor_set(v___x_2129_, 3, v___x_2128_);
v___x_2130_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1));
v___x_2132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_2123_);
v___x_2133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2123_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4));
v___x_2135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_2136_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_2123_);
v___x_2137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2123_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_2139_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
v___x_2140_ = lean_box(0);
lean_inc(v_currMacroScope_2122_);
lean_inc(v_quotContext_2121_);
v___x_2141_ = l_Lean_addMacroScope(v_quotContext_2121_, v___x_2140_, v_currMacroScope_2122_);
v___x_2142_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__4));
lean_inc(v___x_2123_);
v___x_2143_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2123_);
lean_ctor_set(v___x_2143_, 1, v___x_2139_);
lean_ctor_set(v___x_2143_, 2, v___x_2141_);
lean_ctor_set(v___x_2143_, 3, v___x_2142_);
lean_inc(v___x_2123_);
v___x_2144_ = l_Lean_Syntax_node1(v___x_2123_, v___x_2138_, v___x_2143_);
lean_inc(v___x_2123_);
v___x_2145_ = l_Lean_Syntax_node2(v___x_2123_, v___x_2135_, v___x_2137_, v___x_2144_);
v___x_2146_ = lean_box(2);
v___x_2147_ = l_Lean_Syntax_mkStrLit(v___x_1990_, v___x_2146_);
v___x_2148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
lean_inc(v___x_2123_);
v___x_2149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2123_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__6, &l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__6_once, _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__6);
v___x_2151_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__8));
v___x_2152_ = l_Lean_addMacroScope(v_quotContext_2121_, v___x_2151_, v_currMacroScope_2122_);
v___x_2153_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__13));
lean_inc(v___x_2123_);
v___x_2154_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2123_);
lean_ctor_set(v___x_2154_, 1, v___x_2150_);
lean_ctor_set(v___x_2154_, 2, v___x_2152_);
lean_ctor_set(v___x_2154_, 3, v___x_2153_);
v___x_2155_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__15));
v___x_2156_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__16));
lean_inc(v___x_2123_);
v___x_2157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2123_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v_sz_2159_ = lean_array_size(v_a_2116_);
v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(v_sz_2159_, v___x_2114_, v_a_2116_);
v___x_2161_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6);
v___x_2162_ = l_Lean_mkSepArray(v___x_2160_, v___x_2161_);
lean_dec_ref(v___x_2160_);
v___x_2163_ = l_Array_append___redArg(v___x_2158_, v___x_2162_);
lean_dec_ref(v___x_2162_);
lean_inc(v___x_2123_);
v___x_2164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2123_);
lean_ctor_set(v___x_2164_, 1, v___x_2130_);
lean_ctor_set(v___x_2164_, 2, v___x_2163_);
v___x_2165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_2123_);
v___x_2166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2123_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
lean_inc_ref(v___x_2166_);
lean_inc(v___x_2123_);
v___x_2167_ = l_Lean_Syntax_node3(v___x_2123_, v___x_2155_, v___x_2157_, v___x_2164_, v___x_2166_);
lean_inc(v___x_2123_);
v___x_2168_ = l_Lean_Syntax_node1(v___x_2123_, v___x_2130_, v___x_2167_);
lean_inc(v___x_2123_);
v___x_2169_ = l_Lean_Syntax_node2(v___x_2123_, v___x_2124_, v___x_2154_, v___x_2168_);
lean_inc(v___x_2123_);
v___x_2170_ = l_Lean_Syntax_node1(v___x_2123_, v___x_2130_, v___x_2169_);
lean_inc(v___x_2123_);
v___x_2171_ = l_Lean_Syntax_node3(v___x_2123_, v___x_2130_, v___x_2147_, v___x_2149_, v___x_2170_);
v___x_2172_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_2123_);
v___x_2173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2123_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
lean_inc(v___x_2123_);
v___x_2174_ = l_Lean_Syntax_node3(v___x_2123_, v___x_2134_, v___x_2145_, v___x_2171_, v___x_2173_);
lean_inc(v___x_2123_);
v___x_2175_ = l_Lean_Syntax_node1(v___x_2123_, v___x_2130_, v___x_2174_);
lean_inc(v___x_2123_);
v___x_2176_ = l_Lean_Syntax_node3(v___x_2123_, v___x_2131_, v___x_2133_, v___x_2175_, v___x_2166_);
lean_inc(v___x_2123_);
v___x_2177_ = l_Lean_Syntax_node1(v___x_2123_, v___x_2130_, v___x_2176_);
v___x_2178_ = l_Lean_Syntax_node2(v___x_2123_, v___x_2124_, v___x_2129_, v___x_2177_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2178_);
v___x_2180_ = v___x_2118_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec_ref(v___x_1990_);
lean_dec_ref(v___y_1981_);
v_a_2183_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2115_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2115_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
else
{
lean_object* v_val_2191_; 
v_val_2191_ = lean_ctor_get(v_userNames_1976_, 0);
v_xs_2038_ = v_args_1975_;
v_userNames_2039_ = v_val_2191_;
v___y_2040_ = v___y_1977_;
v___y_2041_ = v___y_1978_;
v___y_2042_ = v___y_1979_;
v___y_2043_ = v___y_1980_;
v___y_2044_ = v___y_1981_;
v___y_2045_ = v___y_1982_;
goto v___jp_2037_;
}
}
else
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_array_fget(v_args_1975_, v___x_1971_);
lean_dec_ref(v_args_1975_);
if (lean_obj_tag(v_userNames_1976_) == 0)
{
lean_object* v_toConstantVal_2193_; lean_object* v_fst_2194_; lean_object* v_snd_2195_; lean_object* v_name_2196_; uint8_t v___x_2197_; 
lean_del_object(v___x_1987_);
v_toConstantVal_2193_ = lean_ctor_get(v_a_1972_, 0);
v_fst_2194_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_fst_2194_);
v_snd_2195_ = lean_ctor_get(v___x_2192_, 1);
lean_inc(v_snd_2195_);
lean_dec(v___x_2192_);
v_name_2196_ = lean_ctor_get(v_toConstantVal_2193_, 0);
v___x_2197_ = l_Lean_Expr_isAppOf(v_snd_2195_, v_name_2196_);
lean_dec(v_snd_2195_);
if (v___x_2197_ == 0)
{
lean_object* v_ref_2198_; lean_object* v_quotContext_2199_; lean_object* v_currMacroScope_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec(v___x_1973_);
v_ref_2198_ = lean_ctor_get(v___y_1981_, 5);
v_quotContext_2199_ = lean_ctor_get(v___y_1981_, 10);
v_currMacroScope_2200_ = lean_ctor_get(v___y_1981_, 11);
v___x_2201_ = l_Lean_SourceInfo_fromRef(v_ref_2198_, v___x_2197_);
v___x_2202_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2203_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_2204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
lean_inc(v_currMacroScope_2200_);
lean_inc(v_quotContext_2199_);
v___x_2205_ = l_Lean_addMacroScope(v_quotContext_2199_, v___x_2204_, v_currMacroScope_2200_);
v___x_2206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1));
lean_inc(v___x_2201_);
v___x_2207_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2201_);
lean_ctor_set(v___x_2207_, 1, v___x_2203_);
lean_ctor_set(v___x_2207_, 2, v___x_2205_);
lean_ctor_set(v___x_2207_, 3, v___x_2206_);
v___x_2208_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_2201_);
v___x_2209_ = l_Lean_Syntax_node1(v___x_2201_, v___x_2208_, v_fst_2194_);
v___x_2210_ = l_Lean_Syntax_node2(v___x_2201_, v___x_2202_, v___x_2207_, v___x_2209_);
v_a_1994_ = v___x_2210_;
goto v___jp_1993_;
}
else
{
lean_object* v_ref_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v_ref_2211_ = lean_ctor_get(v___y_1981_, 5);
v___x_2212_ = l_Lean_SourceInfo_fromRef(v_ref_2211_, v___x_1992_);
v___x_2213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2214_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
lean_inc(v___x_2212_);
v___x_2215_ = l_Lean_Syntax_node1(v___x_2212_, v___x_2214_, v_fst_2194_);
v___x_2216_ = l_Lean_Syntax_node2(v___x_2212_, v___x_2213_, v___x_1973_, v___x_2215_);
v_a_1994_ = v___x_2216_;
goto v___jp_1993_;
}
}
else
{
lean_object* v_val_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v_val_2217_ = lean_ctor_get(v_userNames_1976_, 0);
v___x_2218_ = lean_mk_empty_array_with_capacity(v___x_2111_);
v___x_2219_ = lean_array_push(v___x_2218_, v___x_2192_);
v_xs_2038_ = v___x_2219_;
v_userNames_2039_ = v_val_2217_;
v___y_2040_ = v___y_1977_;
v___y_2041_ = v___y_1978_;
v___y_2042_ = v___y_1979_;
v___y_2043_ = v___y_1980_;
v___y_2044_ = v___y_1981_;
v___y_2045_ = v___y_1982_;
goto v___jp_2037_;
}
}
}
else
{
lean_object* v_ref_2220_; lean_object* v_quotContext_2221_; lean_object* v_currMacroScope_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_del_object(v___x_1987_);
lean_dec_ref(v_args_1975_);
lean_dec(v___x_1973_);
v_ref_2220_ = lean_ctor_get(v___y_1981_, 5);
lean_inc(v_ref_2220_);
v_quotContext_2221_ = lean_ctor_get(v___y_1981_, 10);
lean_inc(v_quotContext_2221_);
v_currMacroScope_2222_ = lean_ctor_get(v___y_1981_, 11);
lean_inc(v_currMacroScope_2222_);
lean_dec_ref(v___y_1981_);
v___x_2223_ = 0;
v___x_2224_ = l_Lean_SourceInfo_fromRef(v_ref_2220_, v___x_2223_);
lean_dec(v_ref_2220_);
v___x_2225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2226_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__33);
v___x_2227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__34));
v___x_2228_ = l_Lean_addMacroScope(v_quotContext_2221_, v___x_2227_, v_currMacroScope_2222_);
v___x_2229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg___closed__1));
lean_inc(v___x_2224_);
v___x_2230_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2224_);
lean_ctor_set(v___x_2230_, 1, v___x_2226_);
lean_ctor_set(v___x_2230_, 2, v___x_2228_);
lean_ctor_set(v___x_2230_, 3, v___x_2229_);
v___x_2231_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2232_ = lean_box(2);
v___x_2233_ = l_Lean_Syntax_mkStrLit(v___x_1990_, v___x_2232_);
lean_inc(v___x_2224_);
v___x_2234_ = l_Lean_Syntax_node1(v___x_2224_, v___x_2231_, v___x_2233_);
v___x_2235_ = l_Lean_Syntax_node2(v___x_2224_, v___x_2225_, v___x_2230_, v___x_2234_);
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
v___jp_1993_:
{
lean_object* v_ref_1995_; lean_object* v_quotContext_1996_; lean_object* v_currMacroScope_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v_ref_1995_ = lean_ctor_get(v___y_1981_, 5);
lean_inc(v_ref_1995_);
v_quotContext_1996_ = lean_ctor_get(v___y_1981_, 10);
lean_inc(v_quotContext_1996_);
v_currMacroScope_1997_ = lean_ctor_get(v___y_1981_, 11);
lean_inc(v_currMacroScope_1997_);
lean_dec_ref(v___y_1981_);
v___x_1998_ = l_Lean_SourceInfo_fromRef(v_ref_1995_, v___x_1992_);
lean_dec(v_ref_1995_);
v___x_1999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2000_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3, &l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3_once, _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3);
v___x_2001_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__4));
lean_inc(v_currMacroScope_1997_);
lean_inc(v_quotContext_1996_);
v___x_2002_ = l_Lean_addMacroScope(v_quotContext_1996_, v___x_2001_, v_currMacroScope_1997_);
v___x_2003_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__7));
lean_inc(v___x_1998_);
v___x_2004_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2004_, 0, v___x_1998_);
lean_ctor_set(v___x_2004_, 1, v___x_2000_);
lean_ctor_set(v___x_2004_, 2, v___x_2002_);
lean_ctor_set(v___x_2004_, 3, v___x_2003_);
v___x_2005_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1));
v___x_2007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_1998_);
v___x_2008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_1998_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4));
v___x_2010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_2011_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_1998_);
v___x_2012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_1998_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_2014_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
v___x_2015_ = lean_box(0);
v___x_2016_ = l_Lean_addMacroScope(v_quotContext_1996_, v___x_2015_, v_currMacroScope_1997_);
v___x_2017_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__4));
lean_inc(v___x_1998_);
v___x_2018_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2018_, 0, v___x_1998_);
lean_ctor_set(v___x_2018_, 1, v___x_2014_);
lean_ctor_set(v___x_2018_, 2, v___x_2016_);
lean_ctor_set(v___x_2018_, 3, v___x_2017_);
lean_inc(v___x_1998_);
v___x_2019_ = l_Lean_Syntax_node1(v___x_1998_, v___x_2013_, v___x_2018_);
lean_inc(v___x_1998_);
v___x_2020_ = l_Lean_Syntax_node2(v___x_1998_, v___x_2010_, v___x_2012_, v___x_2019_);
v___x_2021_ = lean_box(2);
v___x_2022_ = l_Lean_Syntax_mkStrLit(v___x_1990_, v___x_2021_);
v___x_2023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
lean_inc(v___x_1998_);
v___x_2024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_1998_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
lean_inc(v___x_1998_);
v___x_2025_ = l_Lean_Syntax_node1(v___x_1998_, v___x_2005_, v_a_1994_);
lean_inc(v___x_1998_);
v___x_2026_ = l_Lean_Syntax_node3(v___x_1998_, v___x_2005_, v___x_2022_, v___x_2024_, v___x_2025_);
v___x_2027_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_1998_);
v___x_2028_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_1998_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
lean_inc(v___x_1998_);
v___x_2029_ = l_Lean_Syntax_node3(v___x_1998_, v___x_2009_, v___x_2020_, v___x_2026_, v___x_2028_);
lean_inc(v___x_1998_);
v___x_2030_ = l_Lean_Syntax_node1(v___x_1998_, v___x_2005_, v___x_2029_);
v___x_2031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_1998_);
v___x_2032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_1998_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
lean_inc(v___x_1998_);
v___x_2033_ = l_Lean_Syntax_node3(v___x_1998_, v___x_2006_, v___x_2008_, v___x_2030_, v___x_2032_);
lean_inc(v___x_1998_);
v___x_2034_ = l_Lean_Syntax_node1(v___x_1998_, v___x_2005_, v___x_2033_);
v___x_2035_ = l_Lean_Syntax_node2(v___x_1998_, v___x_1999_, v___x_2004_, v___x_2034_);
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
return v___x_2036_;
}
v___jp_2037_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2110_; 
v___x_2046_ = lean_array_get_size(v_xs_2038_);
v___x_2047_ = lean_mk_empty_array_with_capacity(v___x_2046_);
lean_inc_ref(v___y_2044_);
v___x_2048_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___redArg(v_a_1972_, v___x_1973_, v_userNames_2039_, v_xs_2038_, v___x_2046_, v___x_1971_, v___x_2047_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec_ref(v_xs_2038_);
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2110_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2110_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_ref_2053_; lean_object* v_quotContext_2054_; lean_object* v_currMacroScope_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; size_t v_sz_2084_; size_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v_ref_2053_ = lean_ctor_get(v___y_2044_, 5);
lean_inc(v_ref_2053_);
v_quotContext_2054_ = lean_ctor_get(v___y_2044_, 10);
lean_inc(v_quotContext_2054_);
v_currMacroScope_2055_ = lean_ctor_get(v___y_2044_, 11);
lean_inc(v_currMacroScope_2055_);
lean_dec_ref(v___y_2044_);
v___x_2056_ = l_Lean_SourceInfo_fromRef(v_ref_2053_, v___x_1992_);
lean_dec(v_ref_2053_);
v___x_2057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2058_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3, &l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3_once, _init_l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__3);
v___x_2059_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__4));
lean_inc(v_currMacroScope_2055_);
lean_inc(v_quotContext_2054_);
v___x_2060_ = l_Lean_addMacroScope(v_quotContext_2054_, v___x_2059_, v_currMacroScope_2055_);
v___x_2061_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__7));
lean_inc(v___x_2056_);
v___x_2062_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2056_);
lean_ctor_set(v___x_2062_, 1, v___x_2058_);
lean_ctor_set(v___x_2062_, 2, v___x_2060_);
lean_ctor_set(v___x_2062_, 3, v___x_2061_);
v___x_2063_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__1));
v___x_2065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_2056_);
v___x_2066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2056_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__4));
v___x_2068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_2069_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_2056_);
v___x_2070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2056_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_2072_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
v___x_2073_ = lean_box(0);
v___x_2074_ = l_Lean_addMacroScope(v_quotContext_2054_, v___x_2073_, v_currMacroScope_2055_);
v___x_2075_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__4));
lean_inc(v___x_2056_);
v___x_2076_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2056_);
lean_ctor_set(v___x_2076_, 1, v___x_2072_);
lean_ctor_set(v___x_2076_, 2, v___x_2074_);
lean_ctor_set(v___x_2076_, 3, v___x_2075_);
lean_inc(v___x_2056_);
v___x_2077_ = l_Lean_Syntax_node1(v___x_2056_, v___x_2071_, v___x_2076_);
lean_inc(v___x_2056_);
v___x_2078_ = l_Lean_Syntax_node2(v___x_2056_, v___x_2068_, v___x_2070_, v___x_2077_);
v___x_2079_ = lean_box(2);
v___x_2080_ = l_Lean_Syntax_mkStrLit(v___x_1990_, v___x_2079_);
v___x_2081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__29));
lean_inc(v___x_2056_);
v___x_2082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2056_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v_sz_2084_ = lean_array_size(v_a_2049_);
v___x_2085_ = ((size_t)0ULL);
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(v_sz_2084_, v___x_2085_, v_a_2049_);
v___x_2087_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6);
v___x_2088_ = l_Lean_mkSepArray(v___x_2086_, v___x_2087_);
lean_dec_ref(v___x_2086_);
v___x_2089_ = l_Array_append___redArg(v___x_2083_, v___x_2088_);
lean_dec_ref(v___x_2088_);
lean_inc(v___x_2056_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 1);
lean_ctor_set(v___x_1987_, 2, v___x_2089_);
lean_ctor_set(v___x_1987_, 1, v___x_2063_);
lean_ctor_set(v___x_1987_, 0, v___x_2056_);
v___x_2091_ = v___x_1987_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_2056_);
v___x_2093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2056_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
lean_inc_ref(v___x_2093_);
lean_inc_ref(v___x_2066_);
lean_inc(v___x_2056_);
v___x_2094_ = l_Lean_Syntax_node3(v___x_2056_, v___x_2064_, v___x_2066_, v___x_2091_, v___x_2093_);
lean_inc(v___x_2056_);
v___x_2095_ = l_Lean_Syntax_node1(v___x_2056_, v___x_2063_, v___x_2094_);
lean_inc_ref(v___x_2062_);
lean_inc(v___x_2056_);
v___x_2096_ = l_Lean_Syntax_node2(v___x_2056_, v___x_2057_, v___x_2062_, v___x_2095_);
lean_inc(v___x_2056_);
v___x_2097_ = l_Lean_Syntax_node1(v___x_2056_, v___x_2063_, v___x_2096_);
lean_inc(v___x_2056_);
v___x_2098_ = l_Lean_Syntax_node3(v___x_2056_, v___x_2063_, v___x_2080_, v___x_2082_, v___x_2097_);
v___x_2099_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_2056_);
v___x_2100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2056_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
lean_inc(v___x_2056_);
v___x_2101_ = l_Lean_Syntax_node3(v___x_2056_, v___x_2067_, v___x_2078_, v___x_2098_, v___x_2100_);
lean_inc(v___x_2056_);
v___x_2102_ = l_Lean_Syntax_node1(v___x_2056_, v___x_2063_, v___x_2101_);
lean_inc(v___x_2056_);
v___x_2103_ = l_Lean_Syntax_node3(v___x_2056_, v___x_2064_, v___x_2066_, v___x_2102_, v___x_2093_);
lean_inc(v___x_2056_);
v___x_2104_ = l_Lean_Syntax_node1(v___x_2056_, v___x_2063_, v___x_2103_);
v___x_2105_ = l_Lean_Syntax_node2(v___x_2056_, v___x_2057_, v___x_2062_, v___x_2104_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2105_);
v___x_2107_ = v___x_2051_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___boxed(lean_object* v___x_2240_, lean_object* v_a_2241_, lean_object* v___x_2242_, lean_object* v_ctor_2243_, lean_object* v_args_2244_, lean_object* v_userNames_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0(v___x_2240_, v_a_2241_, v___x_2242_, v_ctor_2243_, v_args_2244_, v_userNames_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v_userNames_2245_);
lean_dec_ref(v_a_2241_);
lean_dec(v___x_2240_);
return v_res_2253_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__0));
v___x_2256_ = l_Lean_stringToMessageData(v___x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0(lean_object* v_constName_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; lean_object* v_env_2266_; lean_object* v___x_2267_; 
v___x_2265_ = lean_st_ref_get(v___y_2263_);
v_env_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc_ref(v_env_2266_);
lean_dec(v___x_2265_);
lean_inc(v_constName_2257_);
v___x_2267_ = l_Lean_isInductiveCore_x3f(v_env_2266_, v_constName_2257_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2268_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0___closed__1);
v___x_2269_ = 0;
v___x_2270_ = l_Lean_MessageData_ofConstName(v_constName_2257_, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2268_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___closed__1);
v___x_2273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0___redArg(v___x_2273_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
return v___x_2274_;
}
else
{
lean_object* v_val_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec_ref(v___y_2258_);
lean_dec(v_constName_2257_);
v_val_2275_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2267_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_val_2275_);
lean_dec(v___x_2267_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set_tag(v___x_2277_, 0);
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_val_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0___boxed(lean_object* v_constName_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0(v_constName_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct(lean_object* v_ctx_2305_, lean_object* v_header_2306_, lean_object* v_indName_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v___x_2315_; 
lean_inc_ref(v_a_2308_);
v___x_2315_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0(v_indName_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2317_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref(v___x_2315_);
lean_inc(v_a_2316_);
v___x_2317_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2306_, v_a_2316_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v_auxFunNames_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___f_2324_; lean_object* v___x_2325_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref(v___x_2317_);
v_auxFunNames_2319_ = lean_ctor_get(v_ctx_2305_, 2);
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = lean_array_get_borrowed(v___x_2320_, v_auxFunNames_2319_, v___x_2321_);
lean_inc(v___x_2322_);
v___x_2323_ = lean_mk_syntax_ident(v___x_2322_);
lean_inc(v_a_2316_);
v___f_2324_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___boxed), 13, 3);
lean_closure_set(v___f_2324_, 0, v___x_2321_);
lean_closure_set(v___f_2324_, 1, v_a_2316_);
lean_closure_set(v___f_2324_, 2, v___x_2323_);
lean_inc_ref(v_a_2312_);
v___x_2325_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts(v_a_2316_, v___f_2324_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2356_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2356_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2356_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_ref_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; size_t v_sz_2339_; size_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2354_; 
v_ref_2330_ = lean_ctor_get(v_a_2312_, 5);
lean_inc(v_ref_2330_);
lean_dec_ref(v_a_2312_);
v___x_2331_ = 0;
v___x_2332_ = l_Lean_SourceInfo_fromRef(v_ref_2330_, v___x_2331_);
lean_dec(v_ref_2330_);
v___x_2333_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__0));
v___x_2334_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1));
lean_inc(v___x_2332_);
v___x_2335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2332_);
lean_ctor_set(v___x_2335_, 1, v___x_2333_);
v___x_2336_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2337_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_2332_);
v___x_2338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2332_);
lean_ctor_set(v___x_2338_, 1, v___x_2336_);
lean_ctor_set(v___x_2338_, 2, v___x_2337_);
v_sz_2339_ = lean_array_size(v_a_2318_);
v___x_2340_ = ((size_t)0ULL);
v___x_2341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(v_sz_2339_, v___x_2340_, v_a_2318_);
v___x_2342_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6);
v___x_2343_ = l_Lean_mkSepArray(v___x_2341_, v___x_2342_);
lean_dec_ref(v___x_2341_);
v___x_2344_ = l_Array_append___redArg(v___x_2337_, v___x_2343_);
lean_dec_ref(v___x_2343_);
lean_inc(v___x_2332_);
v___x_2345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2332_);
lean_ctor_set(v___x_2345_, 1, v___x_2336_);
lean_ctor_set(v___x_2345_, 2, v___x_2344_);
v___x_2346_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__2));
lean_inc(v___x_2332_);
v___x_2347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2332_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4));
v___x_2349_ = l_Array_append___redArg(v___x_2337_, v_a_2326_);
lean_dec(v_a_2326_);
lean_inc(v___x_2332_);
v___x_2350_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2332_);
lean_ctor_set(v___x_2350_, 1, v___x_2336_);
lean_ctor_set(v___x_2350_, 2, v___x_2349_);
lean_inc(v___x_2332_);
v___x_2351_ = l_Lean_Syntax_node1(v___x_2332_, v___x_2348_, v___x_2350_);
lean_inc_ref(v___x_2338_);
v___x_2352_ = l_Lean_Syntax_node6(v___x_2332_, v___x_2334_, v___x_2335_, v___x_2338_, v___x_2338_, v___x_2345_, v___x_2347_, v___x_2351_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2352_);
v___x_2354_ = v___x_2328_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2312_);
v_a_2357_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2325_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2325_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_a_2316_);
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
v_a_2365_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2317_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2317_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_a_2313_);
lean_dec_ref(v_a_2312_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec_ref(v_header_2306_);
v_a_2373_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2315_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2315_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___boxed(lean_object* v_ctx_2381_, lean_object* v_header_2382_, lean_object* v_indName_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct(v_ctx_2381_, v_header_2382_, v_indName_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
lean_dec_ref(v_ctx_2381_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1(lean_object* v_a_2392_, lean_object* v___x_2393_, lean_object* v_userNames_2394_, lean_object* v_as_2395_, lean_object* v_i_2396_, lean_object* v_j_2397_, lean_object* v_inv_2398_, lean_object* v_bs_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___redArg(v_a_2392_, v___x_2393_, v_userNames_2394_, v_as_2395_, v_i_2396_, v_j_2397_, v_bs_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1___boxed(lean_object* v_a_2408_, lean_object* v___x_2409_, lean_object* v_userNames_2410_, lean_object* v_as_2411_, lean_object* v_i_2412_, lean_object* v_j_2413_, lean_object* v_inv_2414_, lean_object* v_bs_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1(v_a_2408_, v___x_2409_, v_userNames_2410_, v_as_2411_, v_i_2412_, v_j_2413_, v_inv_2414_, v_bs_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v_j_2413_);
lean_dec(v_i_2412_);
lean_dec_ref(v_as_2411_);
lean_dec_ref(v_userNames_2410_);
lean_dec_ref(v_a_2408_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1(lean_object* v_userNames_2424_, lean_object* v_a_2425_, lean_object* v___x_2426_, lean_object* v_as_2427_, lean_object* v_i_2428_, lean_object* v_j_2429_, lean_object* v_inv_2430_, lean_object* v_bs_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___redArg(v_userNames_2424_, v_a_2425_, v___x_2426_, v_as_2427_, v_i_2428_, v_j_2429_, v_bs_2431_, v___y_2436_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1___boxed(lean_object* v_userNames_2440_, lean_object* v_a_2441_, lean_object* v___x_2442_, lean_object* v_as_2443_, lean_object* v_i_2444_, lean_object* v_j_2445_, lean_object* v_inv_2446_, lean_object* v_bs_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Array_mapFinIdxM_map___at___00Array_mapFinIdxM_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__1_spec__1(v_userNames_2440_, v_a_2441_, v___x_2442_, v_as_2443_, v_i_2444_, v_j_2445_, v_inv_2446_, v_bs_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec_ref(v_as_2443_);
lean_dec_ref(v_a_2441_);
lean_dec_ref(v_userNames_2440_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3(lean_object* v_a_2456_, lean_object* v___x_2457_, size_t v_sz_2458_, size_t v_i_2459_, lean_object* v_bs_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___redArg(v_a_2456_, v___x_2457_, v_sz_2458_, v_i_2459_, v_bs_2460_, v___y_2465_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3___boxed(lean_object* v_a_2469_, lean_object* v___x_2470_, lean_object* v_sz_2471_, lean_object* v_i_2472_, lean_object* v_bs_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
size_t v_sz_boxed_2481_; size_t v_i_boxed_2482_; lean_object* v_res_2483_; 
v_sz_boxed_2481_ = lean_unbox_usize(v_sz_2471_);
lean_dec(v_sz_2471_);
v_i_boxed_2482_ = lean_unbox_usize(v_i_2472_);
lean_dec(v_i_2472_);
v_res_2483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__2_spec__3(v_a_2469_, v___x_2470_, v_sz_boxed_2481_, v_i_boxed_2482_, v_bs_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v_a_2469_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2(lean_object* v___x_2504_, size_t v_sz_2505_, size_t v_i_2506_, lean_object* v_bs_2507_){
_start:
{
uint8_t v___x_2508_; 
v___x_2508_ = lean_usize_dec_lt(v_i_2506_, v_sz_2505_);
if (v___x_2508_ == 0)
{
lean_dec(v___x_2504_);
return v_bs_2507_;
}
else
{
lean_object* v_v_2509_; lean_object* v_fst_2510_; lean_object* v_snd_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2536_; 
v_v_2509_ = lean_array_uget(v_bs_2507_, v_i_2506_);
v_fst_2510_ = lean_ctor_get(v_v_2509_, 0);
v_snd_2511_ = lean_ctor_get(v_v_2509_, 1);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_v_2509_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2513_ = v_v_2509_;
v_isShared_2514_ = v_isSharedCheck_2536_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_snd_2511_);
lean_inc(v_fst_2510_);
lean_dec(v_v_2509_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2536_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v_bs_x27_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2515_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2516_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v___x_2517_ = lean_unsigned_to_nat(0u);
v_bs_x27_2518_ = lean_array_uset(v_bs_2507_, v_i_2506_, v___x_2517_);
v___x_2519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1));
v___x_2520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3));
v___x_2521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__4));
lean_inc(v___x_2504_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set_tag(v___x_2513_, 2);
lean_ctor_set(v___x_2513_, 1, v___x_2521_);
lean_ctor_set(v___x_2513_, 0, v___x_2504_);
v___x_2523_ = v___x_2513_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; size_t v___x_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
lean_inc(v___x_2504_);
v___x_2524_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2504_);
lean_ctor_set(v___x_2524_, 1, v___x_2515_);
lean_ctor_set(v___x_2524_, 2, v___x_2516_);
v___x_2525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6));
v___x_2526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__7));
lean_inc(v___x_2504_);
v___x_2527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2504_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
lean_inc_ref(v___x_2524_);
lean_inc(v___x_2504_);
v___x_2528_ = l_Lean_Syntax_node4(v___x_2504_, v___x_2525_, v_fst_2510_, v___x_2524_, v___x_2527_, v_snd_2511_);
lean_inc_ref(v___x_2524_);
lean_inc(v___x_2504_);
v___x_2529_ = l_Lean_Syntax_node3(v___x_2504_, v___x_2520_, v___x_2523_, v___x_2524_, v___x_2528_);
lean_inc(v___x_2504_);
v___x_2530_ = l_Lean_Syntax_node2(v___x_2504_, v___x_2519_, v___x_2529_, v___x_2524_);
v___x_2531_ = ((size_t)1ULL);
v___x_2532_ = lean_usize_add(v_i_2506_, v___x_2531_);
v___x_2533_ = lean_array_uset(v_bs_x27_2518_, v_i_2506_, v___x_2530_);
v_i_2506_ = v___x_2532_;
v_bs_2507_ = v___x_2533_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___boxed(lean_object* v___x_2537_, lean_object* v_sz_2538_, lean_object* v_i_2539_, lean_object* v_bs_2540_){
_start:
{
size_t v_sz_boxed_2541_; size_t v_i_boxed_2542_; lean_object* v_res_2543_; 
v_sz_boxed_2541_ = lean_unbox_usize(v_sz_2538_);
lean_dec(v_sz_2538_);
v_i_boxed_2542_ = lean_unbox_usize(v_i_2539_);
lean_dec(v_i_2539_);
v_res_2543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2(v___x_2537_, v_sz_boxed_2541_, v_i_boxed_2542_, v_bs_2540_);
return v_res_2543_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__0));
v___x_2546_ = l_String_toRawSubstring_x27(v___x_2545_);
return v___x_2546_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__10(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__9));
v___x_2570_ = l_String_toRawSubstring_x27(v___x_2569_);
return v___x_2570_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__21(void){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__20));
v___x_2596_ = l_String_toRawSubstring_x27(v___x_2595_);
return v___x_2596_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__26(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__25));
v___x_2604_ = l_String_toRawSubstring_x27(v___x_2603_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg(lean_object* v_indName_2623_, size_t v_sz_2624_, size_t v_i_2625_, lean_object* v_bs_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
uint8_t v___x_2630_; 
v___x_2630_ = lean_usize_dec_lt(v_i_2625_, v_sz_2624_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; 
lean_dec_ref(v___y_2627_);
lean_dec(v_indName_2623_);
v___x_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2631_, 0, v_bs_2626_);
return v___x_2631_;
}
else
{
lean_object* v_v_2632_; lean_object* v___x_2633_; 
v_v_2632_ = lean_array_uget(v_bs_2626_, v_i_2625_);
lean_inc(v_v_2632_);
v___x_2633_ = l_Lean_Elab_Deriving_FromToJson_mkJsonField(v_v_2632_, v___y_2627_, v___y_2628_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v_ref_2635_; lean_object* v_quotContext_2636_; lean_object* v_currMacroScope_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v_snd_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2741_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref(v___x_2633_);
v_ref_2635_ = lean_ctor_get(v___y_2627_, 5);
v_quotContext_2636_ = lean_ctor_get(v___y_2627_, 10);
v_currMacroScope_2637_ = lean_ctor_get(v___y_2627_, 11);
v___x_2638_ = 0;
v___x_2639_ = l_Lean_SourceInfo_fromRef(v_ref_2635_, v___x_2638_);
v___x_2640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_2641_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__1);
v___x_2642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v_currMacroScope_2637_);
lean_inc(v_quotContext_2636_);
v___x_2643_ = l_Lean_addMacroScope(v_quotContext_2636_, v___x_2642_, v_currMacroScope_2637_);
v___x_2644_ = lean_box(0);
v___x_2645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__5));
lean_inc(v___x_2639_);
v___x_2646_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2639_);
lean_ctor_set(v___x_2646_, 1, v___x_2641_);
lean_ctor_set(v___x_2646_, 2, v___x_2643_);
lean_ctor_set(v___x_2646_, 3, v___x_2645_);
v___x_2647_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10);
v___x_2648_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__11));
lean_inc(v_currMacroScope_2637_);
lean_inc(v_quotContext_2636_);
v___x_2649_ = l_Lean_addMacroScope(v_quotContext_2636_, v___x_2648_, v_currMacroScope_2637_);
v___x_2650_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__6));
lean_inc(v___x_2639_);
v___x_2651_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2639_);
lean_ctor_set(v___x_2651_, 1, v___x_2647_);
lean_ctor_set(v___x_2651_, 2, v___x_2649_);
lean_ctor_set(v___x_2651_, 3, v___x_2650_);
v_snd_2652_ = lean_ctor_get(v_a_2634_, 1);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_a_2634_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; 
v_unused_2742_ = lean_ctor_get(v_a_2634_, 0);
lean_dec(v_unused_2742_);
v___x_2654_ = v_a_2634_;
v_isShared_2655_ = v_isSharedCheck_2741_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_snd_2652_);
lean_dec(v_a_2634_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2741_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2656_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__2));
lean_inc(v___x_2639_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set_tag(v___x_2654_, 2);
lean_ctor_set(v___x_2654_, 1, v___x_2656_);
lean_ctor_set(v___x_2654_, 0, v___x_2639_);
v___x_2658_ = v___x_2654_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2659_; lean_object* v_bs_x27_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; size_t v___x_2736_; size_t v___x_2737_; lean_object* v___x_2738_; 
v___x_2659_ = lean_unsigned_to_nat(0u);
v_bs_x27_2660_ = lean_array_uset(v_bs_2626_, v_i_2625_, v___x_2659_);
v___x_2661_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2662_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1));
lean_inc(v___x_2639_);
v___x_2663_ = l_Lean_Syntax_node1(v___x_2639_, v___x_2662_, v___x_2658_);
lean_inc(v___x_2639_);
v___x_2664_ = l_Lean_Syntax_node3(v___x_2639_, v___x_2661_, v___x_2651_, v___x_2663_, v_snd_2652_);
lean_inc(v___x_2639_);
v___x_2665_ = l_Lean_Syntax_node2(v___x_2639_, v___x_2640_, v___x_2646_, v___x_2664_);
v___x_2666_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_2667_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__1));
v___x_2668_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__10);
v___x_2669_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__13));
lean_inc(v_currMacroScope_2637_);
lean_inc(v_quotContext_2636_);
v___x_2670_ = l_Lean_addMacroScope(v_quotContext_2636_, v___x_2669_, v_currMacroScope_2637_);
v___x_2671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__15));
lean_inc(v___x_2639_);
v___x_2672_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2639_);
lean_ctor_set(v___x_2672_, 1, v___x_2668_);
lean_ctor_set(v___x_2672_, 2, v___x_2670_);
lean_ctor_set(v___x_2672_, 3, v___x_2671_);
v___x_2673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41));
v___x_2674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_2675_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_2639_);
v___x_2676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2639_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_2678_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
v___x_2679_ = lean_box(0);
lean_inc(v_currMacroScope_2637_);
lean_inc(v_quotContext_2636_);
v___x_2680_ = l_Lean_addMacroScope(v_quotContext_2636_, v___x_2679_, v_currMacroScope_2637_);
v___x_2681_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__4));
lean_inc(v___x_2639_);
v___x_2682_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2639_);
lean_ctor_set(v___x_2682_, 1, v___x_2678_);
lean_ctor_set(v___x_2682_, 2, v___x_2680_);
lean_ctor_set(v___x_2682_, 3, v___x_2681_);
lean_inc(v___x_2639_);
v___x_2683_ = l_Lean_Syntax_node1(v___x_2639_, v___x_2677_, v___x_2682_);
lean_inc(v___x_2639_);
v___x_2684_ = l_Lean_Syntax_node2(v___x_2639_, v___x_2674_, v___x_2676_, v___x_2683_);
v___x_2685_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__16));
v___x_2686_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17));
lean_inc(v___x_2639_);
v___x_2687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2639_);
lean_ctor_set(v___x_2687_, 1, v___x_2685_);
v___x_2688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19));
v___x_2689_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__21, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__21);
v___x_2690_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__22));
lean_inc(v_currMacroScope_2637_);
lean_inc(v_quotContext_2636_);
v___x_2691_ = l_Lean_addMacroScope(v_quotContext_2636_, v___x_2690_, v_currMacroScope_2637_);
lean_inc(v___x_2639_);
v___x_2692_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2639_);
lean_ctor_set(v___x_2692_, 1, v___x_2689_);
lean_ctor_set(v___x_2692_, 2, v___x_2691_);
lean_ctor_set(v___x_2692_, 3, v___x_2644_);
lean_inc_ref(v___x_2692_);
lean_inc(v___x_2639_);
v___x_2693_ = l_Lean_Syntax_node1(v___x_2639_, v___x_2661_, v___x_2692_);
v___x_2694_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_2639_);
v___x_2695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2639_);
lean_ctor_set(v___x_2695_, 1, v___x_2661_);
lean_ctor_set(v___x_2695_, 2, v___x_2694_);
v___x_2696_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__7));
lean_inc(v___x_2639_);
v___x_2697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2639_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__24));
v___x_2699_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__26, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__26_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__26);
v___x_2700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__27));
lean_inc(v_currMacroScope_2637_);
lean_inc(v_quotContext_2636_);
v___x_2701_ = l_Lean_addMacroScope(v_quotContext_2636_, v___x_2700_, v_currMacroScope_2637_);
v___x_2702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__31));
lean_inc(v___x_2639_);
v___x_2703_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2639_);
lean_ctor_set(v___x_2703_, 1, v___x_2699_);
lean_ctor_set(v___x_2703_, 2, v___x_2701_);
lean_ctor_set(v___x_2703_, 3, v___x_2702_);
lean_inc(v_indName_2623_);
v___x_2704_ = l_Lean_instQuoteNameMkStr1___private__1(v_indName_2623_);
lean_inc(v___x_2639_);
v___x_2705_ = l_Lean_Syntax_node1(v___x_2639_, v___x_2661_, v___x_2704_);
lean_inc_ref(v___x_2703_);
lean_inc(v___x_2639_);
v___x_2706_ = l_Lean_Syntax_node2(v___x_2639_, v___x_2640_, v___x_2703_, v___x_2705_);
v___x_2707_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_2639_);
v___x_2708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2639_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
lean_inc_ref(v___x_2708_);
lean_inc(v___x_2684_);
lean_inc(v___x_2639_);
v___x_2709_ = l_Lean_Syntax_node3(v___x_2639_, v___x_2673_, v___x_2684_, v___x_2706_, v___x_2708_);
v___x_2710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__32));
lean_inc(v___x_2639_);
v___x_2711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2639_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__34));
v___x_2713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__35));
lean_inc(v___x_2639_);
v___x_2714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2639_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
lean_inc(v___x_2639_);
v___x_2715_ = l_Lean_Syntax_node1(v___x_2639_, v___x_2712_, v___x_2714_);
lean_inc_ref(v___x_2711_);
lean_inc(v___x_2639_);
v___x_2716_ = l_Lean_Syntax_node3(v___x_2639_, v___x_2698_, v___x_2709_, v___x_2711_, v___x_2715_);
v___x_2717_ = l_Lean_instQuoteNameMkStr1___private__1(v_v_2632_);
lean_inc(v___x_2639_);
v___x_2718_ = l_Lean_Syntax_node1(v___x_2639_, v___x_2661_, v___x_2717_);
lean_inc(v___x_2639_);
v___x_2719_ = l_Lean_Syntax_node2(v___x_2639_, v___x_2640_, v___x_2703_, v___x_2718_);
lean_inc_ref(v___x_2708_);
lean_inc(v___x_2684_);
lean_inc(v___x_2639_);
v___x_2720_ = l_Lean_Syntax_node3(v___x_2639_, v___x_2673_, v___x_2684_, v___x_2719_, v___x_2708_);
lean_inc_ref(v___x_2711_);
lean_inc(v___x_2639_);
v___x_2721_ = l_Lean_Syntax_node3(v___x_2639_, v___x_2698_, v___x_2716_, v___x_2711_, v___x_2720_);
v___x_2722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__36));
lean_inc(v___x_2639_);
v___x_2723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2639_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
lean_inc(v___x_2639_);
v___x_2724_ = l_Lean_Syntax_node1(v___x_2639_, v___x_2712_, v___x_2723_);
lean_inc_ref(v___x_2711_);
lean_inc(v___x_2639_);
v___x_2725_ = l_Lean_Syntax_node3(v___x_2639_, v___x_2698_, v___x_2721_, v___x_2711_, v___x_2724_);
lean_inc(v___x_2639_);
v___x_2726_ = l_Lean_Syntax_node3(v___x_2639_, v___x_2698_, v___x_2725_, v___x_2711_, v___x_2692_);
lean_inc(v___x_2639_);
v___x_2727_ = l_Lean_Syntax_node4(v___x_2639_, v___x_2688_, v___x_2693_, v___x_2695_, v___x_2697_, v___x_2726_);
lean_inc(v___x_2639_);
v___x_2728_ = l_Lean_Syntax_node2(v___x_2639_, v___x_2686_, v___x_2687_, v___x_2727_);
lean_inc(v___x_2639_);
v___x_2729_ = l_Lean_Syntax_node3(v___x_2639_, v___x_2673_, v___x_2684_, v___x_2728_, v___x_2708_);
lean_inc(v___x_2639_);
v___x_2730_ = l_Lean_Syntax_node1(v___x_2639_, v___x_2661_, v___x_2729_);
lean_inc(v___x_2639_);
v___x_2731_ = l_Lean_Syntax_node2(v___x_2639_, v___x_2640_, v___x_2672_, v___x_2730_);
v___x_2732_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct___closed__8));
lean_inc(v___x_2639_);
v___x_2733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2639_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
lean_inc(v___x_2639_);
v___x_2734_ = l_Lean_Syntax_node3(v___x_2639_, v___x_2667_, v___x_2731_, v___x_2733_, v___x_2665_);
v___x_2735_ = l_Lean_Syntax_node1(v___x_2639_, v___x_2666_, v___x_2734_);
v___x_2736_ = ((size_t)1ULL);
v___x_2737_ = lean_usize_add(v_i_2625_, v___x_2736_);
v___x_2738_ = lean_array_uset(v_bs_x27_2660_, v_i_2625_, v___x_2735_);
v_i_2625_ = v___x_2737_;
v_bs_2626_ = v___x_2738_;
goto _start;
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_v_2632_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v_bs_2626_);
lean_dec(v_indName_2623_);
v_a_2743_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2633_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2633_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___boxed(lean_object* v_indName_2751_, lean_object* v_sz_2752_, lean_object* v_i_2753_, lean_object* v_bs_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
size_t v_sz_boxed_2758_; size_t v_i_boxed_2759_; lean_object* v_res_2760_; 
v_sz_boxed_2758_ = lean_unbox_usize(v_sz_2752_);
lean_dec(v_sz_2752_);
v_i_boxed_2759_ = lean_unbox_usize(v_i_2753_);
lean_dec(v_i_2753_);
v_res_2760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg(v_indName_2751_, v_sz_boxed_2758_, v_i_boxed_2759_, v_bs_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3(lean_object* v___x_2780_, lean_object* v___x_2781_, size_t v_sz_2782_, size_t v_i_2783_, lean_object* v_bs_2784_){
_start:
{
uint8_t v___x_2785_; 
v___x_2785_ = lean_usize_dec_lt(v_i_2783_, v_sz_2782_);
if (v___x_2785_ == 0)
{
lean_dec(v___x_2781_);
lean_dec(v___x_2780_);
return v_bs_2784_;
}
else
{
lean_object* v_v_2786_; lean_object* v_fst_2787_; lean_object* v_snd_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2810_; 
v_v_2786_ = lean_array_uget(v_bs_2784_, v_i_2783_);
v_fst_2787_ = lean_ctor_get(v_v_2786_, 0);
v_snd_2788_ = lean_ctor_get(v_v_2786_, 1);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_v_2786_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2790_ = v_v_2786_;
v_isShared_2791_ = v_isSharedCheck_2810_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_snd_2788_);
lean_inc(v_fst_2787_);
lean_dec(v_v_2786_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2810_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v_bs_x27_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2792_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2793_ = lean_unsigned_to_nat(0u);
v_bs_x27_2794_ = lean_array_uset(v_bs_2784_, v_i_2783_, v___x_2793_);
v___x_2795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__1));
v___x_2796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__3));
lean_inc(v___x_2781_);
lean_inc(v___x_2780_);
v___x_2797_ = l_Lean_Syntax_node2(v___x_2780_, v___x_2796_, v_fst_2787_, v___x_2781_);
v___x_2798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__5));
v___x_2799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6));
lean_inc(v___x_2780_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set_tag(v___x_2790_, 2);
lean_ctor_set(v___x_2790_, 1, v___x_2799_);
lean_ctor_set(v___x_2790_, 0, v___x_2780_);
v___x_2801_ = v___x_2790_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; size_t v___x_2805_; size_t v___x_2806_; lean_object* v___x_2807_; 
lean_inc(v___x_2781_);
lean_inc(v___x_2780_);
v___x_2802_ = l_Lean_Syntax_node3(v___x_2780_, v___x_2798_, v___x_2801_, v___x_2781_, v_snd_2788_);
lean_inc_n(v___x_2781_, 2);
lean_inc(v___x_2780_);
v___x_2803_ = l_Lean_Syntax_node3(v___x_2780_, v___x_2792_, v___x_2781_, v___x_2781_, v___x_2802_);
lean_inc(v___x_2780_);
v___x_2804_ = l_Lean_Syntax_node2(v___x_2780_, v___x_2795_, v___x_2797_, v___x_2803_);
v___x_2805_ = ((size_t)1ULL);
v___x_2806_ = lean_usize_add(v_i_2783_, v___x_2805_);
v___x_2807_ = lean_array_uset(v_bs_x27_2794_, v_i_2783_, v___x_2804_);
v_i_2783_ = v___x_2806_;
v_bs_2784_ = v___x_2807_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___boxed(lean_object* v___x_2811_, lean_object* v___x_2812_, lean_object* v_sz_2813_, lean_object* v_i_2814_, lean_object* v_bs_2815_){
_start:
{
size_t v_sz_boxed_2816_; size_t v_i_boxed_2817_; lean_object* v_res_2818_; 
v_sz_boxed_2816_ = lean_unbox_usize(v_sz_2813_);
lean_dec(v_sz_2813_);
v_i_boxed_2817_ = lean_unbox_usize(v_i_2814_);
lean_dec(v_i_2814_);
v_res_2818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3(v___x_2811_, v___x_2812_, v_sz_boxed_2816_, v_i_boxed_2817_, v_bs_2815_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__1(size_t v_sz_2819_, size_t v_i_2820_, lean_object* v_bs_2821_){
_start:
{
uint8_t v___x_2822_; 
v___x_2822_ = lean_usize_dec_lt(v_i_2820_, v_sz_2819_);
if (v___x_2822_ == 0)
{
return v_bs_2821_;
}
else
{
lean_object* v_v_2823_; lean_object* v___x_2824_; lean_object* v_bs_x27_2825_; lean_object* v___x_2826_; size_t v___x_2827_; size_t v___x_2828_; lean_object* v___x_2829_; 
v_v_2823_ = lean_array_uget(v_bs_2821_, v_i_2820_);
v___x_2824_ = lean_unsigned_to_nat(0u);
v_bs_x27_2825_ = lean_array_uset(v_bs_2821_, v_i_2820_, v___x_2824_);
v___x_2826_ = lean_mk_syntax_ident(v_v_2823_);
v___x_2827_ = ((size_t)1ULL);
v___x_2828_ = lean_usize_add(v_i_2820_, v___x_2827_);
v___x_2829_ = lean_array_uset(v_bs_x27_2825_, v_i_2820_, v___x_2826_);
v_i_2820_ = v___x_2828_;
v_bs_2821_ = v___x_2829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__1___boxed(lean_object* v_sz_2831_, lean_object* v_i_2832_, lean_object* v_bs_2833_){
_start:
{
size_t v_sz_boxed_2834_; size_t v_i_boxed_2835_; lean_object* v_res_2836_; 
v_sz_boxed_2834_ = lean_unbox_usize(v_sz_2831_);
lean_dec(v_sz_2831_);
v_i_boxed_2835_ = lean_unbox_usize(v_i_2832_);
lean_dec(v_i_2832_);
v_res_2836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__1(v_sz_boxed_2834_, v_i_boxed_2835_, v_bs_2833_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct(lean_object* v_indName_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v___x_2884_; lean_object* v_env_2885_; uint8_t v___x_2886_; lean_object* v___x_2887_; size_t v_sz_2888_; size_t v___x_2889_; lean_object* v___x_2890_; 
v___x_2884_ = lean_st_ref_get(v_a_2882_);
v_env_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc_ref(v_env_2885_);
lean_dec(v___x_2884_);
v___x_2886_ = 0;
lean_inc(v_indName_2876_);
v___x_2887_ = l_Lean_getStructureFieldsFlattened(v_env_2885_, v_indName_2876_, v___x_2886_);
v_sz_2888_ = lean_array_size(v___x_2887_);
v___x_2889_ = ((size_t)0ULL);
lean_inc_ref(v_a_2881_);
lean_inc_ref(v___x_2887_);
v___x_2890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg(v_indName_2876_, v_sz_2888_, v___x_2889_, v___x_2887_, v_a_2881_, v_a_2882_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2940_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2940_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2940_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v_ref_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; size_t v_sz_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; size_t v_sz_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2938_; 
v_ref_2895_ = lean_ctor_get(v_a_2881_, 5);
lean_inc(v_ref_2895_);
lean_dec_ref(v_a_2881_);
v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__1(v_sz_2888_, v___x_2889_, v___x_2887_);
v___x_2897_ = l_Lean_SourceInfo_fromRef(v_ref_2895_, v___x_2886_);
lean_dec(v_ref_2895_);
v___x_2898_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__0));
v___x_2899_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1));
lean_inc(v___x_2897_);
v___x_2900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2897_);
lean_ctor_set(v___x_2900_, 1, v___x_2898_);
v___x_2901_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3));
v___x_2902_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_2903_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v___x_2904_ = l_Array_zip___redArg(v___x_2896_, v_a_2891_);
lean_dec(v_a_2891_);
v_sz_2905_ = lean_array_size(v___x_2904_);
lean_inc(v___x_2897_);
v___x_2906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2(v___x_2897_, v_sz_2905_, v___x_2889_, v___x_2904_);
v___x_2907_ = l_Array_append___redArg(v___x_2903_, v___x_2906_);
lean_dec_ref(v___x_2906_);
v___x_2908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1));
v___x_2909_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5));
v___x_2910_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__6));
lean_inc(v___x_2897_);
v___x_2911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2897_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__8));
v___x_2913_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__9));
lean_inc(v___x_2897_);
v___x_2914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2897_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
lean_inc(v___x_2897_);
v___x_2915_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2897_);
lean_ctor_set(v___x_2915_, 1, v___x_2902_);
lean_ctor_set(v___x_2915_, 2, v___x_2903_);
v___x_2916_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__11));
v___x_2917_ = l_Array_zip___redArg(v___x_2896_, v___x_2896_);
lean_dec_ref(v___x_2896_);
v_sz_2918_ = lean_array_size(v___x_2917_);
lean_inc_ref(v___x_2915_);
lean_inc(v___x_2897_);
v___x_2919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3(v___x_2897_, v___x_2915_, v_sz_2918_, v___x_2889_, v___x_2917_);
v___x_2920_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6);
v___x_2921_ = l_Lean_mkSepArray(v___x_2919_, v___x_2920_);
lean_dec_ref(v___x_2919_);
v___x_2922_ = l_Array_append___redArg(v___x_2903_, v___x_2921_);
lean_dec_ref(v___x_2921_);
lean_inc(v___x_2897_);
v___x_2923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2897_);
lean_ctor_set(v___x_2923_, 1, v___x_2902_);
lean_ctor_set(v___x_2923_, 2, v___x_2922_);
lean_inc(v___x_2897_);
v___x_2924_ = l_Lean_Syntax_node1(v___x_2897_, v___x_2916_, v___x_2923_);
v___x_2925_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__13));
lean_inc_ref(v___x_2915_);
lean_inc(v___x_2897_);
v___x_2926_ = l_Lean_Syntax_node1(v___x_2897_, v___x_2925_, v___x_2915_);
v___x_2927_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__14));
lean_inc(v___x_2897_);
v___x_2928_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2897_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
lean_inc_ref_n(v___x_2915_, 2);
lean_inc(v___x_2897_);
v___x_2929_ = l_Lean_Syntax_node6(v___x_2897_, v___x_2912_, v___x_2914_, v___x_2915_, v___x_2924_, v___x_2926_, v___x_2915_, v___x_2928_);
lean_inc(v___x_2897_);
v___x_2930_ = l_Lean_Syntax_node1(v___x_2897_, v___x_2902_, v___x_2929_);
lean_inc(v___x_2897_);
v___x_2931_ = l_Lean_Syntax_node2(v___x_2897_, v___x_2909_, v___x_2911_, v___x_2930_);
lean_inc(v___x_2897_);
v___x_2932_ = l_Lean_Syntax_node2(v___x_2897_, v___x_2908_, v___x_2931_, v___x_2915_);
v___x_2933_ = lean_array_push(v___x_2907_, v___x_2932_);
lean_inc(v___x_2897_);
v___x_2934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2897_);
lean_ctor_set(v___x_2934_, 1, v___x_2902_);
lean_ctor_set(v___x_2934_, 2, v___x_2933_);
lean_inc(v___x_2897_);
v___x_2935_ = l_Lean_Syntax_node1(v___x_2897_, v___x_2901_, v___x_2934_);
v___x_2936_ = l_Lean_Syntax_node2(v___x_2897_, v___x_2899_, v___x_2900_, v___x_2935_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2936_);
v___x_2938_ = v___x_2893_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec_ref(v___x_2887_);
lean_dec_ref(v_a_2881_);
v_a_2941_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2890_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2890_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___boxed(lean_object* v_indName_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct(v_indName_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
lean_dec(v_a_2955_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0(lean_object* v_indName_2958_, size_t v_sz_2959_, size_t v_i_2960_, lean_object* v_bs_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg(v_indName_2958_, v_sz_2959_, v_i_2960_, v_bs_2961_, v___y_2966_, v___y_2967_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___boxed(lean_object* v_indName_2970_, lean_object* v_sz_2971_, lean_object* v_i_2972_, lean_object* v_bs_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
size_t v_sz_boxed_2981_; size_t v_i_boxed_2982_; lean_object* v_res_2983_; 
v_sz_boxed_2981_ = lean_unbox_usize(v_sz_2971_);
lean_dec(v_sz_2971_);
v_i_boxed_2982_ = lean_unbox_usize(v_i_2972_);
lean_dec(v_i_2972_);
v_res_2983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0(v_indName_2970_, v_sz_boxed_2981_, v_i_boxed_2982_, v_bs_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__4(size_t v_sz_2984_, size_t v_i_2985_, lean_object* v_bs_2986_){
_start:
{
uint8_t v___x_2987_; 
v___x_2987_ = lean_usize_dec_lt(v_i_2985_, v_sz_2984_);
if (v___x_2987_ == 0)
{
return v_bs_2986_;
}
else
{
lean_object* v_v_2988_; lean_object* v___x_2989_; lean_object* v_bs_x27_2990_; lean_object* v___x_2991_; size_t v___x_2992_; size_t v___x_2993_; lean_object* v___x_2994_; 
v_v_2988_ = lean_array_uget(v_bs_2986_, v_i_2985_);
v___x_2989_ = lean_unsigned_to_nat(0u);
v_bs_x27_2990_ = lean_array_uset(v_bs_2986_, v_i_2985_, v___x_2989_);
v___x_2991_ = l_Lean_instQuoteNameMkStr1___private__1(v_v_2988_);
v___x_2992_ = ((size_t)1ULL);
v___x_2993_ = lean_usize_add(v_i_2985_, v___x_2992_);
v___x_2994_ = lean_array_uset(v_bs_x27_2990_, v_i_2985_, v___x_2991_);
v_i_2985_ = v___x_2993_;
v_bs_2986_ = v___x_2994_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__4___boxed(lean_object* v_sz_2996_, lean_object* v_i_2997_, lean_object* v_bs_2998_){
_start:
{
size_t v_sz_boxed_2999_; size_t v_i_boxed_3000_; lean_object* v_res_3001_; 
v_sz_boxed_2999_ = lean_unbox_usize(v_sz_2996_);
lean_dec(v_sz_2996_);
v_i_boxed_3000_ = lean_unbox_usize(v_i_2997_);
lean_dec(v_i_2997_);
v_res_3001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__4(v_sz_boxed_2999_, v_i_boxed_3000_, v_bs_2998_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__0(size_t v_sz_3002_, size_t v_i_3003_, lean_object* v_bs_3004_){
_start:
{
uint8_t v___x_3005_; 
v___x_3005_ = lean_usize_dec_lt(v_i_3003_, v_sz_3002_);
if (v___x_3005_ == 0)
{
return v_bs_3004_;
}
else
{
lean_object* v_v_3006_; lean_object* v_fst_3007_; lean_object* v___x_3008_; lean_object* v_bs_x27_3009_; size_t v___x_3010_; size_t v___x_3011_; lean_object* v___x_3012_; 
v_v_3006_ = lean_array_uget_borrowed(v_bs_3004_, v_i_3003_);
v_fst_3007_ = lean_ctor_get(v_v_3006_, 0);
lean_inc(v_fst_3007_);
v___x_3008_ = lean_unsigned_to_nat(0u);
v_bs_x27_3009_ = lean_array_uset(v_bs_3004_, v_i_3003_, v___x_3008_);
v___x_3010_ = ((size_t)1ULL);
v___x_3011_ = lean_usize_add(v_i_3003_, v___x_3010_);
v___x_3012_ = lean_array_uset(v_bs_x27_3009_, v_i_3003_, v_fst_3007_);
v_i_3003_ = v___x_3011_;
v_bs_3004_ = v___x_3012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__0___boxed(lean_object* v_sz_3014_, lean_object* v_i_3015_, lean_object* v_bs_3016_){
_start:
{
size_t v_sz_boxed_3017_; size_t v_i_boxed_3018_; lean_object* v_res_3019_; 
v_sz_boxed_3017_ = lean_unbox_usize(v_sz_3014_);
lean_dec(v_sz_3014_);
v_i_boxed_3018_ = lean_unbox_usize(v_i_3015_);
lean_dec(v_i_3015_);
v_res_3019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__0(v_sz_boxed_3017_, v_i_boxed_3018_, v_bs_3016_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__2(lean_object* v___x_3020_, lean_object* v___x_3021_, size_t v_sz_3022_, size_t v_i_3023_, lean_object* v_bs_3024_){
_start:
{
uint8_t v___x_3025_; 
v___x_3025_ = lean_usize_dec_lt(v_i_3023_, v_sz_3022_);
if (v___x_3025_ == 0)
{
lean_dec(v___x_3021_);
lean_dec(v___x_3020_);
return v_bs_3024_;
}
else
{
lean_object* v_v_3026_; lean_object* v_fst_3027_; lean_object* v_snd_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3050_; 
v_v_3026_ = lean_array_uget(v_bs_3024_, v_i_3023_);
v_fst_3027_ = lean_ctor_get(v_v_3026_, 0);
v_snd_3028_ = lean_ctor_get(v_v_3026_, 1);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_v_3026_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3030_ = v_v_3026_;
v_isShared_3031_ = v_isSharedCheck_3050_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_snd_3028_);
lean_inc(v_fst_3027_);
lean_dec(v_v_3026_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3050_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v_bs_x27_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; 
v___x_3032_ = lean_unsigned_to_nat(0u);
v_bs_x27_3033_ = lean_array_uset(v_bs_3024_, v_i_3023_, v___x_3032_);
v___x_3034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1));
v___x_3035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__3));
v___x_3036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__4));
lean_inc(v___x_3020_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set_tag(v___x_3030_, 2);
lean_ctor_set(v___x_3030_, 1, v___x_3036_);
lean_ctor_set(v___x_3030_, 0, v___x_3020_);
v___x_3038_ = v___x_3030_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; size_t v___x_3045_; size_t v___x_3046_; lean_object* v___x_3047_; 
v___x_3039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__6));
v___x_3040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__7));
lean_inc(v___x_3020_);
v___x_3041_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3020_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
lean_inc(v___x_3021_);
lean_inc(v___x_3020_);
v___x_3042_ = l_Lean_Syntax_node4(v___x_3020_, v___x_3039_, v_fst_3027_, v___x_3021_, v___x_3041_, v_snd_3028_);
lean_inc(v___x_3021_);
lean_inc(v___x_3020_);
v___x_3043_ = l_Lean_Syntax_node3(v___x_3020_, v___x_3035_, v___x_3038_, v___x_3021_, v___x_3042_);
lean_inc(v___x_3021_);
lean_inc(v___x_3020_);
v___x_3044_ = l_Lean_Syntax_node2(v___x_3020_, v___x_3034_, v___x_3043_, v___x_3021_);
v___x_3045_ = ((size_t)1ULL);
v___x_3046_ = lean_usize_add(v_i_3023_, v___x_3045_);
v___x_3047_ = lean_array_uset(v_bs_x27_3033_, v_i_3023_, v___x_3044_);
v_i_3023_ = v___x_3046_;
v_bs_3024_ = v___x_3047_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__2___boxed(lean_object* v___x_3051_, lean_object* v___x_3052_, lean_object* v_sz_3053_, lean_object* v_i_3054_, lean_object* v_bs_3055_){
_start:
{
size_t v_sz_boxed_3056_; size_t v_i_boxed_3057_; lean_object* v_res_3058_; 
v_sz_boxed_3056_ = lean_unbox_usize(v_sz_3053_);
lean_dec(v_sz_3053_);
v_i_boxed_3057_ = lean_unbox_usize(v_i_3054_);
lean_dec(v_i_3054_);
v_res_3058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__2(v___x_3051_, v___x_3052_, v_sz_boxed_3056_, v_i_boxed_3057_, v_bs_3055_);
return v_res_3058_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__0));
v___x_3061_ = l_String_toRawSubstring_x27(v___x_3060_);
return v___x_3061_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__8));
v___x_3079_ = l_String_toRawSubstring_x27(v___x_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg(lean_object* v_indVal_3086_, lean_object* v___x_3087_, lean_object* v_as_3088_, lean_object* v_i_3089_, lean_object* v_j_3090_, lean_object* v_bs_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_zero_3094_; uint8_t v_isZero_3095_; 
v_zero_3094_ = lean_unsigned_to_nat(0u);
v_isZero_3095_ = lean_nat_dec_eq(v_i_3089_, v_zero_3094_);
if (v_isZero_3095_ == 1)
{
lean_object* v___x_3096_; 
lean_dec_ref(v___y_3092_);
lean_dec(v_j_3090_);
lean_dec(v_i_3089_);
lean_dec(v___x_3087_);
lean_dec_ref(v_indVal_3086_);
v___x_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3096_, 0, v_bs_3091_);
return v___x_3096_;
}
else
{
lean_object* v___x_3097_; lean_object* v_toConstantVal_3098_; lean_object* v_snd_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3189_; 
v___x_3097_ = lean_array_fget(v_as_3088_, v_j_3090_);
v_toConstantVal_3098_ = lean_ctor_get(v_indVal_3086_, 0);
lean_inc_ref(v_toConstantVal_3098_);
v_snd_3099_ = lean_ctor_get(v___x_3097_, 1);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3189_ == 0)
{
lean_object* v_unused_3190_; 
v_unused_3190_ = lean_ctor_get(v___x_3097_, 0);
lean_dec(v_unused_3190_);
v___x_3101_ = v___x_3097_;
v_isShared_3102_ = v_isSharedCheck_3189_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_snd_3099_);
lean_dec(v___x_3097_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3189_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v_name_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3186_; 
v_name_3103_ = lean_ctor_get(v_toConstantVal_3098_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_toConstantVal_3098_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; lean_object* v_unused_3188_; 
v_unused_3187_ = lean_ctor_get(v_toConstantVal_3098_, 2);
lean_dec(v_unused_3187_);
v_unused_3188_ = lean_ctor_get(v_toConstantVal_3098_, 1);
lean_dec(v_unused_3188_);
v___x_3105_ = v_toConstantVal_3098_;
v_isShared_3106_ = v_isSharedCheck_3186_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_name_3103_);
lean_dec(v_toConstantVal_3098_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3186_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v_one_3107_; lean_object* v_n_3108_; lean_object* v_a_3110_; uint8_t v___x_3114_; 
v_one_3107_ = lean_unsigned_to_nat(1u);
v_n_3108_ = lean_nat_sub(v_i_3089_, v_one_3107_);
lean_dec(v_i_3089_);
v___x_3114_ = l_Lean_Expr_isAppOf(v_snd_3099_, v_name_3103_);
lean_dec(v_name_3103_);
lean_dec(v_snd_3099_);
if (v___x_3114_ == 0)
{
lean_object* v_ref_3115_; lean_object* v_quotContext_3116_; lean_object* v_currMacroScope_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
v_ref_3115_ = lean_ctor_get(v___y_3092_, 5);
v_quotContext_3116_ = lean_ctor_get(v___y_3092_, 10);
v_currMacroScope_3117_ = lean_ctor_get(v___y_3092_, 11);
v___x_3118_ = l_Lean_SourceInfo_fromRef(v_ref_3115_, v___x_3114_);
v___x_3119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_3120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_3121_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__1, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__1);
v___x_3122_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__2));
lean_inc(v_currMacroScope_3117_);
lean_inc(v_quotContext_3116_);
v___x_3123_ = l_Lean_addMacroScope(v_quotContext_3116_, v___x_3122_, v_currMacroScope_3117_);
v___x_3124_ = lean_box(0);
v___x_3125_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__5));
lean_inc(v___x_3118_);
v___x_3126_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3118_);
lean_ctor_set(v___x_3126_, 1, v___x_3121_);
lean_ctor_set(v___x_3126_, 2, v___x_3123_);
lean_ctor_set(v___x_3126_, 3, v___x_3125_);
v___x_3127_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_3128_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__7));
v___x_3129_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9);
v___x_3130_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__10));
lean_inc(v_currMacroScope_3117_);
lean_inc(v_quotContext_3116_);
v___x_3131_ = l_Lean_addMacroScope(v_quotContext_3116_, v___x_3130_, v_currMacroScope_3117_);
lean_inc(v___x_3118_);
v___x_3132_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3118_);
lean_ctor_set(v___x_3132_, 1, v___x_3129_);
lean_ctor_set(v___x_3132_, 2, v___x_3131_);
lean_ctor_set(v___x_3132_, 3, v___x_3124_);
v___x_3133_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__12));
v___x_3134_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_3118_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set_tag(v___x_3105_, 1);
lean_ctor_set(v___x_3105_, 2, v___x_3134_);
lean_ctor_set(v___x_3105_, 1, v___x_3133_);
lean_ctor_set(v___x_3105_, 0, v___x_3118_);
v___x_3136_ = v___x_3105_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3152_, 2, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_3118_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set_tag(v___x_3101_, 2);
lean_ctor_set(v___x_3101_, 1, v___x_3137_);
lean_ctor_set(v___x_3101_, 0, v___x_3118_);
v___x_3139_ = v___x_3101_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_inc(v_j_3090_);
v___x_3140_ = l_Nat_reprFast(v_j_3090_);
v___x_3141_ = lean_box(2);
v___x_3142_ = l_Lean_Syntax_mkNumLit(v___x_3140_, v___x_3141_);
v___x_3143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_3118_);
v___x_3144_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3118_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__13));
lean_inc(v___x_3118_);
v___x_3146_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3118_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
lean_inc_ref(v___x_3136_);
lean_inc(v___x_3118_);
v___x_3147_ = l_Lean_Syntax_node7(v___x_3118_, v___x_3128_, v___x_3132_, v___x_3136_, v___x_3139_, v___x_3142_, v___x_3144_, v___x_3136_, v___x_3146_);
lean_inc(v___x_3118_);
v___x_3148_ = l_Lean_Syntax_node1(v___x_3118_, v___x_3127_, v___x_3147_);
lean_inc(v___x_3118_);
v___x_3149_ = l_Lean_Syntax_node2(v___x_3118_, v___x_3120_, v___x_3126_, v___x_3148_);
v___x_3150_ = l_Lean_Syntax_node1(v___x_3118_, v___x_3119_, v___x_3149_);
v_a_3110_ = v___x_3150_;
goto v___jp_3109_;
}
}
}
else
{
lean_object* v_ref_3153_; lean_object* v_quotContext_3154_; lean_object* v_currMacroScope_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3169_; 
v_ref_3153_ = lean_ctor_get(v___y_3092_, 5);
v_quotContext_3154_ = lean_ctor_get(v___y_3092_, 10);
v_currMacroScope_3155_ = lean_ctor_get(v___y_3092_, 11);
v___x_3156_ = l_Lean_SourceInfo_fromRef(v_ref_3153_, v_isZero_3095_);
v___x_3157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_3158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_3159_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_3160_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__7));
v___x_3161_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9);
v___x_3162_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__10));
lean_inc(v_currMacroScope_3155_);
lean_inc(v_quotContext_3154_);
v___x_3163_ = l_Lean_addMacroScope(v_quotContext_3154_, v___x_3162_, v_currMacroScope_3155_);
v___x_3164_ = lean_box(0);
lean_inc(v___x_3156_);
v___x_3165_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3156_);
lean_ctor_set(v___x_3165_, 1, v___x_3161_);
lean_ctor_set(v___x_3165_, 2, v___x_3163_);
lean_ctor_set(v___x_3165_, 3, v___x_3164_);
v___x_3166_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__12));
v___x_3167_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_3156_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set_tag(v___x_3105_, 1);
lean_ctor_set(v___x_3105_, 2, v___x_3167_);
lean_ctor_set(v___x_3105_, 1, v___x_3166_);
lean_ctor_set(v___x_3105_, 0, v___x_3156_);
v___x_3169_ = v___x_3105_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v___x_3166_);
lean_ctor_set(v_reuseFailAlloc_3185_, 2, v___x_3167_);
v___x_3169_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3170_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__2));
lean_inc(v___x_3156_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set_tag(v___x_3101_, 2);
lean_ctor_set(v___x_3101_, 1, v___x_3170_);
lean_ctor_set(v___x_3101_, 0, v___x_3156_);
v___x_3172_ = v___x_3101_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v___x_3170_);
v___x_3172_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_inc(v_j_3090_);
v___x_3173_ = l_Nat_reprFast(v_j_3090_);
v___x_3174_ = lean_box(2);
v___x_3175_ = l_Lean_Syntax_mkNumLit(v___x_3173_, v___x_3174_);
v___x_3176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_3156_);
v___x_3177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3156_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__13));
lean_inc(v___x_3156_);
v___x_3179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3156_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
lean_inc_ref(v___x_3169_);
lean_inc(v___x_3156_);
v___x_3180_ = l_Lean_Syntax_node7(v___x_3156_, v___x_3160_, v___x_3165_, v___x_3169_, v___x_3172_, v___x_3175_, v___x_3177_, v___x_3169_, v___x_3179_);
lean_inc(v___x_3156_);
v___x_3181_ = l_Lean_Syntax_node1(v___x_3156_, v___x_3159_, v___x_3180_);
lean_inc(v___x_3087_);
lean_inc(v___x_3156_);
v___x_3182_ = l_Lean_Syntax_node2(v___x_3156_, v___x_3158_, v___x_3087_, v___x_3181_);
v___x_3183_ = l_Lean_Syntax_node1(v___x_3156_, v___x_3157_, v___x_3182_);
v_a_3110_ = v___x_3183_;
goto v___jp_3109_;
}
}
}
v___jp_3109_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = lean_nat_add(v_j_3090_, v_one_3107_);
lean_dec(v_j_3090_);
v___x_3112_ = lean_array_push(v_bs_3091_, v_a_3110_);
v_i_3089_ = v_n_3108_;
v_j_3090_ = v___x_3111_;
v_bs_3091_ = v___x_3112_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___boxed(lean_object* v_indVal_3191_, lean_object* v___x_3192_, lean_object* v_as_3193_, lean_object* v_i_3194_, lean_object* v_j_3195_, lean_object* v_bs_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg(v_indVal_3191_, v___x_3192_, v_as_3193_, v_i_3194_, v_j_3195_, v_bs_3196_, v___y_3197_);
lean_dec_ref(v_as_3193_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(lean_object* v_a_3200_, lean_object* v_fst_3201_, lean_object* v_____r_3202_, lean_object* v_userNames_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__2___redArg___lam__0___closed__1));
v___x_3212_ = l_Lean_Core_mkFreshUserName(v___x_3211_, v___y_3208_, v___y_3209_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3226_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3215_ = v___x_3212_;
v_isShared_3216_ = v_isSharedCheck_3226_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3212_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3226_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3217_ = lean_mk_syntax_ident(v_a_3213_);
v___x_3218_ = l_Lean_LocalDecl_type(v_a_3200_);
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3217_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = lean_array_push(v_fst_3201_, v___x_3219_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_ctor_set(v___x_3221_, 1, v_userNames_3203_);
v___x_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 0, v___x_3222_);
v___x_3224_ = v___x_3215_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec_ref(v_userNames_3203_);
lean_dec(v_fst_3201_);
v_a_3227_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3212_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3212_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___boxed(lean_object* v_a_3235_, lean_object* v_fst_3236_, lean_object* v_____r_3237_, lean_object* v_userNames_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(v_a_3235_, v_fst_3236_, v_____r_3237_, v_userNames_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec_ref(v_a_3235_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg(lean_object* v_upperBound_3247_, lean_object* v_indVal_3248_, lean_object* v_xs_3249_, lean_object* v_a_3250_, lean_object* v_b_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___y_3260_; uint8_t v___x_3282_; 
v___x_3282_ = lean_nat_dec_lt(v_a_3250_, v_upperBound_3247_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; 
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec_ref(v___y_3254_);
lean_dec(v_a_3250_);
v___x_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3283_, 0, v_b_3251_);
return v___x_3283_;
}
else
{
lean_object* v_numParams_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_numParams_3284_ = lean_ctor_get(v_indVal_3248_, 1);
v___x_3285_ = l_Lean_instInhabitedExpr;
v___x_3286_ = lean_nat_add(v_numParams_3284_, v_a_3250_);
v___x_3287_ = lean_array_get_borrowed(v___x_3285_, v_xs_3249_, v___x_3286_);
lean_dec(v___x_3286_);
v___x_3288_ = l_Lean_Expr_fvarId_x21(v___x_3287_);
lean_inc_ref(v___y_3254_);
v___x_3289_ = l_Lean_FVarId_getDecl___redArg(v___x_3288_, v___y_3254_, v___y_3256_, v___y_3257_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v_fst_3291_; lean_object* v_snd_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref(v___x_3289_);
v_fst_3291_ = lean_ctor_get(v_b_3251_, 0);
lean_inc(v_fst_3291_);
v_snd_3292_ = lean_ctor_get(v_b_3251_, 1);
lean_inc(v_snd_3292_);
lean_dec_ref(v_b_3251_);
v___x_3293_ = l_Lean_LocalDecl_userName(v_a_3290_);
v___x_3294_ = l_Lean_Name_hasMacroScopes(v___x_3293_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3295_ = lean_array_push(v_snd_3292_, v___x_3293_);
v___x_3296_ = lean_box(0);
lean_inc(v___y_3257_);
lean_inc_ref(v___y_3256_);
v___x_3297_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(v_a_3290_, v_fst_3291_, v___x_3296_, v___x_3295_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v_a_3290_);
v___y_3260_ = v___x_3297_;
goto v___jp_3259_;
}
else
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_dec(v___x_3293_);
v___x_3298_ = lean_box(0);
lean_inc(v___y_3257_);
lean_inc_ref(v___y_3256_);
v___x_3299_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0(v_a_3290_, v_fst_3291_, v___x_3298_, v_snd_3292_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v_a_3290_);
v___y_3260_ = v___x_3299_;
goto v___jp_3259_;
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec_ref(v___y_3254_);
lean_dec_ref(v_b_3251_);
lean_dec(v_a_3250_);
v_a_3300_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3289_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3289_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
v___jp_3259_:
{
if (lean_obj_tag(v___y_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3273_; 
v_a_3261_ = lean_ctor_get(v___y_3260_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___y_3260_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3263_ = v___y_3260_;
v_isShared_3264_ = v_isSharedCheck_3273_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___y_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3273_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
if (lean_obj_tag(v_a_3261_) == 0)
{
lean_object* v_a_3265_; lean_object* v___x_3267_; 
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec_ref(v___y_3254_);
lean_dec(v_a_3250_);
v_a_3265_ = lean_ctor_get(v_a_3261_, 0);
lean_inc(v_a_3265_);
lean_dec_ref(v_a_3261_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v_a_3265_);
v___x_3267_ = v___x_3263_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3265_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_del_object(v___x_3263_);
v_a_3269_ = lean_ctor_get(v_a_3261_, 0);
lean_inc(v_a_3269_);
lean_dec_ref(v_a_3261_);
v___x_3270_ = lean_unsigned_to_nat(1u);
v___x_3271_ = lean_nat_add(v_a_3250_, v___x_3270_);
lean_dec(v_a_3250_);
v_a_3250_ = v___x_3271_;
v_b_3251_ = v_a_3269_;
goto _start;
}
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec_ref(v___y_3254_);
lean_dec(v_a_3250_);
v_a_3274_ = lean_ctor_get(v___y_3260_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___y_3260_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___y_3260_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___y_3260_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg___boxed(lean_object* v_upperBound_3308_, lean_object* v_indVal_3309_, lean_object* v_xs_3310_, lean_object* v_a_3311_, lean_object* v_b_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg(v_upperBound_3308_, v_indVal_3309_, v_xs_3310_, v_a_3311_, v_b_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3316_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec_ref(v_xs_3310_);
lean_dec_ref(v_indVal_3309_);
lean_dec(v_upperBound_3308_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__3(size_t v_sz_3321_, size_t v_i_3322_, lean_object* v_bs_3323_){
_start:
{
uint8_t v___x_3324_; 
v___x_3324_ = lean_usize_dec_lt(v_i_3322_, v_sz_3321_);
if (v___x_3324_ == 0)
{
return v_bs_3323_;
}
else
{
lean_object* v_v_3325_; lean_object* v___x_3326_; lean_object* v_bs_x27_3327_; size_t v___x_3328_; size_t v___x_3329_; lean_object* v___x_3330_; 
v_v_3325_ = lean_array_uget(v_bs_3323_, v_i_3322_);
v___x_3326_ = lean_unsigned_to_nat(0u);
v_bs_x27_3327_ = lean_array_uset(v_bs_3323_, v_i_3322_, v___x_3326_);
v___x_3328_ = ((size_t)1ULL);
v___x_3329_ = lean_usize_add(v_i_3322_, v___x_3328_);
v___x_3330_ = lean_array_uset(v_bs_x27_3327_, v_i_3322_, v_v_3325_);
v_i_3322_ = v___x_3329_;
v_bs_3323_ = v___x_3330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__3___boxed(lean_object* v_sz_3332_, lean_object* v_i_3333_, lean_object* v_bs_3334_){
_start:
{
size_t v_sz_boxed_3335_; size_t v_i_boxed_3336_; lean_object* v_res_3337_; 
v_sz_boxed_3335_ = lean_unbox_usize(v_sz_3332_);
lean_dec(v_sz_3332_);
v_i_boxed_3336_ = lean_unbox_usize(v_i_3333_);
lean_dec(v_i_3333_);
v_res_3337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__3(v_sz_boxed_3335_, v_i_boxed_3336_, v_bs_3334_);
return v_res_3337_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__0));
v___x_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
return v___x_3341_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__2));
v___x_3344_ = l_String_toRawSubstring_x27(v___x_3343_);
return v___x_3344_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__9));
v___x_3361_ = l_String_toRawSubstring_x27(v___x_3360_);
return v___x_3361_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__18));
v___x_3382_ = l_String_toRawSubstring_x27(v___x_3381_);
return v___x_3382_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__25));
v___x_3397_ = l_String_toRawSubstring_x27(v___x_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0(lean_object* v_numFields_3409_, lean_object* v_indVal_3410_, lean_object* v_ctx_3411_, lean_object* v___x_3412_, lean_object* v___x_3413_, lean_object* v_head_3414_, lean_object* v_xs_3415_, lean_object* v_x_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_stx_3425_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = lean_unsigned_to_nat(0u);
v___x_3430_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__1);
lean_inc_ref(v___y_3421_);
v___x_3431_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg(v_numFields_3409_, v_indVal_3410_, v_xs_3415_, v___x_3429_, v___x_3430_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v_fst_3433_; lean_object* v_snd_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3603_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref(v___x_3431_);
v_fst_3433_ = lean_ctor_get(v_a_3432_, 0);
v_snd_3434_ = lean_ctor_get(v_a_3432_, 1);
v_isSharedCheck_3603_ = !lean_is_exclusive(v_a_3432_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3436_ = v_a_3432_;
v_isShared_3437_ = v_isSharedCheck_3603_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_snd_3434_);
lean_inc(v_fst_3433_);
lean_dec(v_a_3432_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3603_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v_auxFunNames_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; size_t v_sz_3441_; size_t v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v_a_3447_; lean_object* v_userNamesOpt_3449_; lean_object* v___y_3450_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v_auxFunNames_3438_ = lean_ctor_get(v_ctx_3411_, 2);
v___x_3439_ = lean_array_get_borrowed(v___x_3412_, v_auxFunNames_3438_, v___x_3429_);
lean_inc(v___x_3439_);
v___x_3440_ = lean_mk_syntax_ident(v___x_3439_);
v_sz_3441_ = lean_array_size(v_fst_3433_);
v___x_3442_ = ((size_t)0ULL);
lean_inc(v_fst_3433_);
v___x_3443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__0(v_sz_3441_, v___x_3442_, v_fst_3433_);
v___x_3444_ = lean_array_get_size(v_fst_3433_);
v___x_3445_ = lean_mk_empty_array_with_capacity(v___x_3444_);
lean_inc_ref(v___y_3421_);
v___x_3446_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg(v_indVal_3410_, v___x_3440_, v_fst_3433_, v___x_3444_, v___x_3429_, v___x_3445_, v___y_3421_);
lean_dec(v_fst_3433_);
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref(v___x_3446_);
v___x_3563_ = lean_array_get_size(v_snd_3434_);
v___x_3564_ = lean_nat_dec_eq(v___x_3444_, v___x_3563_);
if (v___x_3564_ == 0)
{
lean_object* v_ref_3565_; lean_object* v_quotContext_3566_; lean_object* v_currMacroScope_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_dec(v_snd_3434_);
v_ref_3565_ = lean_ctor_get(v___y_3421_, 5);
v_quotContext_3566_ = lean_ctor_get(v___y_3421_, 10);
v_currMacroScope_3567_ = lean_ctor_get(v___y_3421_, 11);
v___x_3568_ = l_Lean_SourceInfo_fromRef(v_ref_3565_, v___x_3564_);
v___x_3569_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19);
v___x_3570_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__20));
lean_inc(v_currMacroScope_3567_);
lean_inc(v_quotContext_3566_);
v___x_3571_ = l_Lean_addMacroScope(v_quotContext_3566_, v___x_3570_, v_currMacroScope_3567_);
v___x_3572_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__24));
v___x_3573_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3568_);
lean_ctor_set(v___x_3573_, 1, v___x_3569_);
lean_ctor_set(v___x_3573_, 2, v___x_3571_);
lean_ctor_set(v___x_3573_, 3, v___x_3572_);
v_userNamesOpt_3449_ = v___x_3573_;
v___y_3450_ = v___y_3421_;
goto v___jp_3448_;
}
else
{
lean_object* v_ref_3574_; lean_object* v_quotContext_3575_; lean_object* v_currMacroScope_3576_; uint8_t v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; size_t v_sz_3590_; lean_object* v___x_3591_; size_t v_sz_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_ref_3574_ = lean_ctor_get(v___y_3421_, 5);
v_quotContext_3575_ = lean_ctor_get(v___y_3421_, 10);
v_currMacroScope_3576_ = lean_ctor_get(v___y_3421_, 11);
v___x_3577_ = 0;
v___x_3578_ = l_Lean_SourceInfo_fromRef(v_ref_3574_, v___x_3577_);
v___x_3579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_3580_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26);
v___x_3581_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__27));
lean_inc(v_currMacroScope_3576_);
lean_inc(v_quotContext_3575_);
v___x_3582_ = l_Lean_addMacroScope(v_quotContext_3575_, v___x_3581_, v_currMacroScope_3576_);
v___x_3583_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__30));
lean_inc(v___x_3578_);
v___x_3584_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3578_);
lean_ctor_set(v___x_3584_, 1, v___x_3580_);
lean_ctor_set(v___x_3584_, 2, v___x_3582_);
lean_ctor_set(v___x_3584_, 3, v___x_3583_);
v___x_3585_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_3586_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__15));
v___x_3587_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___lam__0___closed__16));
lean_inc(v___x_3578_);
v___x_3588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3578_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
v___x_3589_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v_sz_3590_ = lean_array_size(v_snd_3434_);
v___x_3591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__4(v_sz_3590_, v___x_3442_, v_snd_3434_);
v_sz_3592_ = lean_array_size(v___x_3591_);
v___x_3593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__1(v_sz_3592_, v___x_3442_, v___x_3591_);
v___x_3594_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__6);
v___x_3595_ = l_Lean_mkSepArray(v___x_3593_, v___x_3594_);
lean_dec_ref(v___x_3593_);
v___x_3596_ = l_Array_append___redArg(v___x_3589_, v___x_3595_);
lean_dec_ref(v___x_3595_);
lean_inc(v___x_3578_);
v___x_3597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3578_);
lean_ctor_set(v___x_3597_, 1, v___x_3585_);
lean_ctor_set(v___x_3597_, 2, v___x_3596_);
v___x_3598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__43));
lean_inc(v___x_3578_);
v___x_3599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3578_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
lean_inc(v___x_3578_);
v___x_3600_ = l_Lean_Syntax_node3(v___x_3578_, v___x_3586_, v___x_3588_, v___x_3597_, v___x_3599_);
lean_inc(v___x_3578_);
v___x_3601_ = l_Lean_Syntax_node1(v___x_3578_, v___x_3585_, v___x_3600_);
v___x_3602_ = l_Lean_Syntax_node2(v___x_3578_, v___x_3579_, v___x_3584_, v___x_3601_);
v_userNamesOpt_3449_ = v___x_3602_;
v___y_3450_ = v___y_3421_;
goto v___jp_3448_;
}
v___jp_3448_:
{
uint8_t v___x_3451_; 
v___x_3451_ = lean_nat_dec_eq(v_numFields_3409_, v___x_3429_);
if (v___x_3451_ == 0)
{
lean_object* v_ref_3452_; lean_object* v_quotContext_3453_; lean_object* v_currMacroScope_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; 
v_ref_3452_ = lean_ctor_get(v___y_3450_, 5);
lean_inc(v_ref_3452_);
v_quotContext_3453_ = lean_ctor_get(v___y_3450_, 10);
lean_inc(v_quotContext_3453_);
v_currMacroScope_3454_ = lean_ctor_get(v___y_3450_, 11);
lean_inc(v_currMacroScope_3454_);
lean_dec_ref(v___y_3450_);
v___x_3455_ = l_Lean_SourceInfo_fromRef(v_ref_3452_, v___x_3451_);
lean_dec(v_ref_3452_);
v___x_3456_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_3457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__39));
v___x_3458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__41));
v___x_3459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__6));
v___x_3460_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__6));
lean_inc(v___x_3455_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set_tag(v___x_3436_, 2);
lean_ctor_set(v___x_3436_, 1, v___x_3460_);
lean_ctor_set(v___x_3436_, 0, v___x_3455_);
v___x_3462_ = v___x_3436_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; size_t v_sz_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; size_t v_sz_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__8));
v___x_3464_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__10);
v___x_3465_ = lean_box(0);
lean_inc(v_currMacroScope_3454_);
lean_inc(v_quotContext_3453_);
v___x_3466_ = l_Lean_addMacroScope(v_quotContext_3453_, v___x_3465_, v_currMacroScope_3454_);
v___x_3467_ = lean_box(0);
v___x_3468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__28));
lean_inc(v___x_3455_);
v___x_3469_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3455_);
lean_ctor_set(v___x_3469_, 1, v___x_3464_);
lean_ctor_set(v___x_3469_, 2, v___x_3466_);
lean_ctor_set(v___x_3469_, 3, v___x_3468_);
lean_inc(v___x_3455_);
v___x_3470_ = l_Lean_Syntax_node1(v___x_3455_, v___x_3463_, v___x_3469_);
lean_inc(v___x_3455_);
v___x_3471_ = l_Lean_Syntax_node2(v___x_3455_, v___x_3459_, v___x_3462_, v___x_3470_);
v___x_3472_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__3);
v___x_3473_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__5));
lean_inc(v_currMacroScope_3454_);
lean_inc(v_quotContext_3453_);
v___x_3474_ = l_Lean_addMacroScope(v_quotContext_3453_, v___x_3473_, v_currMacroScope_3454_);
v___x_3475_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__8));
lean_inc(v___x_3455_);
v___x_3476_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3455_);
lean_ctor_set(v___x_3476_, 1, v___x_3472_);
lean_ctor_set(v___x_3476_, 2, v___x_3474_);
lean_ctor_set(v___x_3476_, 3, v___x_3475_);
v___x_3477_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_3478_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10);
v___x_3479_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__11));
lean_inc(v_currMacroScope_3454_);
lean_inc(v_quotContext_3453_);
v___x_3480_ = l_Lean_addMacroScope(v_quotContext_3453_, v___x_3479_, v_currMacroScope_3454_);
v___x_3481_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__15));
lean_inc(v___x_3455_);
v___x_3482_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3455_);
lean_ctor_set(v___x_3482_, 1, v___x_3478_);
lean_ctor_set(v___x_3482_, 2, v___x_3480_);
lean_ctor_set(v___x_3482_, 3, v___x_3481_);
v___x_3483_ = lean_box(2);
lean_inc_ref(v___x_3413_);
v___x_3484_ = l_Lean_Syntax_mkStrLit(v___x_3413_, v___x_3483_);
lean_inc(v_numFields_3409_);
v___x_3485_ = l_Nat_reprFast(v_numFields_3409_);
v___x_3486_ = l_Lean_Syntax_mkNumLit(v___x_3485_, v___x_3483_);
lean_inc(v___x_3455_);
v___x_3487_ = l_Lean_Syntax_node4(v___x_3455_, v___x_3477_, v___x_3482_, v___x_3484_, v___x_3486_, v_userNamesOpt_3449_);
lean_inc(v___x_3455_);
v___x_3488_ = l_Lean_Syntax_node2(v___x_3455_, v___x_3456_, v___x_3476_, v___x_3487_);
v___x_3489_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__25));
lean_inc(v___x_3455_);
v___x_3490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3455_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
lean_inc_ref(v___x_3490_);
lean_inc(v___x_3471_);
lean_inc(v___x_3455_);
v___x_3491_ = l_Lean_Syntax_node3(v___x_3455_, v___x_3458_, v___x_3471_, v___x_3488_, v___x_3490_);
v___x_3492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__42));
lean_inc(v___x_3455_);
v___x_3493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3455_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__10, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__10_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__10);
v___x_3495_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__11));
lean_inc(v_currMacroScope_3454_);
lean_inc(v_quotContext_3453_);
v___x_3496_ = l_Lean_addMacroScope(v_quotContext_3453_, v___x_3495_, v_currMacroScope_3454_);
v___x_3497_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__15));
lean_inc(v___x_3455_);
v___x_3498_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3455_);
lean_ctor_set(v___x_3498_, 1, v___x_3494_);
lean_ctor_set(v___x_3498_, 2, v___x_3496_);
lean_ctor_set(v___x_3498_, 3, v___x_3497_);
lean_inc(v___x_3455_);
v___x_3499_ = l_Lean_Syntax_node3(v___x_3455_, v___x_3457_, v___x_3491_, v___x_3493_, v___x_3498_);
v___x_3500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__16));
v___x_3501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__17));
lean_inc(v___x_3455_);
v___x_3502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3455_);
lean_ctor_set(v___x_3502_, 1, v___x_3500_);
v___x_3503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__19));
v___x_3504_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9, &l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__9);
v___x_3505_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg___closed__10));
v___x_3506_ = l_Lean_addMacroScope(v_quotContext_3453_, v___x_3505_, v_currMacroScope_3454_);
lean_inc(v___x_3455_);
v___x_3507_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3455_);
lean_ctor_set(v___x_3507_, 1, v___x_3504_);
lean_ctor_set(v___x_3507_, 2, v___x_3506_);
lean_ctor_set(v___x_3507_, 3, v___x_3467_);
lean_inc(v___x_3455_);
v___x_3508_ = l_Lean_Syntax_node1(v___x_3455_, v___x_3477_, v___x_3507_);
v___x_3509_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_3455_);
v___x_3510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3455_);
lean_ctor_set(v___x_3510_, 1, v___x_3477_);
lean_ctor_set(v___x_3510_, 2, v___x_3509_);
v___x_3511_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__7));
lean_inc(v___x_3455_);
v___x_3512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3455_);
lean_ctor_set(v___x_3512_, 1, v___x_3511_);
v___x_3513_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__0));
v___x_3514_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__1));
lean_inc(v___x_3455_);
v___x_3515_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3455_);
lean_ctor_set(v___x_3515_, 1, v___x_3513_);
v___x_3516_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__3));
v___x_3517_ = l_Array_zip___redArg(v___x_3443_, v_a_3447_);
lean_dec(v_a_3447_);
v_sz_3518_ = lean_array_size(v___x_3517_);
lean_inc_ref(v___x_3510_);
lean_inc(v___x_3455_);
v___x_3519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__2(v___x_3455_, v___x_3510_, v_sz_3518_, v___x_3442_, v___x_3517_);
v___x_3520_ = l_Array_append___redArg(v___x_3509_, v___x_3519_);
lean_dec_ref(v___x_3519_);
v___x_3521_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__2___closed__1));
v___x_3522_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__5));
v___x_3523_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__6));
lean_inc(v___x_3455_);
v___x_3524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3455_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = lean_mk_syntax_ident(v_head_3414_);
v_sz_3526_ = lean_array_size(v___x_3443_);
v___x_3527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__3(v_sz_3526_, v___x_3442_, v___x_3443_);
v___x_3528_ = l_Array_append___redArg(v___x_3509_, v___x_3527_);
lean_dec_ref(v___x_3527_);
lean_inc(v___x_3455_);
v___x_3529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3455_);
lean_ctor_set(v___x_3529_, 1, v___x_3477_);
lean_ctor_set(v___x_3529_, 2, v___x_3528_);
lean_inc(v___x_3455_);
v___x_3530_ = l_Lean_Syntax_node2(v___x_3455_, v___x_3456_, v___x_3525_, v___x_3529_);
lean_inc(v___x_3455_);
v___x_3531_ = l_Lean_Syntax_node1(v___x_3455_, v___x_3477_, v___x_3530_);
lean_inc(v___x_3455_);
v___x_3532_ = l_Lean_Syntax_node2(v___x_3455_, v___x_3522_, v___x_3524_, v___x_3531_);
lean_inc_ref(v___x_3510_);
lean_inc(v___x_3455_);
v___x_3533_ = l_Lean_Syntax_node2(v___x_3455_, v___x_3521_, v___x_3532_, v___x_3510_);
v___x_3534_ = lean_array_push(v___x_3520_, v___x_3533_);
lean_inc(v___x_3455_);
v___x_3535_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3455_);
lean_ctor_set(v___x_3535_, 1, v___x_3477_);
lean_ctor_set(v___x_3535_, 2, v___x_3534_);
lean_inc(v___x_3455_);
v___x_3536_ = l_Lean_Syntax_node1(v___x_3455_, v___x_3516_, v___x_3535_);
lean_inc(v___x_3455_);
v___x_3537_ = l_Lean_Syntax_node2(v___x_3455_, v___x_3514_, v___x_3515_, v___x_3536_);
lean_inc(v___x_3455_);
v___x_3538_ = l_Lean_Syntax_node4(v___x_3455_, v___x_3503_, v___x_3508_, v___x_3510_, v___x_3512_, v___x_3537_);
lean_inc(v___x_3455_);
v___x_3539_ = l_Lean_Syntax_node2(v___x_3455_, v___x_3501_, v___x_3502_, v___x_3538_);
lean_inc(v___x_3455_);
v___x_3540_ = l_Lean_Syntax_node3(v___x_3455_, v___x_3458_, v___x_3471_, v___x_3539_, v___x_3490_);
lean_inc(v___x_3455_);
v___x_3541_ = l_Lean_Syntax_node1(v___x_3455_, v___x_3477_, v___x_3540_);
v___x_3542_ = l_Lean_Syntax_node2(v___x_3455_, v___x_3456_, v___x_3499_, v___x_3541_);
v_stx_3425_ = v___x_3542_;
goto v___jp_3424_;
}
}
else
{
lean_object* v_ref_3544_; uint8_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3550_; 
lean_dec(v_userNamesOpt_3449_);
lean_dec(v_a_3447_);
v_ref_3544_ = lean_ctor_get(v___y_3450_, 5);
lean_inc(v_ref_3544_);
lean_dec_ref(v___y_3450_);
v___x_3545_ = 0;
v___x_3546_ = l_Lean_SourceInfo_fromRef(v_ref_3544_, v___x_3545_);
lean_dec(v_ref_3544_);
v___x_3547_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__17));
v___x_3548_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct___closed__6));
lean_inc(v___x_3546_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set_tag(v___x_3436_, 2);
lean_ctor_set(v___x_3436_, 1, v___x_3548_);
lean_ctor_set(v___x_3436_, 0, v___x_3546_);
v___x_3550_ = v___x_3436_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; size_t v_sz_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3551_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_3552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_3553_ = lean_mk_syntax_ident(v_head_3414_);
v___x_3554_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v_sz_3555_ = lean_array_size(v___x_3443_);
v___x_3556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__3(v_sz_3555_, v___x_3442_, v___x_3443_);
v___x_3557_ = l_Array_append___redArg(v___x_3554_, v___x_3556_);
lean_dec_ref(v___x_3556_);
lean_inc(v___x_3546_);
v___x_3558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3546_);
lean_ctor_set(v___x_3558_, 1, v___x_3551_);
lean_ctor_set(v___x_3558_, 2, v___x_3557_);
lean_inc(v___x_3546_);
v___x_3559_ = l_Lean_Syntax_node2(v___x_3546_, v___x_3552_, v___x_3553_, v___x_3558_);
lean_inc(v___x_3546_);
v___x_3560_ = l_Lean_Syntax_node1(v___x_3546_, v___x_3551_, v___x_3559_);
v___x_3561_ = l_Lean_Syntax_node2(v___x_3546_, v___x_3547_, v___x_3550_, v___x_3560_);
v_stx_3425_ = v___x_3561_;
goto v___jp_3424_;
}
}
}
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
lean_dec_ref(v___y_3421_);
lean_dec(v_head_3414_);
lean_dec_ref(v___x_3413_);
lean_dec(v___x_3412_);
lean_dec_ref(v_indVal_3410_);
lean_dec(v_numFields_3409_);
v_a_3604_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3431_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3431_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
v___jp_3424_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3413_);
lean_ctor_set(v___x_3426_, 1, v_stx_3425_);
v___x_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v_numFields_3409_);
v___x_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
return v___x_3428_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___boxed(lean_object* v_numFields_3612_, lean_object* v_indVal_3613_, lean_object* v_ctx_3614_, lean_object* v___x_3615_, lean_object* v___x_3616_, lean_object* v_head_3617_, lean_object* v_xs_3618_, lean_object* v_x_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0(v_numFields_3612_, v_indVal_3613_, v_ctx_3614_, v___x_3615_, v___x_3616_, v_head_3617_, v_xs_3618_, v_x_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___y_3623_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec_ref(v_x_3619_);
lean_dec_ref(v_xs_3618_);
lean_dec_ref(v_ctx_3614_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___redArg(lean_object* v_ctx_3628_, lean_object* v_indVal_3629_, lean_object* v_as_x27_3630_, lean_object* v_b_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
if (lean_obj_tag(v_as_x27_3630_) == 0)
{
lean_object* v___x_3639_; 
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v_indVal_3629_);
lean_dec_ref(v_ctx_3628_);
v___x_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3639_, 0, v_b_3631_);
return v___x_3639_;
}
else
{
lean_object* v_head_3640_; lean_object* v_tail_3641_; lean_object* v___x_3642_; 
v_head_3640_ = lean_ctor_get(v_as_x27_3630_, 0);
lean_inc(v_head_3640_);
v_tail_3641_ = lean_ctor_get(v_as_x27_3630_, 1);
lean_inc(v_tail_3641_);
lean_dec_ref(v_as_x27_3630_);
lean_inc(v___y_3637_);
lean_inc_ref(v___y_3636_);
lean_inc(v___y_3635_);
lean_inc_ref(v___y_3634_);
lean_inc(v___y_3633_);
lean_inc_ref(v___y_3632_);
lean_inc(v_head_3640_);
v___x_3642_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0(v_head_3640_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v_toConstantVal_3644_; lean_object* v_numFields_3645_; lean_object* v_type_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___f_3650_; uint8_t v___x_3651_; lean_object* v___x_3652_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref(v___x_3642_);
v_toConstantVal_3644_ = lean_ctor_get(v_a_3643_, 0);
lean_inc_ref(v_toConstantVal_3644_);
v_numFields_3645_ = lean_ctor_get(v_a_3643_, 4);
lean_inc(v_numFields_3645_);
lean_dec(v_a_3643_);
v_type_3646_ = lean_ctor_get(v_toConstantVal_3644_, 2);
lean_inc_ref(v_type_3646_);
lean_dec_ref(v_toConstantVal_3644_);
v___x_3647_ = lean_box(0);
lean_inc(v_head_3640_);
v___x_3648_ = lean_erase_macro_scopes(v_head_3640_);
v___x_3649_ = l_Lean_Name_getString_x21(v___x_3648_);
lean_dec(v___x_3648_);
lean_inc_ref(v_ctx_3628_);
lean_inc_ref(v_indVal_3629_);
v___f_3650_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___boxed), 15, 6);
lean_closure_set(v___f_3650_, 0, v_numFields_3645_);
lean_closure_set(v___f_3650_, 1, v_indVal_3629_);
lean_closure_set(v___f_3650_, 2, v_ctx_3628_);
lean_closure_set(v___f_3650_, 3, v___x_3647_);
lean_closure_set(v___f_3650_, 4, v___x_3649_);
lean_closure_set(v___f_3650_, 5, v_head_3640_);
v___x_3651_ = 0;
lean_inc(v___y_3637_);
lean_inc_ref(v___y_3636_);
lean_inc(v___y_3635_);
lean_inc_ref(v___y_3634_);
lean_inc(v___y_3633_);
lean_inc_ref(v___y_3632_);
v___x_3652_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(v_type_3646_, v___f_3650_, v___x_3651_, v___x_3651_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3654_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref(v___x_3652_);
v___x_3654_ = lean_array_push(v_b_3631_, v_a_3653_);
v_as_x27_3630_ = v_tail_3641_;
v_b_3631_ = v___x_3654_;
goto _start;
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_dec(v_tail_3641_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v_b_3631_);
lean_dec_ref(v_indVal_3629_);
lean_dec_ref(v_ctx_3628_);
v_a_3656_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3652_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3652_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v_tail_3641_);
lean_dec(v_head_3640_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v_b_3631_);
lean_dec_ref(v_indVal_3629_);
lean_dec_ref(v_ctx_3628_);
v_a_3664_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3642_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3642_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___redArg___boxed(lean_object* v_ctx_3672_, lean_object* v_indVal_3673_, lean_object* v_as_x27_3674_, lean_object* v_b_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___redArg(v_ctx_3672_, v_indVal_3673_, v_as_x27_3674_, v_b_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg(lean_object* v_indVal_3684_, lean_object* v_ctx_3685_, lean_object* v_as_3686_, lean_object* v_as_x27_3687_, lean_object* v_b_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
if (lean_obj_tag(v_as_x27_3687_) == 0)
{
lean_object* v___x_3696_; 
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec_ref(v_ctx_3685_);
lean_dec_ref(v_indVal_3684_);
v___x_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3696_, 0, v_b_3688_);
return v___x_3696_;
}
else
{
lean_object* v_head_3697_; lean_object* v_tail_3698_; lean_object* v___x_3699_; 
v_head_3697_ = lean_ctor_get(v_as_x27_3687_, 0);
lean_inc(v_head_3697_);
v_tail_3698_ = lean_ctor_get(v_as_x27_3687_, 1);
lean_inc(v_tail_3698_);
lean_dec_ref(v_as_x27_3687_);
lean_inc(v___y_3694_);
lean_inc_ref(v___y_3693_);
lean_inc(v___y_3692_);
lean_inc_ref(v___y_3691_);
lean_inc(v___y_3690_);
lean_inc_ref(v___y_3689_);
lean_inc(v_head_3697_);
v___x_3699_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0(v_head_3697_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v_toConstantVal_3701_; lean_object* v_numFields_3702_; lean_object* v_type_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___f_3707_; uint8_t v___x_3708_; lean_object* v___x_3709_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_a_3700_);
lean_dec_ref(v___x_3699_);
v_toConstantVal_3701_ = lean_ctor_get(v_a_3700_, 0);
lean_inc_ref(v_toConstantVal_3701_);
v_numFields_3702_ = lean_ctor_get(v_a_3700_, 4);
lean_inc(v_numFields_3702_);
lean_dec(v_a_3700_);
v_type_3703_ = lean_ctor_get(v_toConstantVal_3701_, 2);
lean_inc_ref(v_type_3703_);
lean_dec_ref(v_toConstantVal_3701_);
v___x_3704_ = lean_box(0);
lean_inc(v_head_3697_);
v___x_3705_ = lean_erase_macro_scopes(v_head_3697_);
v___x_3706_ = l_Lean_Name_getString_x21(v___x_3705_);
lean_dec(v___x_3705_);
lean_inc_ref(v_ctx_3685_);
lean_inc_ref(v_indVal_3684_);
v___f_3707_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___boxed), 15, 6);
lean_closure_set(v___f_3707_, 0, v_numFields_3702_);
lean_closure_set(v___f_3707_, 1, v_indVal_3684_);
lean_closure_set(v___f_3707_, 2, v_ctx_3685_);
lean_closure_set(v___f_3707_, 3, v___x_3704_);
lean_closure_set(v___f_3707_, 4, v___x_3706_);
lean_closure_set(v___f_3707_, 5, v_head_3697_);
v___x_3708_ = 0;
lean_inc(v___y_3694_);
lean_inc_ref(v___y_3693_);
lean_inc(v___y_3692_);
lean_inc_ref(v___y_3691_);
lean_inc(v___y_3690_);
lean_inc_ref(v___y_3689_);
v___x_3709_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__4___redArg(v_type_3703_, v___f_3707_, v___x_3708_, v___x_3708_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref(v___x_3709_);
v___x_3711_ = lean_array_push(v_b_3688_, v_a_3710_);
v___x_3712_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___redArg(v_ctx_3685_, v_indVal_3684_, v_tail_3698_, v___x_3711_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
return v___x_3712_;
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_dec(v_tail_3698_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec_ref(v_b_3688_);
lean_dec_ref(v_ctx_3685_);
lean_dec_ref(v_indVal_3684_);
v_a_3713_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3709_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3709_);
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
lean_dec(v_tail_3698_);
lean_dec(v_head_3697_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec_ref(v_b_3688_);
lean_dec_ref(v_ctx_3685_);
lean_dec_ref(v_indVal_3684_);
v_a_3721_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3699_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3699_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___boxed(lean_object* v_indVal_3729_, lean_object* v_ctx_3730_, lean_object* v_as_3731_, lean_object* v_as_x27_3732_, lean_object* v_b_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg(v_indVal_3729_, v_ctx_3730_, v_as_3731_, v_as_x27_3732_, v_b_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v_as_3731_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__7(size_t v_sz_3742_, size_t v_i_3743_, lean_object* v_bs_3744_){
_start:
{
uint8_t v___x_3745_; 
v___x_3745_ = lean_usize_dec_lt(v_i_3743_, v_sz_3742_);
if (v___x_3745_ == 0)
{
return v_bs_3744_;
}
else
{
lean_object* v_v_3746_; lean_object* v_fst_3747_; lean_object* v___x_3748_; lean_object* v_bs_x27_3749_; size_t v___x_3750_; size_t v___x_3751_; lean_object* v___x_3752_; 
v_v_3746_ = lean_array_uget_borrowed(v_bs_3744_, v_i_3743_);
v_fst_3747_ = lean_ctor_get(v_v_3746_, 0);
lean_inc(v_fst_3747_);
v___x_3748_ = lean_unsigned_to_nat(0u);
v_bs_x27_3749_ = lean_array_uset(v_bs_3744_, v_i_3743_, v___x_3748_);
v___x_3750_ = ((size_t)1ULL);
v___x_3751_ = lean_usize_add(v_i_3743_, v___x_3750_);
v___x_3752_ = lean_array_uset(v_bs_x27_3749_, v_i_3743_, v_fst_3747_);
v_i_3743_ = v___x_3751_;
v_bs_3744_ = v___x_3752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__7___boxed(lean_object* v_sz_3754_, lean_object* v_i_3755_, lean_object* v_bs_3756_){
_start:
{
size_t v_sz_boxed_3757_; size_t v_i_boxed_3758_; lean_object* v_res_3759_; 
v_sz_boxed_3757_ = lean_unbox_usize(v_sz_3754_);
lean_dec(v_sz_3754_);
v_i_boxed_3758_ = lean_unbox_usize(v_i_3755_);
lean_dec(v_i_3755_);
v_res_3759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__7(v_sz_boxed_3757_, v_i_boxed_3758_, v_bs_3756_);
return v_res_3759_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___lam__0(lean_object* v_x_3760_, lean_object* v_x_3761_){
_start:
{
lean_object* v_snd_3762_; lean_object* v_snd_3763_; uint8_t v___x_3764_; 
v_snd_3762_ = lean_ctor_get(v_x_3760_, 1);
v_snd_3763_ = lean_ctor_get(v_x_3761_, 1);
v___x_3764_ = lean_nat_dec_lt(v_snd_3762_, v_snd_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___lam__0___boxed(lean_object* v_x_3765_, lean_object* v_x_3766_){
_start:
{
uint8_t v_res_3767_; lean_object* v_r_3768_; 
v_res_3767_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___lam__0(v_x_3765_, v_x_3766_);
lean_dec_ref(v_x_3766_);
lean_dec_ref(v_x_3765_);
v_r_3768_ = lean_box(v_res_3767_);
return v_r_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg(lean_object* v_as_3770_, lean_object* v_lo_3771_, lean_object* v_hi_3772_){
_start:
{
uint8_t v___x_3773_; 
v___x_3773_ = lean_nat_dec_lt(v_lo_3771_, v_hi_3772_);
if (v___x_3773_ == 0)
{
lean_dec(v_lo_3771_);
return v_as_3770_;
}
else
{
lean_object* v___f_3774_; lean_object* v___x_3775_; lean_object* v_fst_3776_; lean_object* v_snd_3777_; uint8_t v___x_3778_; 
v___f_3774_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___closed__0));
lean_inc(v_lo_3771_);
v___x_3775_ = l_Array_qpartition___redArg(v_as_3770_, v___f_3774_, v_lo_3771_, v_hi_3772_);
v_fst_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_fst_3776_);
v_snd_3777_ = lean_ctor_get(v___x_3775_, 1);
lean_inc(v_snd_3777_);
lean_dec_ref(v___x_3775_);
v___x_3778_ = lean_nat_dec_le(v_hi_3772_, v_fst_3776_);
if (v___x_3778_ == 0)
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3779_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg(v_snd_3777_, v_lo_3771_, v_fst_3776_);
v___x_3780_ = lean_unsigned_to_nat(1u);
v___x_3781_ = lean_nat_add(v_fst_3776_, v___x_3780_);
lean_dec(v_fst_3776_);
v_as_3770_ = v___x_3779_;
v_lo_3771_ = v___x_3781_;
goto _start;
}
else
{
lean_dec(v_fst_3776_);
lean_dec(v_lo_3771_);
return v_snd_3777_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg___boxed(lean_object* v_as_3783_, lean_object* v_lo_3784_, lean_object* v_hi_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg(v_as_3783_, v_lo_3784_, v_hi_3785_);
lean_dec(v_hi_3785_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts(lean_object* v_ctx_3789_, lean_object* v_indVal_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_){
_start:
{
lean_object* v_ctors_3798_; lean_object* v___x_3799_; lean_object* v_alts_3800_; lean_object* v___x_3801_; 
v_ctors_3798_ = lean_ctor_get(v_indVal_3790_, 4);
lean_inc(v_ctors_3798_);
v___x_3799_ = lean_unsigned_to_nat(0u);
v_alts_3800_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts___closed__0));
lean_inc(v_ctors_3798_);
v___x_3801_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg(v_indVal_3790_, v_ctx_3789_, v_ctors_3798_, v_ctors_3798_, v_alts_3800_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
lean_dec(v_ctors_3798_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3826_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3804_ = v___x_3801_;
v_isShared_3805_ = v_isSharedCheck_3826_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3801_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3826_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___y_3807_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___x_3818_; uint8_t v___x_3819_; 
v___x_3818_ = lean_array_get_size(v_a_3802_);
v___x_3819_ = lean_nat_dec_eq(v___x_3818_, v___x_3799_);
if (v___x_3819_ == 0)
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___y_3823_; uint8_t v___x_3825_; 
v___x_3820_ = lean_unsigned_to_nat(1u);
v___x_3821_ = lean_nat_sub(v___x_3818_, v___x_3820_);
v___x_3825_ = lean_nat_dec_le(v___x_3799_, v___x_3821_);
if (v___x_3825_ == 0)
{
lean_inc(v___x_3821_);
v___y_3823_ = v___x_3821_;
goto v___jp_3822_;
}
else
{
v___y_3823_ = v___x_3799_;
goto v___jp_3822_;
}
v___jp_3822_:
{
uint8_t v___x_3824_; 
v___x_3824_ = lean_nat_dec_le(v___y_3823_, v___x_3821_);
if (v___x_3824_ == 0)
{
lean_dec(v___x_3821_);
lean_inc(v___y_3823_);
v___y_3815_ = v___y_3823_;
v___y_3816_ = v___y_3823_;
goto v___jp_3814_;
}
else
{
v___y_3815_ = v___y_3823_;
v___y_3816_ = v___x_3821_;
goto v___jp_3814_;
}
}
}
else
{
v___y_3807_ = v_a_3802_;
goto v___jp_3806_;
}
v___jp_3806_:
{
size_t v_sz_3808_; size_t v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3812_; 
v_sz_3808_ = lean_array_size(v___y_3807_);
v___x_3809_ = ((size_t)0ULL);
v___x_3810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__7(v_sz_3808_, v___x_3809_, v___y_3807_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3810_);
v___x_3812_ = v___x_3804_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
v___jp_3814_:
{
lean_object* v___x_3817_; 
v___x_3817_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg(v_a_3802_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
v___y_3807_ = v___x_3817_;
goto v___jp_3806_;
}
}
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
v_a_3827_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3801_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3801_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts___boxed(lean_object* v_ctx_3835_, lean_object* v_indVal_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts(v_ctx_3835_, v_indVal_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1(lean_object* v_indVal_3845_, lean_object* v___x_3846_, lean_object* v_as_3847_, lean_object* v_i_3848_, lean_object* v_j_3849_, lean_object* v_inv_3850_, lean_object* v_bs_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___redArg(v_indVal_3845_, v___x_3846_, v_as_3847_, v_i_3848_, v_j_3849_, v_bs_3851_, v___y_3856_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1___boxed(lean_object* v_indVal_3860_, lean_object* v___x_3861_, lean_object* v_as_3862_, lean_object* v_i_3863_, lean_object* v_j_3864_, lean_object* v_inv_3865_, lean_object* v_bs_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__1(v_indVal_3860_, v___x_3861_, v_as_3862_, v_i_3863_, v_j_3864_, v_inv_3865_, v_bs_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec_ref(v_as_3862_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5(lean_object* v_upperBound_3875_, lean_object* v_indVal_3876_, lean_object* v_xs_3877_, lean_object* v_inst_3878_, lean_object* v_R_3879_, lean_object* v_a_3880_, lean_object* v_b_3881_, lean_object* v_c_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___redArg(v_upperBound_3875_, v_indVal_3876_, v_xs_3877_, v_a_3880_, v_b_3881_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5___boxed(lean_object* v_upperBound_3891_, lean_object* v_indVal_3892_, lean_object* v_xs_3893_, lean_object* v_inst_3894_, lean_object* v_R_3895_, lean_object* v_a_3896_, lean_object* v_b_3897_, lean_object* v_c_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__5(v_upperBound_3891_, v_indVal_3892_, v_xs_3893_, v_inst_3894_, v_R_3895_, v_a_3896_, v_b_3897_, v_c_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
lean_dec(v___y_3902_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec_ref(v_xs_3893_);
lean_dec_ref(v_indVal_3892_);
lean_dec(v_upperBound_3891_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6(lean_object* v_indVal_3907_, lean_object* v_ctx_3908_, lean_object* v_as_3909_, lean_object* v_as_x27_3910_, lean_object* v_b_3911_, lean_object* v_a_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg(v_indVal_3907_, v_ctx_3908_, v_as_3909_, v_as_x27_3910_, v_b_3911_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___boxed(lean_object* v_indVal_3921_, lean_object* v_ctx_3922_, lean_object* v_as_3923_, lean_object* v_as_x27_3924_, lean_object* v_b_3925_, lean_object* v_a_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6(v_indVal_3921_, v_ctx_3922_, v_as_3923_, v_as_x27_3924_, v_b_3925_, v_a_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v_as_3923_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8(lean_object* v_n_3935_, lean_object* v_as_3936_, lean_object* v_lo_3937_, lean_object* v_hi_3938_, lean_object* v_w_3939_, lean_object* v_hlo_3940_, lean_object* v_hhi_3941_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___redArg(v_as_3936_, v_lo_3937_, v_hi_3938_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8___boxed(lean_object* v_n_3943_, lean_object* v_as_3944_, lean_object* v_lo_3945_, lean_object* v_hi_3946_, lean_object* v_w_3947_, lean_object* v_hlo_3948_, lean_object* v_hhi_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__8(v_n_3943_, v_as_3944_, v_lo_3945_, v_hi_3946_, v_w_3947_, v_hlo_3948_, v_hhi_3949_);
lean_dec(v_hi_3946_);
lean_dec(v_n_3943_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6(lean_object* v_ctx_3951_, lean_object* v_indVal_3952_, lean_object* v_as_3953_, lean_object* v_as_x27_3954_, lean_object* v_b_3955_, lean_object* v_a_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___redArg(v_ctx_3951_, v_indVal_3952_, v_as_x27_3954_, v_b_3955_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6___boxed(lean_object* v_ctx_3965_, lean_object* v_indVal_3966_, lean_object* v_as_3967_, lean_object* v_as_x27_3968_, lean_object* v_b_3969_, lean_object* v_a_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6_spec__6(v_ctx_3965_, v_indVal_3966_, v_as_3967_, v_as_x27_3968_, v_b_3969_, v_a_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v_as_3967_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__1(lean_object* v___x_3979_, lean_object* v___x_3980_, lean_object* v___x_3981_, size_t v_sz_3982_, size_t v_i_3983_, lean_object* v_bs_3984_){
_start:
{
uint8_t v___x_3985_; 
v___x_3985_ = lean_usize_dec_lt(v_i_3983_, v_sz_3982_);
if (v___x_3985_ == 0)
{
lean_dec(v___x_3981_);
lean_dec(v___x_3980_);
lean_dec(v___x_3979_);
return v_bs_3984_;
}
else
{
lean_object* v_v_3986_; lean_object* v_fst_3987_; lean_object* v_snd_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v_bs_x27_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; size_t v___x_3996_; size_t v___x_3997_; lean_object* v___x_3998_; 
v_v_3986_ = lean_array_uget_borrowed(v_bs_3984_, v_i_3983_);
v_fst_3987_ = lean_ctor_get(v_v_3986_, 0);
lean_inc(v_fst_3987_);
v_snd_3988_ = lean_ctor_get(v_v_3986_, 1);
lean_inc(v_snd_3988_);
v___x_3989_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_3990_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4));
v___x_3991_ = lean_unsigned_to_nat(0u);
v_bs_x27_3992_ = lean_array_uset(v_bs_3984_, v_i_3983_, v___x_3991_);
lean_inc(v___x_3979_);
v___x_3993_ = l_Lean_Syntax_node1(v___x_3979_, v___x_3989_, v_fst_3987_);
lean_inc(v___x_3979_);
v___x_3994_ = l_Lean_Syntax_node1(v___x_3979_, v___x_3989_, v___x_3993_);
lean_inc(v___x_3981_);
lean_inc(v___x_3980_);
lean_inc(v___x_3979_);
v___x_3995_ = l_Lean_Syntax_node4(v___x_3979_, v___x_3990_, v___x_3980_, v___x_3994_, v___x_3981_, v_snd_3988_);
v___x_3996_ = ((size_t)1ULL);
v___x_3997_ = lean_usize_add(v_i_3983_, v___x_3996_);
v___x_3998_ = lean_array_uset(v_bs_x27_3992_, v_i_3983_, v___x_3995_);
v_i_3983_ = v___x_3997_;
v_bs_3984_ = v___x_3998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__1___boxed(lean_object* v___x_4000_, lean_object* v___x_4001_, lean_object* v___x_4002_, lean_object* v_sz_4003_, lean_object* v_i_4004_, lean_object* v_bs_4005_){
_start:
{
size_t v_sz_boxed_4006_; size_t v_i_boxed_4007_; lean_object* v_res_4008_; 
v_sz_boxed_4006_ = lean_unbox_usize(v_sz_4003_);
lean_dec(v_sz_4003_);
v_i_boxed_4007_ = lean_unbox_usize(v_i_4004_);
lean_dec(v_i_4004_);
v_res_4008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__1(v___x_4000_, v___x_4001_, v___x_4002_, v_sz_boxed_4006_, v_i_boxed_4007_, v_bs_4005_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__0(size_t v_sz_4009_, size_t v_i_4010_, lean_object* v_bs_4011_){
_start:
{
uint8_t v___x_4012_; 
v___x_4012_ = lean_usize_dec_lt(v_i_4010_, v_sz_4009_);
if (v___x_4012_ == 0)
{
return v_bs_4011_;
}
else
{
lean_object* v_v_4013_; lean_object* v___x_4014_; lean_object* v_bs_x27_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; size_t v___x_4018_; size_t v___x_4019_; lean_object* v___x_4020_; 
v_v_4013_ = lean_array_uget(v_bs_4011_, v_i_4010_);
v___x_4014_ = lean_unsigned_to_nat(0u);
v_bs_x27_4015_ = lean_array_uset(v_bs_4011_, v_i_4010_, v___x_4014_);
v___x_4016_ = lean_box(2);
v___x_4017_ = l_Lean_Syntax_mkStrLit(v_v_4013_, v___x_4016_);
v___x_4018_ = ((size_t)1ULL);
v___x_4019_ = lean_usize_add(v_i_4010_, v___x_4018_);
v___x_4020_ = lean_array_uset(v_bs_x27_4015_, v_i_4010_, v___x_4017_);
v_i_4010_ = v___x_4019_;
v_bs_4011_ = v___x_4020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__0___boxed(lean_object* v_sz_4022_, lean_object* v_i_4023_, lean_object* v_bs_4024_){
_start:
{
size_t v_sz_boxed_4025_; size_t v_i_boxed_4026_; lean_object* v_res_4027_; 
v_sz_boxed_4025_ = lean_unbox_usize(v_sz_4022_);
lean_dec(v_sz_4022_);
v_i_boxed_4026_ = lean_unbox_usize(v_i_4023_);
lean_dec(v_i_4023_);
v_res_4027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__0(v_sz_boxed_4025_, v_i_boxed_4026_, v_bs_4024_);
return v_res_4027_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__3(void){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__2));
v___x_4036_ = l_String_toRawSubstring_x27(v___x_4035_);
return v___x_4036_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__10(void){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__9));
v___x_4053_ = l_String_toRawSubstring_x27(v___x_4052_);
return v___x_4053_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__13(void){
_start:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__12));
v___x_4058_ = l_String_toRawSubstring_x27(v___x_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct(lean_object* v_ctx_4076_, lean_object* v_indName_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v___x_4085_; 
lean_inc_ref(v_a_4078_);
v___x_4085_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_spec__0(v_indName_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_object* v_a_4086_; lean_object* v___x_4087_; 
v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
lean_inc(v_a_4086_);
lean_dec_ref(v___x_4085_);
lean_inc_ref(v_a_4082_);
v___x_4087_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts(v_ctx_4076_, v_a_4086_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4201_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4090_ = v___x_4087_;
v_isShared_4091_ = v_isSharedCheck_4201_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4201_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4092_; lean_object* v_fst_4093_; lean_object* v_snd_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4200_; 
v___x_4092_ = l_Array_unzip___redArg(v_a_4088_);
lean_dec(v_a_4088_);
v_fst_4093_ = lean_ctor_get(v___x_4092_, 0);
v_snd_4094_ = lean_ctor_get(v___x_4092_, 1);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4096_ = v___x_4092_;
v_isShared_4097_ = v_isSharedCheck_4200_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_snd_4094_);
lean_inc(v_fst_4093_);
lean_dec(v___x_4092_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4200_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v_ref_4098_; lean_object* v_quotContext_4099_; lean_object* v_currMacroScope_4100_; uint8_t v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4106_; 
v_ref_4098_ = lean_ctor_get(v_a_4082_, 5);
lean_inc(v_ref_4098_);
v_quotContext_4099_ = lean_ctor_get(v_a_4082_, 10);
lean_inc(v_quotContext_4099_);
v_currMacroScope_4100_ = lean_ctor_get(v_a_4082_, 11);
lean_inc(v_currMacroScope_4100_);
lean_dec_ref(v_a_4082_);
v___x_4101_ = 0;
v___x_4102_ = l_Lean_SourceInfo_fromRef(v_ref_4098_, v___x_4101_);
lean_dec(v_ref_4098_);
v___x_4103_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__0));
v___x_4104_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__1));
lean_inc(v___x_4102_);
if (v_isShared_4097_ == 0)
{
lean_ctor_set_tag(v___x_4096_, 2);
lean_ctor_set(v___x_4096_, 1, v___x_4103_);
lean_ctor_set(v___x_4096_, 0, v___x_4102_);
v___x_4106_ = v___x_4096_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4102_);
lean_ctor_set(v_reuseFailAlloc_4199_, 1, v___x_4103_);
v___x_4106_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; size_t v_sz_4150_; size_t v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; size_t v_sz_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4197_; 
v___x_4107_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_4108_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_4102_);
v___x_4109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4102_);
lean_ctor_set(v___x_4109_, 1, v___x_4107_);
lean_ctor_set(v___x_4109_, 2, v___x_4108_);
v___x_4110_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__1));
v___x_4111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__31));
v___x_4112_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__3, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__3_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__3);
v___x_4113_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__5));
lean_inc(v_currMacroScope_4100_);
lean_inc(v_quotContext_4099_);
v___x_4114_ = l_Lean_addMacroScope(v_quotContext_4099_, v___x_4113_, v_currMacroScope_4100_);
v___x_4115_ = lean_box(0);
v___x_4116_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__8));
lean_inc(v___x_4102_);
v___x_4117_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4102_);
lean_ctor_set(v___x_4117_, 1, v___x_4112_);
lean_ctor_set(v___x_4117_, 2, v___x_4114_);
lean_ctor_set(v___x_4117_, 3, v___x_4116_);
v___x_4118_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__10);
v___x_4119_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__11));
lean_inc(v_currMacroScope_4100_);
lean_inc(v_quotContext_4099_);
v___x_4120_ = l_Lean_addMacroScope(v_quotContext_4099_, v___x_4119_, v_currMacroScope_4100_);
v___x_4121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__6));
lean_inc(v___x_4102_);
v___x_4122_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4102_);
lean_ctor_set(v___x_4122_, 1, v___x_4118_);
lean_ctor_set(v___x_4122_, 2, v___x_4120_);
lean_ctor_set(v___x_4122_, 3, v___x_4121_);
lean_inc(v___x_4102_);
v___x_4123_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4107_, v___x_4122_);
lean_inc(v___x_4102_);
v___x_4124_ = l_Lean_Syntax_node2(v___x_4102_, v___x_4111_, v___x_4117_, v___x_4123_);
lean_inc_ref(v___x_4109_);
lean_inc(v___x_4102_);
v___x_4125_ = l_Lean_Syntax_node2(v___x_4102_, v___x_4110_, v___x_4109_, v___x_4124_);
lean_inc(v___x_4102_);
v___x_4126_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4107_, v___x_4125_);
v___x_4127_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__2));
lean_inc(v___x_4102_);
v___x_4128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4102_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
v___x_4129_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct___closed__4));
v___x_4130_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__4));
v___x_4131_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__5));
lean_inc(v___x_4102_);
v___x_4132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4102_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__26);
v___x_4134_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__27));
lean_inc(v_currMacroScope_4100_);
lean_inc(v_quotContext_4099_);
v___x_4135_ = l_Lean_addMacroScope(v_quotContext_4099_, v___x_4134_, v_currMacroScope_4100_);
v___x_4136_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__30));
lean_inc(v___x_4102_);
v___x_4137_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4102_);
lean_ctor_set(v___x_4137_, 1, v___x_4133_);
lean_ctor_set(v___x_4137_, 2, v___x_4135_);
lean_ctor_set(v___x_4137_, 3, v___x_4136_);
v___x_4138_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__10, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__10_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__10);
v___x_4139_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__11));
lean_inc(v_currMacroScope_4100_);
lean_inc(v_quotContext_4099_);
v___x_4140_ = l_Lean_addMacroScope(v_quotContext_4099_, v___x_4139_, v_currMacroScope_4100_);
lean_inc(v___x_4102_);
v___x_4141_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4102_);
lean_ctor_set(v___x_4141_, 1, v___x_4138_);
lean_ctor_set(v___x_4141_, 2, v___x_4140_);
lean_ctor_set(v___x_4141_, 3, v___x_4115_);
lean_inc_ref(v___x_4141_);
lean_inc(v___x_4102_);
v___x_4142_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4107_, v___x_4141_);
lean_inc(v___x_4102_);
v___x_4143_ = l_Lean_Syntax_node2(v___x_4102_, v___x_4111_, v___x_4137_, v___x_4142_);
lean_inc(v___x_4102_);
v___x_4144_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4107_, v___x_4143_);
lean_inc(v___x_4102_);
v___x_4145_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4107_, v___x_4144_);
v___x_4146_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___lam__0___closed__7));
lean_inc(v___x_4102_);
v___x_4147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4102_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
lean_inc_ref(v___x_4109_);
lean_inc(v___x_4102_);
v___x_4148_ = l_Lean_Syntax_node2(v___x_4102_, v___x_4110_, v___x_4109_, v___x_4141_);
lean_inc(v___x_4102_);
v___x_4149_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4107_, v___x_4148_);
v_sz_4150_ = lean_array_size(v_fst_4093_);
v___x_4151_ = ((size_t)0ULL);
v___x_4152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__0(v_sz_4150_, v___x_4151_, v_fst_4093_);
v___x_4153_ = l_Array_zip___redArg(v___x_4152_, v_snd_4094_);
lean_dec(v_snd_4094_);
lean_dec_ref(v___x_4152_);
v_sz_4154_ = lean_array_size(v___x_4153_);
lean_inc_ref(v___x_4147_);
lean_inc_ref(v___x_4132_);
lean_inc(v___x_4102_);
v___x_4155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_spec__1(v___x_4102_, v___x_4132_, v___x_4147_, v_sz_4154_, v___x_4151_, v___x_4153_);
v___x_4156_ = l_Array_append___redArg(v___x_4108_, v___x_4155_);
lean_dec_ref(v___x_4155_);
v___x_4157_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__1));
v___x_4158_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__3___redArg___closed__2));
lean_inc(v___x_4102_);
v___x_4159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4102_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
lean_inc(v___x_4102_);
v___x_4160_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4157_, v___x_4159_);
lean_inc(v___x_4102_);
v___x_4161_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4107_, v___x_4160_);
lean_inc(v___x_4102_);
v___x_4162_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4107_, v___x_4161_);
v___x_4163_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__13, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__13_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__13);
v___x_4164_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__15));
lean_inc(v_currMacroScope_4100_);
lean_inc(v_quotContext_4099_);
v___x_4165_ = l_Lean_addMacroScope(v_quotContext_4099_, v___x_4164_, v_currMacroScope_4100_);
v___x_4166_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__19));
lean_inc(v___x_4102_);
v___x_4167_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4102_);
lean_ctor_set(v___x_4167_, 1, v___x_4163_);
lean_ctor_set(v___x_4167_, 2, v___x_4165_);
lean_ctor_set(v___x_4167_, 3, v___x_4166_);
v___x_4168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__34));
v___x_4169_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__20));
lean_inc(v___x_4102_);
v___x_4170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4102_);
lean_ctor_set(v___x_4170_, 1, v___x_4169_);
lean_inc(v___x_4102_);
v___x_4171_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4168_, v___x_4170_);
lean_inc(v___x_4102_);
v___x_4172_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4107_, v___x_4171_);
lean_inc_ref(v___x_4167_);
lean_inc(v___x_4102_);
v___x_4173_ = l_Lean_Syntax_node2(v___x_4102_, v___x_4111_, v___x_4167_, v___x_4172_);
lean_inc_ref(v___x_4147_);
lean_inc_ref(v___x_4132_);
lean_inc(v___x_4102_);
v___x_4174_ = l_Lean_Syntax_node4(v___x_4102_, v___x_4130_, v___x_4132_, v___x_4162_, v___x_4147_, v___x_4173_);
v___x_4175_ = lean_array_push(v___x_4156_, v___x_4174_);
lean_inc(v___x_4102_);
v___x_4176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4102_);
lean_ctor_set(v___x_4176_, 1, v___x_4107_);
lean_ctor_set(v___x_4176_, 2, v___x_4175_);
lean_inc(v___x_4102_);
v___x_4177_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4129_, v___x_4176_);
lean_inc_ref(v___x_4128_);
lean_inc_ref_n(v___x_4109_, 2);
lean_inc_ref(v___x_4106_);
lean_inc(v___x_4102_);
v___x_4178_ = l_Lean_Syntax_node6(v___x_4102_, v___x_4104_, v___x_4106_, v___x_4109_, v___x_4109_, v___x_4149_, v___x_4128_, v___x_4177_);
lean_inc_ref(v___x_4147_);
lean_inc_ref(v___x_4132_);
lean_inc(v___x_4102_);
v___x_4179_ = l_Lean_Syntax_node4(v___x_4102_, v___x_4130_, v___x_4132_, v___x_4145_, v___x_4147_, v___x_4178_);
v___x_4180_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__19);
v___x_4181_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__20));
v___x_4182_ = l_Lean_addMacroScope(v_quotContext_4099_, v___x_4181_, v_currMacroScope_4100_);
v___x_4183_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct_mkAlts_spec__6___redArg___lam__0___closed__24));
lean_inc(v___x_4102_);
v___x_4184_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4102_);
lean_ctor_set(v___x_4184_, 1, v___x_4180_);
lean_ctor_set(v___x_4184_, 2, v___x_4182_);
lean_ctor_set(v___x_4184_, 3, v___x_4183_);
lean_inc(v___x_4102_);
v___x_4185_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4107_, v___x_4184_);
lean_inc(v___x_4102_);
v___x_4186_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4107_, v___x_4185_);
v___x_4187_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___closed__21));
lean_inc(v___x_4102_);
v___x_4188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4102_);
lean_ctor_set(v___x_4188_, 1, v___x_4187_);
lean_inc(v___x_4102_);
v___x_4189_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4168_, v___x_4188_);
lean_inc(v___x_4102_);
v___x_4190_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4107_, v___x_4189_);
lean_inc(v___x_4102_);
v___x_4191_ = l_Lean_Syntax_node2(v___x_4102_, v___x_4111_, v___x_4167_, v___x_4190_);
lean_inc(v___x_4102_);
v___x_4192_ = l_Lean_Syntax_node4(v___x_4102_, v___x_4130_, v___x_4132_, v___x_4186_, v___x_4147_, v___x_4191_);
lean_inc(v___x_4102_);
v___x_4193_ = l_Lean_Syntax_node2(v___x_4102_, v___x_4107_, v___x_4179_, v___x_4192_);
lean_inc(v___x_4102_);
v___x_4194_ = l_Lean_Syntax_node1(v___x_4102_, v___x_4129_, v___x_4193_);
lean_inc_ref(v___x_4109_);
v___x_4195_ = l_Lean_Syntax_node6(v___x_4102_, v___x_4104_, v___x_4106_, v___x_4109_, v___x_4109_, v___x_4126_, v___x_4128_, v___x_4194_);
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v___x_4195_);
v___x_4197_ = v___x_4090_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_dec_ref(v_a_4082_);
v_a_4202_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4087_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4087_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
else
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
lean_dec(v_a_4083_);
lean_dec_ref(v_a_4082_);
lean_dec(v_a_4081_);
lean_dec_ref(v_a_4080_);
lean_dec(v_a_4079_);
lean_dec_ref(v_a_4078_);
lean_dec_ref(v_ctx_4076_);
v_a_4210_ = lean_ctor_get(v___x_4085_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4212_ = v___x_4085_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4085_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct___boxed(lean_object* v_ctx_4218_, lean_object* v_indName_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct(v_ctx_4218_, v_indName_4219_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_, v_a_4224_, v_a_4225_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBody(lean_object* v_ctx_4228_, lean_object* v_header_4229_, lean_object* v_e_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_){
_start:
{
lean_object* v___x_4238_; lean_object* v_env_4239_; lean_object* v___x_4240_; lean_object* v_indName_4241_; uint8_t v___x_4242_; 
v___x_4238_ = lean_st_ref_get(v_a_4236_);
v_env_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc_ref(v_env_4239_);
lean_dec(v___x_4238_);
v___x_4240_ = l_Lean_Expr_getAppFn(v_e_4230_);
v_indName_4241_ = l_Lean_Expr_constName_x21(v___x_4240_);
lean_dec_ref(v___x_4240_);
lean_inc(v_indName_4241_);
v___x_4242_ = l_Lean_isStructure(v_env_4239_, v_indName_4241_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct(v_ctx_4228_, v_header_4229_, v_indName_4241_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_);
return v___x_4243_;
}
else
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct(v_header_4229_, v_indName_4241_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_);
lean_dec(v_a_4236_);
lean_dec(v_a_4234_);
lean_dec_ref(v_a_4233_);
lean_dec(v_a_4232_);
lean_dec_ref(v_a_4231_);
lean_dec_ref(v_header_4229_);
return v___x_4244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonBody___boxed(lean_object* v_ctx_4245_, lean_object* v_header_4246_, lean_object* v_e_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBody(v_ctx_4245_, v_header_4246_, v_e_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_);
lean_dec_ref(v_e_4247_);
lean_dec_ref(v_ctx_4245_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0(lean_object* v_targetType_4267_, lean_object* v_ctx_4268_, lean_object* v_a_4269_, uint8_t v_usePartial_4270_, lean_object* v___x_4271_, lean_object* v___x_4272_, lean_object* v_auxFunName_4273_, lean_object* v_binders_4274_, lean_object* v___x_4275_, lean_object* v_argNames_4276_, lean_object* v_x_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
lean_object* v___x_4285_; uint8_t v___x_4286_; lean_object* v___x_4287_; 
v___x_4285_ = lean_box(0);
v___x_4286_ = 1;
lean_inc(v___y_4283_);
lean_inc_ref(v___y_4282_);
lean_inc(v___y_4281_);
lean_inc_ref(v___y_4280_);
lean_inc(v___y_4279_);
lean_inc_ref(v___y_4278_);
v___x_4287_ = l_Lean_Elab_Term_elabTerm(v_targetType_4267_, v___x_4285_, v___x_4286_, v___x_4286_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4289_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref(v___x_4287_);
lean_inc(v___y_4283_);
lean_inc_ref(v___y_4282_);
lean_inc(v___y_4281_);
lean_inc_ref(v___y_4280_);
lean_inc(v___y_4279_);
lean_inc_ref(v___y_4278_);
v___x_4289_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonBody(v_ctx_4268_, v_a_4269_, v_a_4288_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_);
lean_dec(v_a_4288_);
if (lean_obj_tag(v___x_4289_) == 0)
{
if (v_usePartial_4270_ == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4351_; 
lean_dec(v___y_4283_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec_ref(v_argNames_4276_);
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4292_ = v___x_4289_;
v_isShared_4293_ = v_isSharedCheck_4351_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4289_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4351_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v_ref_4294_; lean_object* v_quotContext_4295_; lean_object* v_currMacroScope_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4349_; 
v_ref_4294_ = lean_ctor_get(v___y_4282_, 5);
lean_inc(v_ref_4294_);
v_quotContext_4295_ = lean_ctor_get(v___y_4282_, 10);
lean_inc(v_quotContext_4295_);
v_currMacroScope_4296_ = lean_ctor_get(v___y_4282_, 11);
lean_inc(v_currMacroScope_4296_);
lean_dec_ref(v___y_4282_);
v___x_4297_ = l_Lean_SourceInfo_fromRef(v_ref_4294_, v_usePartial_4270_);
lean_dec(v_ref_4294_);
v___x_4298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21));
v___x_4299_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__0));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4300_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4298_, v___x_4299_);
v___x_4301_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__1));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4302_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4298_, v___x_4301_);
v___x_4303_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_4304_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_4297_);
v___x_4305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4297_);
lean_ctor_set(v___x_4305_, 1, v___x_4303_);
lean_ctor_set(v___x_4305_, 2, v___x_4304_);
lean_inc_ref_n(v___x_4305_, 7);
lean_inc(v___x_4297_);
v___x_4306_ = l_Lean_Syntax_node7(v___x_4297_, v___x_4302_, v___x_4305_, v___x_4305_, v___x_4305_, v___x_4305_, v___x_4305_, v___x_4305_, v___x_4305_);
v___x_4307_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__2));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4308_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4298_, v___x_4307_);
v___x_4309_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__3));
lean_inc(v___x_4297_);
v___x_4310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4297_);
lean_ctor_set(v___x_4310_, 1, v___x_4309_);
v___x_4311_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__4));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4312_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4298_, v___x_4311_);
v___x_4313_ = lean_mk_syntax_ident(v_auxFunName_4273_);
lean_inc_ref(v___x_4305_);
lean_inc(v___x_4297_);
v___x_4314_ = l_Lean_Syntax_node2(v___x_4297_, v___x_4312_, v___x_4313_, v___x_4305_);
v___x_4315_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__5));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4316_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4298_, v___x_4315_);
v___x_4317_ = l_Array_append___redArg(v___x_4304_, v_binders_4274_);
lean_inc(v___x_4297_);
v___x_4318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4297_);
lean_ctor_set(v___x_4318_, 1, v___x_4303_);
lean_ctor_set(v___x_4318_, 2, v___x_4317_);
v___x_4319_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__6));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4320_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4275_, v___x_4319_);
v___x_4321_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__16));
lean_inc(v___x_4297_);
v___x_4322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4297_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
v___x_4323_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12));
v___x_4324_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17);
v___x_4325_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__18));
v___x_4326_ = l_Lean_addMacroScope(v_quotContext_4295_, v___x_4325_, v_currMacroScope_4296_);
lean_inc_ref(v___x_4271_);
v___x_4327_ = l_Lean_Name_mkStr2(v___x_4271_, v___x_4323_);
v___x_4328_ = lean_box(0);
lean_inc(v___x_4327_);
v___x_4329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4327_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
v___x_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4327_);
v___x_4331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4330_);
lean_ctor_set(v___x_4331_, 1, v___x_4328_);
v___x_4332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4329_);
lean_ctor_set(v___x_4332_, 1, v___x_4331_);
lean_inc(v___x_4297_);
v___x_4333_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4297_);
lean_ctor_set(v___x_4333_, 1, v___x_4324_);
lean_ctor_set(v___x_4333_, 2, v___x_4326_);
lean_ctor_set(v___x_4333_, 3, v___x_4332_);
lean_inc(v___x_4297_);
v___x_4334_ = l_Lean_Syntax_node2(v___x_4297_, v___x_4320_, v___x_4322_, v___x_4333_);
lean_inc(v___x_4297_);
v___x_4335_ = l_Lean_Syntax_node1(v___x_4297_, v___x_4303_, v___x_4334_);
lean_inc(v___x_4297_);
v___x_4336_ = l_Lean_Syntax_node2(v___x_4297_, v___x_4316_, v___x_4318_, v___x_4335_);
v___x_4337_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__7));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4338_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4298_, v___x_4337_);
v___x_4339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6));
lean_inc(v___x_4297_);
v___x_4340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4297_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__8));
v___x_4342_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__9));
v___x_4343_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4341_, v___x_4342_);
lean_inc_ref_n(v___x_4305_, 2);
lean_inc(v___x_4297_);
v___x_4344_ = l_Lean_Syntax_node2(v___x_4297_, v___x_4343_, v___x_4305_, v___x_4305_);
lean_inc_ref(v___x_4305_);
lean_inc(v___x_4297_);
v___x_4345_ = l_Lean_Syntax_node4(v___x_4297_, v___x_4338_, v___x_4340_, v_a_4290_, v___x_4344_, v___x_4305_);
lean_inc(v___x_4297_);
v___x_4346_ = l_Lean_Syntax_node5(v___x_4297_, v___x_4308_, v___x_4310_, v___x_4314_, v___x_4336_, v___x_4345_, v___x_4305_);
v___x_4347_ = l_Lean_Syntax_node2(v___x_4297_, v___x_4300_, v___x_4306_, v___x_4346_);
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v___x_4347_);
v___x_4349_ = v___x_4292_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v_a_4352_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4352_);
lean_dec_ref(v___x_4289_);
v___x_4353_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__1));
lean_inc_ref(v___x_4271_);
v___x_4354_ = l_Lean_Name_mkStr2(v___x_4271_, v___x_4353_);
lean_inc(v___y_4283_);
lean_inc_ref(v___y_4282_);
lean_inc(v___y_4281_);
lean_inc_ref(v___y_4280_);
lean_inc(v___y_4279_);
lean_inc_ref(v___y_4278_);
v___x_4355_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_4268_, v___x_4354_, v_argNames_4276_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4357_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref(v___x_4355_);
v___x_4357_ = l_Lean_Elab_Deriving_mkLet(v_a_4356_, v_a_4352_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_);
lean_dec(v___y_4283_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v_a_4356_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4425_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4360_ = v___x_4357_;
v_isShared_4361_ = v_isSharedCheck_4425_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4357_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4425_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v_ref_4362_; lean_object* v_quotContext_4363_; lean_object* v_currMacroScope_4364_; uint8_t v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4423_; 
v_ref_4362_ = lean_ctor_get(v___y_4282_, 5);
lean_inc(v_ref_4362_);
v_quotContext_4363_ = lean_ctor_get(v___y_4282_, 10);
lean_inc(v_quotContext_4363_);
v_currMacroScope_4364_ = lean_ctor_get(v___y_4282_, 11);
lean_inc(v_currMacroScope_4364_);
lean_dec_ref(v___y_4282_);
v___x_4365_ = 0;
v___x_4366_ = l_Lean_SourceInfo_fromRef(v_ref_4362_, v___x_4365_);
lean_dec(v_ref_4362_);
v___x_4367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21));
v___x_4368_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__0));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4369_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4367_, v___x_4368_);
v___x_4370_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__1));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4371_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4367_, v___x_4370_);
v___x_4372_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_4373_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_4366_);
v___x_4374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4366_);
lean_ctor_set(v___x_4374_, 1, v___x_4372_);
lean_ctor_set(v___x_4374_, 2, v___x_4373_);
v___x_4375_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__10));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4376_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4367_, v___x_4375_);
lean_inc(v___x_4366_);
v___x_4377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4366_);
lean_ctor_set(v___x_4377_, 1, v___x_4375_);
lean_inc(v___x_4366_);
v___x_4378_ = l_Lean_Syntax_node1(v___x_4366_, v___x_4376_, v___x_4377_);
lean_inc(v___x_4366_);
v___x_4379_ = l_Lean_Syntax_node1(v___x_4366_, v___x_4372_, v___x_4378_);
lean_inc_ref_n(v___x_4374_, 6);
lean_inc(v___x_4366_);
v___x_4380_ = l_Lean_Syntax_node7(v___x_4366_, v___x_4371_, v___x_4374_, v___x_4374_, v___x_4374_, v___x_4374_, v___x_4374_, v___x_4374_, v___x_4379_);
v___x_4381_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__2));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4382_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4367_, v___x_4381_);
v___x_4383_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__3));
lean_inc(v___x_4366_);
v___x_4384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4366_);
lean_ctor_set(v___x_4384_, 1, v___x_4383_);
v___x_4385_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__4));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4386_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4367_, v___x_4385_);
v___x_4387_ = lean_mk_syntax_ident(v_auxFunName_4273_);
lean_inc_ref(v___x_4374_);
lean_inc(v___x_4366_);
v___x_4388_ = l_Lean_Syntax_node2(v___x_4366_, v___x_4386_, v___x_4387_, v___x_4374_);
v___x_4389_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__5));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4390_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4367_, v___x_4389_);
v___x_4391_ = l_Array_append___redArg(v___x_4373_, v_binders_4274_);
lean_inc(v___x_4366_);
v___x_4392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4366_);
lean_ctor_set(v___x_4392_, 1, v___x_4372_);
lean_ctor_set(v___x_4392_, 2, v___x_4391_);
v___x_4393_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__6));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4394_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4275_, v___x_4393_);
v___x_4395_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__16));
lean_inc(v___x_4366_);
v___x_4396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4366_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
v___x_4397_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__12));
v___x_4398_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__17);
v___x_4399_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__18));
v___x_4400_ = l_Lean_addMacroScope(v_quotContext_4363_, v___x_4399_, v_currMacroScope_4364_);
lean_inc_ref(v___x_4271_);
v___x_4401_ = l_Lean_Name_mkStr2(v___x_4271_, v___x_4397_);
v___x_4402_ = lean_box(0);
lean_inc(v___x_4401_);
v___x_4403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4401_);
lean_ctor_set(v___x_4403_, 1, v___x_4402_);
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4401_);
v___x_4405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4404_);
lean_ctor_set(v___x_4405_, 1, v___x_4402_);
v___x_4406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4403_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
lean_inc(v___x_4366_);
v___x_4407_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4366_);
lean_ctor_set(v___x_4407_, 1, v___x_4398_);
lean_ctor_set(v___x_4407_, 2, v___x_4400_);
lean_ctor_set(v___x_4407_, 3, v___x_4406_);
lean_inc(v___x_4366_);
v___x_4408_ = l_Lean_Syntax_node2(v___x_4366_, v___x_4394_, v___x_4396_, v___x_4407_);
lean_inc(v___x_4366_);
v___x_4409_ = l_Lean_Syntax_node1(v___x_4366_, v___x_4372_, v___x_4408_);
lean_inc(v___x_4366_);
v___x_4410_ = l_Lean_Syntax_node2(v___x_4366_, v___x_4390_, v___x_4392_, v___x_4409_);
v___x_4411_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__7));
lean_inc_ref(v___x_4272_);
lean_inc_ref(v___x_4271_);
v___x_4412_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4367_, v___x_4411_);
v___x_4413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6));
lean_inc(v___x_4366_);
v___x_4414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4366_);
lean_ctor_set(v___x_4414_, 1, v___x_4413_);
v___x_4415_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__8));
v___x_4416_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__9));
v___x_4417_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___x_4415_, v___x_4416_);
lean_inc_ref_n(v___x_4374_, 2);
lean_inc(v___x_4366_);
v___x_4418_ = l_Lean_Syntax_node2(v___x_4366_, v___x_4417_, v___x_4374_, v___x_4374_);
lean_inc_ref(v___x_4374_);
lean_inc(v___x_4366_);
v___x_4419_ = l_Lean_Syntax_node4(v___x_4366_, v___x_4412_, v___x_4414_, v_a_4358_, v___x_4418_, v___x_4374_);
lean_inc(v___x_4366_);
v___x_4420_ = l_Lean_Syntax_node5(v___x_4366_, v___x_4382_, v___x_4384_, v___x_4388_, v___x_4410_, v___x_4419_, v___x_4374_);
v___x_4421_ = l_Lean_Syntax_node2(v___x_4366_, v___x_4369_, v___x_4380_, v___x_4420_);
if (v_isShared_4361_ == 0)
{
lean_ctor_set(v___x_4360_, 0, v___x_4421_);
v___x_4423_ = v___x_4360_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4421_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
else
{
lean_dec_ref(v___y_4282_);
lean_dec_ref(v___x_4275_);
lean_dec(v_auxFunName_4273_);
lean_dec_ref(v___x_4272_);
lean_dec_ref(v___x_4271_);
return v___x_4357_;
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
lean_dec(v_a_4352_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec_ref(v___x_4275_);
lean_dec(v_auxFunName_4273_);
lean_dec_ref(v___x_4272_);
lean_dec_ref(v___x_4271_);
v_a_4426_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4355_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4355_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
}
else
{
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec_ref(v_argNames_4276_);
lean_dec_ref(v___x_4275_);
lean_dec(v_auxFunName_4273_);
lean_dec_ref(v___x_4272_);
lean_dec_ref(v___x_4271_);
return v___x_4289_;
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec_ref(v_argNames_4276_);
lean_dec_ref(v___x_4275_);
lean_dec(v_auxFunName_4273_);
lean_dec_ref(v___x_4272_);
lean_dec_ref(v___x_4271_);
lean_dec_ref(v_a_4269_);
v_a_4434_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4287_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4287_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___boxed(lean_object** _args){
lean_object* v_targetType_4442_ = _args[0];
lean_object* v_ctx_4443_ = _args[1];
lean_object* v_a_4444_ = _args[2];
lean_object* v_usePartial_4445_ = _args[3];
lean_object* v___x_4446_ = _args[4];
lean_object* v___x_4447_ = _args[5];
lean_object* v_auxFunName_4448_ = _args[6];
lean_object* v_binders_4449_ = _args[7];
lean_object* v___x_4450_ = _args[8];
lean_object* v_argNames_4451_ = _args[9];
lean_object* v_x_4452_ = _args[10];
lean_object* v___y_4453_ = _args[11];
lean_object* v___y_4454_ = _args[12];
lean_object* v___y_4455_ = _args[13];
lean_object* v___y_4456_ = _args[14];
lean_object* v___y_4457_ = _args[15];
lean_object* v___y_4458_ = _args[16];
lean_object* v___y_4459_ = _args[17];
_start:
{
uint8_t v_usePartial_boxed_4460_; lean_object* v_res_4461_; 
v_usePartial_boxed_4460_ = lean_unbox(v_usePartial_4445_);
v_res_4461_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0(v_targetType_4442_, v_ctx_4443_, v_a_4444_, v_usePartial_boxed_4460_, v___x_4446_, v___x_4447_, v_auxFunName_4448_, v_binders_4449_, v___x_4450_, v_argNames_4451_, v_x_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
lean_dec_ref(v_x_4452_);
lean_dec_ref(v_binders_4449_);
lean_dec_ref(v_ctx_4443_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction(lean_object* v_ctx_4462_, lean_object* v_i_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v_typeInfos_4471_; lean_object* v_auxFunNames_4472_; uint8_t v_usePartial_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v_typeInfos_4471_ = lean_ctor_get(v_ctx_4462_, 1);
v_auxFunNames_4472_ = lean_ctor_get(v_ctx_4462_, 2);
v_usePartial_4473_ = lean_ctor_get_uint8(v_ctx_4462_, sizeof(void*)*3);
v___x_4474_ = l_Lean_instInhabitedInductiveVal_default;
v___x_4475_ = lean_array_get_borrowed(v___x_4474_, v_typeInfos_4471_, v_i_4463_);
lean_inc(v_a_4469_);
lean_inc_ref(v_a_4468_);
lean_inc(v_a_4467_);
lean_inc_ref(v_a_4466_);
lean_inc(v_a_4465_);
lean_inc_ref(v_a_4464_);
lean_inc(v___x_4475_);
v___x_4476_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader(v___x_4475_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v_binders_4478_; lean_object* v_argNames_4479_; lean_object* v_targetType_4480_; lean_object* v___x_4481_; lean_object* v_auxFunName_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___f_4487_; lean_object* v___x_4488_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref(v___x_4476_);
v_binders_4478_ = lean_ctor_get(v_a_4477_, 0);
lean_inc_ref(v_binders_4478_);
v_argNames_4479_ = lean_ctor_get(v_a_4477_, 1);
lean_inc_ref(v_argNames_4479_);
v_targetType_4480_ = lean_ctor_get(v_a_4477_, 3);
lean_inc(v_targetType_4480_);
v___x_4481_ = lean_box(0);
v_auxFunName_4482_ = lean_array_get(v___x_4481_, v_auxFunNames_4472_, v_i_4463_);
v___x_4483_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0));
v___x_4484_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2));
v___x_4485_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3));
v___x_4486_ = lean_box(v_usePartial_4473_);
lean_inc_ref(v_binders_4478_);
v___f_4487_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___boxed), 18, 10);
lean_closure_set(v___f_4487_, 0, v_targetType_4480_);
lean_closure_set(v___f_4487_, 1, v_ctx_4462_);
lean_closure_set(v___f_4487_, 2, v_a_4477_);
lean_closure_set(v___f_4487_, 3, v___x_4486_);
lean_closure_set(v___f_4487_, 4, v___x_4483_);
lean_closure_set(v___f_4487_, 5, v___x_4484_);
lean_closure_set(v___f_4487_, 6, v_auxFunName_4482_);
lean_closure_set(v___f_4487_, 7, v_binders_4478_);
lean_closure_set(v___f_4487_, 8, v___x_4485_);
lean_closure_set(v___f_4487_, 9, v_argNames_4479_);
v___x_4488_ = l_Lean_Elab_Term_elabBinders___redArg(v_binders_4478_, v___f_4487_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
return v___x_4488_;
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
lean_dec(v_a_4465_);
lean_dec_ref(v_a_4464_);
lean_dec_ref(v_ctx_4462_);
v_a_4489_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4476_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4476_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___boxed(lean_object* v_ctx_4497_, lean_object* v_i_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction(v_ctx_4497_, v_i_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
lean_dec(v_i_4498_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBody(lean_object* v_ctx_4507_, lean_object* v_e_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_){
_start:
{
lean_object* v___x_4516_; lean_object* v_env_4517_; lean_object* v___x_4518_; lean_object* v_indName_4519_; uint8_t v___x_4520_; 
v___x_4516_ = lean_st_ref_get(v_a_4514_);
v_env_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc_ref(v_env_4517_);
lean_dec(v___x_4516_);
v___x_4518_ = l_Lean_Expr_getAppFn(v_e_4508_);
v_indName_4519_ = l_Lean_Expr_constName_x21(v___x_4518_);
lean_dec_ref(v___x_4518_);
lean_inc(v_indName_4519_);
v___x_4520_ = l_Lean_isStructure(v_env_4517_, v_indName_4519_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; 
v___x_4521_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForInduct(v_ctx_4507_, v_indName_4519_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_);
return v___x_4521_;
}
else
{
lean_object* v___x_4522_; 
lean_dec_ref(v_ctx_4507_);
v___x_4522_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct(v_indName_4519_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_);
lean_dec(v_a_4514_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
return v___x_4522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonBody___boxed(lean_object* v_ctx_4523_, lean_object* v_e_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonBody(v_ctx_4523_, v_e_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
lean_dec_ref(v_e_4524_);
return v_res_4532_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__0___redArg___closed__11));
v___x_4534_ = l_String_toRawSubstring_x27(v___x_4533_);
return v___x_4534_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4549_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__6));
v___x_4550_ = l_String_toRawSubstring_x27(v___x_4549_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0(lean_object* v_targetType_4564_, lean_object* v_ctx_4565_, lean_object* v___x_4566_, lean_object* v_argNames_4567_, lean_object* v_indval_4568_, lean_object* v___x_4569_, lean_object* v_auxFunName_4570_, lean_object* v_binders_4571_, lean_object* v___x_4572_, uint8_t v_usePartial_4573_, lean_object* v_x_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v___x_4582_; uint8_t v___x_4583_; lean_object* v___x_4584_; 
v___x_4582_ = lean_box(0);
v___x_4583_ = 1;
lean_inc(v___y_4580_);
lean_inc_ref(v___y_4579_);
lean_inc(v___y_4578_);
lean_inc_ref(v___y_4577_);
lean_inc(v___y_4576_);
lean_inc_ref(v___y_4575_);
v___x_4584_ = l_Lean_Elab_Term_elabTerm(v_targetType_4564_, v___x_4582_, v___x_4583_, v___x_4583_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_object* v_a_4585_; lean_object* v___x_4586_; 
v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
lean_inc(v_a_4585_);
lean_dec_ref(v___x_4584_);
lean_inc(v___y_4580_);
lean_inc_ref(v___y_4579_);
lean_inc(v___y_4578_);
lean_inc_ref(v___y_4577_);
lean_inc(v___y_4576_);
lean_inc_ref(v___y_4575_);
lean_inc_ref(v_ctx_4565_);
v___x_4586_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonBody(v_ctx_4565_, v_a_4585_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
lean_dec(v_a_4585_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4587_);
lean_dec_ref(v___x_4586_);
if (v_usePartial_4573_ == 0)
{
uint8_t v_isRec_4675_; 
v_isRec_4675_ = lean_ctor_get_uint8(v_indval_4568_, sizeof(void*)*6);
if (v_isRec_4675_ == 0)
{
lean_object* v___x_4676_; 
lean_dec(v___y_4580_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec_ref(v_ctx_4565_);
v___x_4676_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indval_4568_, v_argNames_4567_, v___y_4579_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4741_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4679_ = v___x_4676_;
v_isShared_4680_ = v_isSharedCheck_4741_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4676_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4741_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v_ref_4681_; lean_object* v_quotContext_4682_; lean_object* v_currMacroScope_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4739_; 
v_ref_4681_ = lean_ctor_get(v___y_4579_, 5);
lean_inc(v_ref_4681_);
v_quotContext_4682_ = lean_ctor_get(v___y_4579_, 10);
lean_inc(v_quotContext_4682_);
v_currMacroScope_4683_ = lean_ctor_get(v___y_4579_, 11);
lean_inc(v_currMacroScope_4683_);
lean_dec_ref(v___y_4579_);
v___x_4684_ = l_Lean_SourceInfo_fromRef(v_ref_4681_, v_isRec_4675_);
lean_dec(v_ref_4681_);
v___x_4685_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21));
v___x_4686_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__0));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4687_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4685_, v___x_4686_);
v___x_4688_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__1));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4689_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4685_, v___x_4688_);
v___x_4690_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_4691_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_4684_);
v___x_4692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4684_);
lean_ctor_set(v___x_4692_, 1, v___x_4690_);
lean_ctor_set(v___x_4692_, 2, v___x_4691_);
lean_inc_ref_n(v___x_4692_, 7);
lean_inc(v___x_4684_);
v___x_4693_ = l_Lean_Syntax_node7(v___x_4684_, v___x_4689_, v___x_4692_, v___x_4692_, v___x_4692_, v___x_4692_, v___x_4692_, v___x_4692_, v___x_4692_);
v___x_4694_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__2));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4695_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4685_, v___x_4694_);
v___x_4696_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__3));
lean_inc(v___x_4684_);
v___x_4697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4697_, 0, v___x_4684_);
lean_ctor_set(v___x_4697_, 1, v___x_4696_);
v___x_4698_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__4));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4699_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4685_, v___x_4698_);
v___x_4700_ = lean_mk_syntax_ident(v_auxFunName_4570_);
lean_inc_ref(v___x_4692_);
lean_inc(v___x_4684_);
v___x_4701_ = l_Lean_Syntax_node2(v___x_4684_, v___x_4699_, v___x_4700_, v___x_4692_);
v___x_4702_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__5));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4703_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4685_, v___x_4702_);
v___x_4704_ = l_Array_append___redArg(v___x_4691_, v_binders_4571_);
lean_inc(v___x_4684_);
v___x_4705_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4705_, 0, v___x_4684_);
lean_ctor_set(v___x_4705_, 1, v___x_4690_);
lean_ctor_set(v___x_4705_, 2, v___x_4704_);
v___x_4706_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__6));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4707_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4572_, v___x_4706_);
v___x_4708_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__16));
lean_inc(v___x_4684_);
v___x_4709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4684_);
lean_ctor_set(v___x_4709_, 1, v___x_4708_);
v___x_4710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__30));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4711_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4572_, v___x_4710_);
v___x_4712_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0);
v___x_4713_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__1));
lean_inc(v_currMacroScope_4683_);
lean_inc(v_quotContext_4682_);
v___x_4714_ = l_Lean_addMacroScope(v_quotContext_4682_, v___x_4713_, v_currMacroScope_4683_);
v___x_4715_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__5));
lean_inc(v___x_4684_);
v___x_4716_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4684_);
lean_ctor_set(v___x_4716_, 1, v___x_4712_);
lean_ctor_set(v___x_4716_, 2, v___x_4714_);
lean_ctor_set(v___x_4716_, 3, v___x_4715_);
v___x_4717_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7);
v___x_4718_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__8));
v___x_4719_ = l_Lean_addMacroScope(v_quotContext_4682_, v___x_4718_, v_currMacroScope_4683_);
v___x_4720_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__12));
lean_inc(v___x_4684_);
v___x_4721_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4684_);
lean_ctor_set(v___x_4721_, 1, v___x_4717_);
lean_ctor_set(v___x_4721_, 2, v___x_4719_);
lean_ctor_set(v___x_4721_, 3, v___x_4720_);
lean_inc(v___x_4684_);
v___x_4722_ = l_Lean_Syntax_node2(v___x_4684_, v___x_4690_, v___x_4721_, v_a_4677_);
lean_inc(v___x_4684_);
v___x_4723_ = l_Lean_Syntax_node2(v___x_4684_, v___x_4711_, v___x_4716_, v___x_4722_);
lean_inc(v___x_4684_);
v___x_4724_ = l_Lean_Syntax_node2(v___x_4684_, v___x_4707_, v___x_4709_, v___x_4723_);
lean_inc(v___x_4684_);
v___x_4725_ = l_Lean_Syntax_node1(v___x_4684_, v___x_4690_, v___x_4724_);
lean_inc(v___x_4684_);
v___x_4726_ = l_Lean_Syntax_node2(v___x_4684_, v___x_4703_, v___x_4705_, v___x_4725_);
v___x_4727_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__7));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4728_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4685_, v___x_4727_);
v___x_4729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6));
lean_inc(v___x_4684_);
v___x_4730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4730_, 0, v___x_4684_);
lean_ctor_set(v___x_4730_, 1, v___x_4729_);
v___x_4731_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__8));
v___x_4732_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__9));
v___x_4733_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4731_, v___x_4732_);
lean_inc_ref_n(v___x_4692_, 2);
lean_inc(v___x_4684_);
v___x_4734_ = l_Lean_Syntax_node2(v___x_4684_, v___x_4733_, v___x_4692_, v___x_4692_);
lean_inc_ref(v___x_4692_);
lean_inc(v___x_4684_);
v___x_4735_ = l_Lean_Syntax_node4(v___x_4684_, v___x_4728_, v___x_4730_, v_a_4587_, v___x_4734_, v___x_4692_);
lean_inc(v___x_4684_);
v___x_4736_ = l_Lean_Syntax_node5(v___x_4684_, v___x_4695_, v___x_4697_, v___x_4701_, v___x_4726_, v___x_4735_, v___x_4692_);
v___x_4737_ = l_Lean_Syntax_node2(v___x_4684_, v___x_4687_, v___x_4693_, v___x_4736_);
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 0, v___x_4737_);
v___x_4739_ = v___x_4679_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v___x_4737_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
return v___x_4739_;
}
}
}
else
{
lean_dec(v_a_4587_);
lean_dec_ref(v___y_4579_);
lean_dec_ref(v___x_4572_);
lean_dec(v_auxFunName_4570_);
lean_dec_ref(v___x_4569_);
lean_dec_ref(v___x_4566_);
return v___x_4676_;
}
}
else
{
goto v___jp_4588_;
}
}
else
{
goto v___jp_4588_;
}
v___jp_4588_:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4589_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__0));
lean_inc_ref(v___x_4566_);
v___x_4590_ = l_Lean_Name_mkStr2(v___x_4566_, v___x_4589_);
lean_inc(v___y_4580_);
lean_inc_ref(v___y_4579_);
lean_inc(v___y_4578_);
lean_inc_ref(v___y_4577_);
lean_inc(v___y_4576_);
lean_inc_ref(v___y_4575_);
lean_inc_ref(v_argNames_4567_);
v___x_4591_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_4565_, v___x_4590_, v_argNames_4567_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
lean_dec_ref(v_ctx_4565_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; lean_object* v___x_4593_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
lean_inc(v_a_4592_);
lean_dec_ref(v___x_4591_);
v___x_4593_ = l_Lean_Elab_Deriving_mkLet(v_a_4592_, v_a_4587_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
lean_dec(v___y_4580_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec(v_a_4592_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; lean_object* v___x_4595_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc(v_a_4594_);
lean_dec_ref(v___x_4593_);
v___x_4595_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(v_indval_4568_, v_argNames_4567_, v___y_4579_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4666_; 
v_a_4596_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4598_ = v___x_4595_;
v_isShared_4599_ = v_isSharedCheck_4666_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4595_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4666_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v_ref_4600_; lean_object* v_quotContext_4601_; lean_object* v_currMacroScope_4602_; uint8_t v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4664_; 
v_ref_4600_ = lean_ctor_get(v___y_4579_, 5);
lean_inc(v_ref_4600_);
v_quotContext_4601_ = lean_ctor_get(v___y_4579_, 10);
lean_inc(v_quotContext_4601_);
v_currMacroScope_4602_ = lean_ctor_get(v___y_4579_, 11);
lean_inc(v_currMacroScope_4602_);
lean_dec_ref(v___y_4579_);
v___x_4603_ = 0;
v___x_4604_ = l_Lean_SourceInfo_fromRef(v_ref_4600_, v___x_4603_);
lean_dec(v_ref_4600_);
v___x_4605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__21));
v___x_4606_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__0));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4607_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4605_, v___x_4606_);
v___x_4608_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__1));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4609_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4605_, v___x_4608_);
v___x_4610_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_4611_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
lean_inc(v___x_4604_);
v___x_4612_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4604_);
lean_ctor_set(v___x_4612_, 1, v___x_4610_);
lean_ctor_set(v___x_4612_, 2, v___x_4611_);
v___x_4613_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__10));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4614_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4605_, v___x_4613_);
lean_inc(v___x_4604_);
v___x_4615_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4604_);
lean_ctor_set(v___x_4615_, 1, v___x_4613_);
lean_inc(v___x_4604_);
v___x_4616_ = l_Lean_Syntax_node1(v___x_4604_, v___x_4614_, v___x_4615_);
lean_inc(v___x_4604_);
v___x_4617_ = l_Lean_Syntax_node1(v___x_4604_, v___x_4610_, v___x_4616_);
lean_inc_ref_n(v___x_4612_, 6);
lean_inc(v___x_4604_);
v___x_4618_ = l_Lean_Syntax_node7(v___x_4604_, v___x_4609_, v___x_4612_, v___x_4612_, v___x_4612_, v___x_4612_, v___x_4612_, v___x_4612_, v___x_4617_);
v___x_4619_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__2));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4620_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4605_, v___x_4619_);
v___x_4621_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__3));
lean_inc(v___x_4604_);
v___x_4622_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4604_);
lean_ctor_set(v___x_4622_, 1, v___x_4621_);
v___x_4623_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__4));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4624_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4605_, v___x_4623_);
v___x_4625_ = lean_mk_syntax_ident(v_auxFunName_4570_);
lean_inc_ref(v___x_4612_);
lean_inc(v___x_4604_);
v___x_4626_ = l_Lean_Syntax_node2(v___x_4604_, v___x_4624_, v___x_4625_, v___x_4612_);
v___x_4627_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__5));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4628_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4605_, v___x_4627_);
v___x_4629_ = l_Array_append___redArg(v___x_4611_, v_binders_4571_);
lean_inc(v___x_4604_);
v___x_4630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4604_);
lean_ctor_set(v___x_4630_, 1, v___x_4610_);
lean_ctor_set(v___x_4630_, 2, v___x_4629_);
v___x_4631_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__6));
lean_inc_ref(v___x_4572_);
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4632_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4572_, v___x_4631_);
v___x_4633_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__16));
lean_inc(v___x_4604_);
v___x_4634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4604_);
lean_ctor_set(v___x_4634_, 1, v___x_4633_);
v___x_4635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__30));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4636_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4572_, v___x_4635_);
v___x_4637_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__0);
v___x_4638_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__1));
lean_inc(v_currMacroScope_4602_);
lean_inc(v_quotContext_4601_);
v___x_4639_ = l_Lean_addMacroScope(v_quotContext_4601_, v___x_4638_, v_currMacroScope_4602_);
v___x_4640_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__5));
lean_inc(v___x_4604_);
v___x_4641_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4641_, 0, v___x_4604_);
lean_ctor_set(v___x_4641_, 1, v___x_4637_);
lean_ctor_set(v___x_4641_, 2, v___x_4639_);
lean_ctor_set(v___x_4641_, 3, v___x_4640_);
v___x_4642_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__7);
v___x_4643_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__8));
v___x_4644_ = l_Lean_addMacroScope(v_quotContext_4601_, v___x_4643_, v_currMacroScope_4602_);
v___x_4645_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___closed__12));
lean_inc(v___x_4604_);
v___x_4646_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4604_);
lean_ctor_set(v___x_4646_, 1, v___x_4642_);
lean_ctor_set(v___x_4646_, 2, v___x_4644_);
lean_ctor_set(v___x_4646_, 3, v___x_4645_);
lean_inc(v___x_4604_);
v___x_4647_ = l_Lean_Syntax_node2(v___x_4604_, v___x_4610_, v___x_4646_, v_a_4596_);
lean_inc(v___x_4604_);
v___x_4648_ = l_Lean_Syntax_node2(v___x_4604_, v___x_4636_, v___x_4641_, v___x_4647_);
lean_inc(v___x_4604_);
v___x_4649_ = l_Lean_Syntax_node2(v___x_4604_, v___x_4632_, v___x_4634_, v___x_4648_);
lean_inc(v___x_4604_);
v___x_4650_ = l_Lean_Syntax_node1(v___x_4604_, v___x_4610_, v___x_4649_);
lean_inc(v___x_4604_);
v___x_4651_ = l_Lean_Syntax_node2(v___x_4604_, v___x_4628_, v___x_4630_, v___x_4650_);
v___x_4652_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__7));
lean_inc_ref(v___x_4569_);
lean_inc_ref(v___x_4566_);
v___x_4653_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4605_, v___x_4652_);
v___x_4654_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonBodyForStruct_spec__3___closed__6));
lean_inc(v___x_4604_);
v___x_4655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4604_);
lean_ctor_set(v___x_4655_, 1, v___x_4654_);
v___x_4656_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__8));
v___x_4657_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction___lam__0___closed__9));
v___x_4658_ = l_Lean_Name_mkStr4(v___x_4566_, v___x_4569_, v___x_4656_, v___x_4657_);
lean_inc_ref_n(v___x_4612_, 2);
lean_inc(v___x_4604_);
v___x_4659_ = l_Lean_Syntax_node2(v___x_4604_, v___x_4658_, v___x_4612_, v___x_4612_);
lean_inc_ref(v___x_4612_);
lean_inc(v___x_4604_);
v___x_4660_ = l_Lean_Syntax_node4(v___x_4604_, v___x_4653_, v___x_4655_, v_a_4594_, v___x_4659_, v___x_4612_);
lean_inc(v___x_4604_);
v___x_4661_ = l_Lean_Syntax_node5(v___x_4604_, v___x_4620_, v___x_4622_, v___x_4626_, v___x_4651_, v___x_4660_, v___x_4612_);
v___x_4662_ = l_Lean_Syntax_node2(v___x_4604_, v___x_4607_, v___x_4618_, v___x_4661_);
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 0, v___x_4662_);
v___x_4664_ = v___x_4598_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4662_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
else
{
lean_dec(v_a_4594_);
lean_dec_ref(v___y_4579_);
lean_dec_ref(v___x_4572_);
lean_dec(v_auxFunName_4570_);
lean_dec_ref(v___x_4569_);
lean_dec_ref(v___x_4566_);
return v___x_4595_;
}
}
else
{
lean_dec_ref(v___y_4579_);
lean_dec_ref(v___x_4572_);
lean_dec(v_auxFunName_4570_);
lean_dec_ref(v___x_4569_);
lean_dec_ref(v_indval_4568_);
lean_dec_ref(v_argNames_4567_);
lean_dec_ref(v___x_4566_);
return v___x_4593_;
}
}
else
{
lean_object* v_a_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4674_; 
lean_dec(v_a_4587_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec_ref(v___x_4572_);
lean_dec(v_auxFunName_4570_);
lean_dec_ref(v___x_4569_);
lean_dec_ref(v_indval_4568_);
lean_dec_ref(v_argNames_4567_);
lean_dec_ref(v___x_4566_);
v_a_4667_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4669_ = v___x_4591_;
v_isShared_4670_ = v_isSharedCheck_4674_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_a_4667_);
lean_dec(v___x_4591_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4674_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v___x_4672_; 
if (v_isShared_4670_ == 0)
{
v___x_4672_ = v___x_4669_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_a_4667_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
}
}
}
else
{
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec_ref(v___x_4572_);
lean_dec(v_auxFunName_4570_);
lean_dec_ref(v___x_4569_);
lean_dec_ref(v_indval_4568_);
lean_dec_ref(v_argNames_4567_);
lean_dec_ref(v___x_4566_);
lean_dec_ref(v_ctx_4565_);
return v___x_4586_;
}
}
else
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec_ref(v___x_4572_);
lean_dec(v_auxFunName_4570_);
lean_dec_ref(v___x_4569_);
lean_dec_ref(v_indval_4568_);
lean_dec_ref(v_argNames_4567_);
lean_dec_ref(v___x_4566_);
lean_dec_ref(v_ctx_4565_);
v_a_4742_ = lean_ctor_get(v___x_4584_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4744_ = v___x_4584_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4584_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4747_; 
if (v_isShared_4745_ == 0)
{
v___x_4747_ = v___x_4744_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___boxed(lean_object** _args){
lean_object* v_targetType_4750_ = _args[0];
lean_object* v_ctx_4751_ = _args[1];
lean_object* v___x_4752_ = _args[2];
lean_object* v_argNames_4753_ = _args[3];
lean_object* v_indval_4754_ = _args[4];
lean_object* v___x_4755_ = _args[5];
lean_object* v_auxFunName_4756_ = _args[6];
lean_object* v_binders_4757_ = _args[7];
lean_object* v___x_4758_ = _args[8];
lean_object* v_usePartial_4759_ = _args[9];
lean_object* v_x_4760_ = _args[10];
lean_object* v___y_4761_ = _args[11];
lean_object* v___y_4762_ = _args[12];
lean_object* v___y_4763_ = _args[13];
lean_object* v___y_4764_ = _args[14];
lean_object* v___y_4765_ = _args[15];
lean_object* v___y_4766_ = _args[16];
lean_object* v___y_4767_ = _args[17];
_start:
{
uint8_t v_usePartial_boxed_4768_; lean_object* v_res_4769_; 
v_usePartial_boxed_4768_ = lean_unbox(v_usePartial_4759_);
v_res_4769_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0(v_targetType_4750_, v_ctx_4751_, v___x_4752_, v_argNames_4753_, v_indval_4754_, v___x_4755_, v_auxFunName_4756_, v_binders_4757_, v___x_4758_, v_usePartial_boxed_4768_, v_x_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_);
lean_dec_ref(v_x_4760_);
lean_dec_ref(v_binders_4757_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction(lean_object* v_ctx_4770_, lean_object* v_i_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v_typeInfos_4779_; lean_object* v_auxFunNames_4780_; uint8_t v_usePartial_4781_; lean_object* v___x_4782_; lean_object* v_indval_4783_; lean_object* v___x_4784_; 
v_typeInfos_4779_ = lean_ctor_get(v_ctx_4770_, 1);
v_auxFunNames_4780_ = lean_ctor_get(v_ctx_4770_, 2);
v_usePartial_4781_ = lean_ctor_get_uint8(v_ctx_4770_, sizeof(void*)*3);
v___x_4782_ = l_Lean_instInhabitedInductiveVal_default;
v_indval_4783_ = lean_array_get(v___x_4782_, v_typeInfos_4779_, v_i_4771_);
lean_inc(v_a_4777_);
lean_inc_ref(v_a_4776_);
lean_inc(v_a_4775_);
lean_inc_ref(v_a_4774_);
lean_inc(v_a_4773_);
lean_inc_ref(v_a_4772_);
lean_inc(v_indval_4783_);
v___x_4784_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader(v_indval_4783_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; lean_object* v_binders_4786_; lean_object* v_argNames_4787_; lean_object* v_targetType_4788_; lean_object* v___x_4789_; lean_object* v_auxFunName_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___f_4795_; lean_object* v___x_4796_; 
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
lean_inc(v_a_4785_);
lean_dec_ref(v___x_4784_);
v_binders_4786_ = lean_ctor_get(v_a_4785_, 0);
lean_inc_ref(v_binders_4786_);
v_argNames_4787_ = lean_ctor_get(v_a_4785_, 1);
lean_inc_ref(v_argNames_4787_);
v_targetType_4788_ = lean_ctor_get(v_a_4785_, 3);
lean_inc(v_targetType_4788_);
lean_dec(v_a_4785_);
v___x_4789_ = lean_box(0);
v_auxFunName_4790_ = lean_array_get(v___x_4789_, v_auxFunNames_4780_, v_i_4771_);
v___x_4791_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__0));
v___x_4792_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__2));
v___x_4793_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__3));
v___x_4794_ = lean_box(v_usePartial_4781_);
lean_inc_ref(v_binders_4786_);
v___f_4795_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___lam__0___boxed), 18, 10);
lean_closure_set(v___f_4795_, 0, v_targetType_4788_);
lean_closure_set(v___f_4795_, 1, v_ctx_4770_);
lean_closure_set(v___f_4795_, 2, v___x_4791_);
lean_closure_set(v___f_4795_, 3, v_argNames_4787_);
lean_closure_set(v___f_4795_, 4, v_indval_4783_);
lean_closure_set(v___f_4795_, 5, v___x_4792_);
lean_closure_set(v___f_4795_, 6, v_auxFunName_4790_);
lean_closure_set(v___f_4795_, 7, v_binders_4786_);
lean_closure_set(v___f_4795_, 8, v___x_4793_);
lean_closure_set(v___f_4795_, 9, v___x_4794_);
v___x_4796_ = l_Lean_Elab_Term_elabBinders___redArg(v_binders_4786_, v___f_4795_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
return v___x_4796_;
}
else
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4804_; 
lean_dec(v_indval_4783_);
lean_dec(v_a_4777_);
lean_dec_ref(v_a_4776_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
lean_dec(v_a_4773_);
lean_dec_ref(v_a_4772_);
lean_dec_ref(v_ctx_4770_);
v_a_4797_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4804_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4804_ == 0)
{
v___x_4799_ = v___x_4784_;
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v___x_4784_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4802_; 
if (v_isShared_4800_ == 0)
{
v___x_4802_ = v___x_4799_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_a_4797_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction___boxed(lean_object* v_ctx_4805_, lean_object* v_i_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction(v_ctx_4805_, v_i_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
lean_dec(v_i_4806_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___redArg(lean_object* v_upperBound_4815_, lean_object* v_ctx_4816_, lean_object* v_a_4817_, lean_object* v_b_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_){
_start:
{
uint8_t v___x_4826_; 
v___x_4826_ = lean_nat_dec_lt(v_a_4817_, v_upperBound_4815_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4827_; 
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
lean_dec(v_a_4817_);
lean_dec_ref(v_ctx_4816_);
v___x_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4827_, 0, v_b_4818_);
return v___x_4827_;
}
else
{
lean_object* v___x_4828_; 
lean_inc(v___y_4824_);
lean_inc_ref(v___y_4823_);
lean_inc(v___y_4822_);
lean_inc_ref(v___y_4821_);
lean_inc(v___y_4820_);
lean_inc_ref(v___y_4819_);
lean_inc_ref(v_ctx_4816_);
v___x_4828_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonAuxFunction(v_ctx_4816_, v_a_4817_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v_a_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4829_);
lean_dec_ref(v___x_4828_);
v___x_4830_ = lean_array_push(v_b_4818_, v_a_4829_);
v___x_4831_ = lean_unsigned_to_nat(1u);
v___x_4832_ = lean_nat_add(v_a_4817_, v___x_4831_);
lean_dec(v_a_4817_);
v_a_4817_ = v___x_4832_;
v_b_4818_ = v___x_4830_;
goto _start;
}
else
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4841_; 
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
lean_dec_ref(v_b_4818_);
lean_dec(v_a_4817_);
lean_dec_ref(v_ctx_4816_);
v_a_4834_ = lean_ctor_get(v___x_4828_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4836_ = v___x_4828_;
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4828_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4839_; 
if (v_isShared_4837_ == 0)
{
v___x_4839_ = v___x_4836_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4834_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_4842_, lean_object* v_ctx_4843_, lean_object* v_a_4844_, lean_object* v_b_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_){
_start:
{
lean_object* v_res_4853_; 
v_res_4853_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___redArg(v_upperBound_4842_, v_ctx_4843_, v_a_4844_, v_b_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_);
lean_dec(v_upperBound_4842_);
return v_res_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock(lean_object* v_ctx_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v_typeInfos_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v_auxDefs_4872_; lean_object* v___x_4873_; 
v_typeInfos_4869_ = lean_ctor_get(v_ctx_4861_, 1);
v___x_4870_ = lean_array_get_size(v_typeInfos_4869_);
v___x_4871_ = lean_unsigned_to_nat(0u);
v_auxDefs_4872_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___closed__0));
lean_inc_ref(v_a_4866_);
v___x_4873_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___redArg(v___x_4870_, v_ctx_4861_, v___x_4871_, v_auxDefs_4872_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4894_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4876_ = v___x_4873_;
v_isShared_4877_ = v_isSharedCheck_4894_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4873_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4894_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v_ref_4878_; uint8_t v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4892_; 
v_ref_4878_ = lean_ctor_get(v_a_4866_, 5);
lean_inc(v_ref_4878_);
lean_dec_ref(v_a_4866_);
v___x_4879_ = 0;
v___x_4880_ = l_Lean_SourceInfo_fromRef(v_ref_4878_, v___x_4879_);
lean_dec(v_ref_4878_);
v___x_4881_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__0));
v___x_4882_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1));
lean_inc(v___x_4880_);
v___x_4883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4880_);
lean_ctor_set(v___x_4883_, 1, v___x_4881_);
v___x_4884_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_4885_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v___x_4886_ = l_Array_append___redArg(v___x_4885_, v_a_4874_);
lean_dec(v_a_4874_);
lean_inc(v___x_4880_);
v___x_4887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4880_);
lean_ctor_set(v___x_4887_, 1, v___x_4884_);
lean_ctor_set(v___x_4887_, 2, v___x_4886_);
v___x_4888_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__2));
lean_inc(v___x_4880_);
v___x_4889_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4880_);
lean_ctor_set(v___x_4889_, 1, v___x_4888_);
v___x_4890_ = l_Lean_Syntax_node3(v___x_4880_, v___x_4882_, v___x_4883_, v___x_4887_, v___x_4889_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v___x_4890_);
v___x_4892_ = v___x_4876_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4890_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
else
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4902_; 
lean_dec_ref(v_a_4866_);
v_a_4895_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4873_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4873_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4895_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___boxed(lean_object* v_ctx_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock(v_ctx_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0(lean_object* v_upperBound_4912_, lean_object* v_ctx_4913_, lean_object* v_inst_4914_, lean_object* v_R_4915_, lean_object* v_a_4916_, lean_object* v_b_4917_, lean_object* v_c_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___redArg(v_upperBound_4912_, v_ctx_4913_, v_a_4916_, v_b_4917_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0___boxed(lean_object* v_upperBound_4927_, lean_object* v_ctx_4928_, lean_object* v_inst_4929_, lean_object* v_R_4930_, lean_object* v_a_4931_, lean_object* v_b_4932_, lean_object* v_c_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock_spec__0(v_upperBound_4927_, v_ctx_4928_, v_inst_4929_, v_R_4930_, v_a_4931_, v_b_4932_, v_c_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_);
lean_dec(v_upperBound_4927_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___redArg(lean_object* v_upperBound_4942_, lean_object* v_ctx_4943_, lean_object* v_a_4944_, lean_object* v_b_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_){
_start:
{
uint8_t v___x_4953_; 
v___x_4953_ = lean_nat_dec_lt(v_a_4944_, v_upperBound_4942_);
if (v___x_4953_ == 0)
{
lean_object* v___x_4954_; 
lean_dec(v___y_4951_);
lean_dec_ref(v___y_4950_);
lean_dec(v___y_4949_);
lean_dec_ref(v___y_4948_);
lean_dec(v___y_4947_);
lean_dec_ref(v___y_4946_);
lean_dec(v_a_4944_);
lean_dec_ref(v_ctx_4943_);
v___x_4954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4954_, 0, v_b_4945_);
return v___x_4954_;
}
else
{
lean_object* v___x_4955_; 
lean_inc(v___y_4951_);
lean_inc_ref(v___y_4950_);
lean_inc(v___y_4949_);
lean_inc_ref(v___y_4948_);
lean_inc(v___y_4947_);
lean_inc_ref(v___y_4946_);
lean_inc_ref(v_ctx_4943_);
v___x_4955_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonAuxFunction(v_ctx_4943_, v_a_4944_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_object* v_a_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v_a_4956_ = lean_ctor_get(v___x_4955_, 0);
lean_inc(v_a_4956_);
lean_dec_ref(v___x_4955_);
v___x_4957_ = lean_array_push(v_b_4945_, v_a_4956_);
v___x_4958_ = lean_unsigned_to_nat(1u);
v___x_4959_ = lean_nat_add(v_a_4944_, v___x_4958_);
lean_dec(v_a_4944_);
v_a_4944_ = v___x_4959_;
v_b_4945_ = v___x_4957_;
goto _start;
}
else
{
lean_object* v_a_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4968_; 
lean_dec(v___y_4951_);
lean_dec_ref(v___y_4950_);
lean_dec(v___y_4949_);
lean_dec_ref(v___y_4948_);
lean_dec(v___y_4947_);
lean_dec_ref(v___y_4946_);
lean_dec_ref(v_b_4945_);
lean_dec(v_a_4944_);
lean_dec_ref(v_ctx_4943_);
v_a_4961_ = lean_ctor_get(v___x_4955_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4955_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4963_ = v___x_4955_;
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_a_4961_);
lean_dec(v___x_4955_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4966_; 
if (v_isShared_4964_ == 0)
{
v___x_4966_ = v___x_4963_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4961_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_4969_, lean_object* v_ctx_4970_, lean_object* v_a_4971_, lean_object* v_b_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_){
_start:
{
lean_object* v_res_4980_; 
v_res_4980_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___redArg(v_upperBound_4969_, v_ctx_4970_, v_a_4971_, v_b_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_);
lean_dec(v_upperBound_4969_);
return v_res_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock(lean_object* v_ctx_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_){
_start:
{
lean_object* v_typeInfos_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v_auxDefs_4992_; lean_object* v___x_4993_; 
v_typeInfos_4989_ = lean_ctor_get(v_ctx_4981_, 1);
v___x_4990_ = lean_array_get_size(v_typeInfos_4989_);
v___x_4991_ = lean_unsigned_to_nat(0u);
v_auxDefs_4992_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__5___redArg___closed__0));
lean_inc_ref(v_a_4986_);
v___x_4993_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___redArg(v___x_4990_, v_ctx_4981_, v___x_4991_, v_auxDefs_4992_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5014_; 
v_a_4994_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_4996_ = v___x_4993_;
v_isShared_4997_ = v_isSharedCheck_5014_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v___x_4993_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5014_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v_ref_4998_; uint8_t v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5012_; 
v_ref_4998_ = lean_ctor_get(v_a_4986_, 5);
lean_inc(v_ref_4998_);
lean_dec_ref(v_a_4986_);
v___x_4999_ = 0;
v___x_5000_ = l_Lean_SourceInfo_fromRef(v_ref_4998_, v___x_4999_);
lean_dec(v_ref_4998_);
v___x_5001_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__0));
v___x_5002_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__1));
lean_inc(v___x_5000_);
v___x_5003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5003_, 0, v___x_5000_);
lean_ctor_set(v___x_5003_, 1, v___x_5001_);
v___x_5004_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__8));
v___x_5005_ = lean_obj_once(&l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24, &l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24_once, _init_l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__24);
v___x_5006_ = l_Array_append___redArg(v___x_5005_, v_a_4994_);
lean_dec(v_a_4994_);
lean_inc(v___x_5000_);
v___x_5007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5007_, 0, v___x_5000_);
lean_ctor_set(v___x_5007_, 1, v___x_5004_);
lean_ctor_set(v___x_5007_, 2, v___x_5006_);
v___x_5008_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock___closed__2));
lean_inc(v___x_5000_);
v___x_5009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5009_, 0, v___x_5000_);
lean_ctor_set(v___x_5009_, 1, v___x_5008_);
v___x_5010_ = l_Lean_Syntax_node3(v___x_5000_, v___x_5002_, v___x_5003_, v___x_5007_, v___x_5009_);
if (v_isShared_4997_ == 0)
{
lean_ctor_set(v___x_4996_, 0, v___x_5010_);
v___x_5012_ = v___x_4996_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v___x_5010_);
v___x_5012_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
return v___x_5012_;
}
}
}
else
{
lean_object* v_a_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5022_; 
lean_dec_ref(v_a_4986_);
v_a_5015_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5022_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5022_ == 0)
{
v___x_5017_ = v___x_4993_;
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_a_5015_);
lean_dec(v___x_4993_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5020_; 
if (v_isShared_5018_ == 0)
{
v___x_5020_ = v___x_5017_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5015_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock___boxed(lean_object* v_ctx_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_){
_start:
{
lean_object* v_res_5031_; 
v_res_5031_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock(v_ctx_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_);
return v_res_5031_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0(lean_object* v_upperBound_5032_, lean_object* v_ctx_5033_, lean_object* v_inst_5034_, lean_object* v_R_5035_, lean_object* v_a_5036_, lean_object* v_b_5037_, lean_object* v_c_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_){
_start:
{
lean_object* v___x_5046_; 
v___x_5046_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___redArg(v_upperBound_5032_, v_ctx_5033_, v_a_5036_, v_b_5037_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
return v___x_5046_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0___boxed(lean_object* v_upperBound_5047_, lean_object* v_ctx_5048_, lean_object* v_inst_5049_, lean_object* v_R_5050_, lean_object* v_a_5051_, lean_object* v_b_5052_, lean_object* v_c_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock_spec__0(v_upperBound_5047_, v_ctx_5048_, v_inst_5049_, v_R_5050_, v_a_5051_, v_b_5052_, v_c_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_);
lean_dec(v_upperBound_5047_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg(lean_object* v_cls_5065_, lean_object* v___y_5066_){
_start:
{
lean_object* v_options_5068_; uint8_t v_hasTrace_5069_; 
v_options_5068_ = lean_ctor_get(v___y_5066_, 2);
v_hasTrace_5069_ = lean_ctor_get_uint8(v_options_5068_, sizeof(void*)*1);
if (v_hasTrace_5069_ == 0)
{
lean_object* v___x_5070_; lean_object* v___x_5071_; 
lean_dec(v_cls_5065_);
v___x_5070_ = lean_box(v_hasTrace_5069_);
v___x_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5070_);
return v___x_5071_;
}
else
{
lean_object* v_inheritedTraceOptions_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; uint8_t v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v_inheritedTraceOptions_5072_ = lean_ctor_get(v___y_5066_, 13);
v___x_5073_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg___closed__1));
v___x_5074_ = l_Lean_Name_append(v___x_5073_, v_cls_5065_);
v___x_5075_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5072_, v_options_5068_, v___x_5074_);
lean_dec(v___x_5074_);
v___x_5076_ = lean_box(v___x_5075_);
v___x_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5076_);
return v___x_5077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg___boxed(lean_object* v_cls_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_){
_start:
{
lean_object* v_res_5081_; 
v_res_5081_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg(v_cls_5078_, v___y_5079_);
lean_dec_ref(v___y_5079_);
return v_res_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0(lean_object* v_cls_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_){
_start:
{
lean_object* v___x_5090_; 
v___x_5090_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg(v_cls_5082_, v___y_5087_);
return v___x_5090_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___boxed(lean_object* v_cls_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
lean_object* v_res_5099_; 
v_res_5099_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0(v_cls_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
lean_dec(v___y_5097_);
lean_dec_ref(v___y_5096_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
return v_res_5099_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_5100_; double v___x_5101_; 
v___x_5100_ = lean_unsigned_to_nat(0u);
v___x_5101_ = lean_float_of_nat(v___x_5100_);
return v___x_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg(lean_object* v_cls_5104_, lean_object* v_msg_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_){
_start:
{
lean_object* v_ref_5111_; lean_object* v___x_5112_; lean_object* v_a_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5157_; 
v_ref_5111_ = lean_ctor_get(v___y_5108_, 5);
v___x_5112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonBodyForInduct_mkAlts_spec__0_spec__0_spec__2(v_msg_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_);
v_a_5113_ = lean_ctor_get(v___x_5112_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5115_ = v___x_5112_;
v_isShared_5116_ = v_isSharedCheck_5157_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_a_5113_);
lean_dec(v___x_5112_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5157_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5117_; lean_object* v_traceState_5118_; lean_object* v_env_5119_; lean_object* v_nextMacroScope_5120_; lean_object* v_ngen_5121_; lean_object* v_auxDeclNGen_5122_; lean_object* v_cache_5123_; lean_object* v_messages_5124_; lean_object* v_infoState_5125_; lean_object* v_snapshotTasks_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5156_; 
v___x_5117_ = lean_st_ref_take(v___y_5109_);
v_traceState_5118_ = lean_ctor_get(v___x_5117_, 4);
v_env_5119_ = lean_ctor_get(v___x_5117_, 0);
v_nextMacroScope_5120_ = lean_ctor_get(v___x_5117_, 1);
v_ngen_5121_ = lean_ctor_get(v___x_5117_, 2);
v_auxDeclNGen_5122_ = lean_ctor_get(v___x_5117_, 3);
v_cache_5123_ = lean_ctor_get(v___x_5117_, 5);
v_messages_5124_ = lean_ctor_get(v___x_5117_, 6);
v_infoState_5125_ = lean_ctor_get(v___x_5117_, 7);
v_snapshotTasks_5126_ = lean_ctor_get(v___x_5117_, 8);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5117_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5128_ = v___x_5117_;
v_isShared_5129_ = v_isSharedCheck_5156_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_snapshotTasks_5126_);
lean_inc(v_infoState_5125_);
lean_inc(v_messages_5124_);
lean_inc(v_cache_5123_);
lean_inc(v_traceState_5118_);
lean_inc(v_auxDeclNGen_5122_);
lean_inc(v_ngen_5121_);
lean_inc(v_nextMacroScope_5120_);
lean_inc(v_env_5119_);
lean_dec(v___x_5117_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5156_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
uint64_t v_tid_5130_; lean_object* v_traces_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5155_; 
v_tid_5130_ = lean_ctor_get_uint64(v_traceState_5118_, sizeof(void*)*1);
v_traces_5131_ = lean_ctor_get(v_traceState_5118_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v_traceState_5118_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5133_ = v_traceState_5118_;
v_isShared_5134_ = v_isSharedCheck_5155_;
goto v_resetjp_5132_;
}
else
{
lean_inc(v_traces_5131_);
lean_dec(v_traceState_5118_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5155_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
lean_object* v___x_5135_; double v___x_5136_; uint8_t v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5145_; 
v___x_5135_ = lean_box(0);
v___x_5136_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__0);
v___x_5137_ = 0;
v___x_5138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__9));
v___x_5139_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5139_, 0, v_cls_5104_);
lean_ctor_set(v___x_5139_, 1, v___x_5135_);
lean_ctor_set(v___x_5139_, 2, v___x_5138_);
lean_ctor_set_float(v___x_5139_, sizeof(void*)*3, v___x_5136_);
lean_ctor_set_float(v___x_5139_, sizeof(void*)*3 + 8, v___x_5136_);
lean_ctor_set_uint8(v___x_5139_, sizeof(void*)*3 + 16, v___x_5137_);
v___x_5140_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___closed__1));
v___x_5141_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5139_);
lean_ctor_set(v___x_5141_, 1, v_a_5113_);
lean_ctor_set(v___x_5141_, 2, v___x_5140_);
lean_inc(v_ref_5111_);
v___x_5142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5142_, 0, v_ref_5111_);
lean_ctor_set(v___x_5142_, 1, v___x_5141_);
v___x_5143_ = l_Lean_PersistentArray_push___redArg(v_traces_5131_, v___x_5142_);
if (v_isShared_5134_ == 0)
{
lean_ctor_set(v___x_5133_, 0, v___x_5143_);
v___x_5145_ = v___x_5133_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v___x_5143_);
lean_ctor_set_uint64(v_reuseFailAlloc_5154_, sizeof(void*)*1, v_tid_5130_);
v___x_5145_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
lean_object* v___x_5147_; 
if (v_isShared_5129_ == 0)
{
lean_ctor_set(v___x_5128_, 4, v___x_5145_);
v___x_5147_ = v___x_5128_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_env_5119_);
lean_ctor_set(v_reuseFailAlloc_5153_, 1, v_nextMacroScope_5120_);
lean_ctor_set(v_reuseFailAlloc_5153_, 2, v_ngen_5121_);
lean_ctor_set(v_reuseFailAlloc_5153_, 3, v_auxDeclNGen_5122_);
lean_ctor_set(v_reuseFailAlloc_5153_, 4, v___x_5145_);
lean_ctor_set(v_reuseFailAlloc_5153_, 5, v_cache_5123_);
lean_ctor_set(v_reuseFailAlloc_5153_, 6, v_messages_5124_);
lean_ctor_set(v_reuseFailAlloc_5153_, 7, v_infoState_5125_);
lean_ctor_set(v_reuseFailAlloc_5153_, 8, v_snapshotTasks_5126_);
v___x_5147_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5151_; 
v___x_5148_ = lean_st_ref_set(v___y_5109_, v___x_5147_);
v___x_5149_ = lean_box(0);
if (v_isShared_5116_ == 0)
{
lean_ctor_set(v___x_5115_, 0, v___x_5149_);
v___x_5151_ = v___x_5115_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v___x_5149_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg___boxed(lean_object* v_cls_5158_, lean_object* v_msg_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_){
_start:
{
lean_object* v_res_5165_; 
v_res_5165_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg(v_cls_5158_, v_msg_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
lean_dec(v___y_5161_);
lean_dec_ref(v___y_5160_);
return v_res_5165_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__1(lean_object* v_a_5166_, lean_object* v_a_5167_){
_start:
{
if (lean_obj_tag(v_a_5166_) == 0)
{
lean_object* v___x_5168_; 
v___x_5168_ = l_List_reverse___redArg(v_a_5167_);
return v___x_5168_;
}
else
{
lean_object* v_head_5169_; lean_object* v_tail_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5179_; 
v_head_5169_ = lean_ctor_get(v_a_5166_, 0);
v_tail_5170_ = lean_ctor_get(v_a_5166_, 1);
v_isSharedCheck_5179_ = !lean_is_exclusive(v_a_5166_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5172_ = v_a_5166_;
v_isShared_5173_ = v_isSharedCheck_5179_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_tail_5170_);
lean_inc(v_head_5169_);
lean_dec(v_a_5166_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5179_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
lean_object* v___x_5174_; lean_object* v___x_5176_; 
v___x_5174_ = l_Lean_MessageData_ofSyntax(v_head_5169_);
if (v_isShared_5173_ == 0)
{
lean_ctor_set(v___x_5172_, 1, v_a_5167_);
lean_ctor_set(v___x_5172_, 0, v___x_5174_);
v___x_5176_ = v___x_5172_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v___x_5174_);
lean_ctor_set(v_reuseFailAlloc_5178_, 1, v_a_5167_);
v___x_5176_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
v_a_5166_ = v_tail_5170_;
v_a_5167_ = v___x_5176_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2(void){
_start:
{
lean_object* v___x_5185_; lean_object* v___x_5186_; 
v___x_5185_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__1));
v___x_5186_ = l_Lean_stringToMessageData(v___x_5185_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance(lean_object* v_declName_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_){
_start:
{
lean_object* v___x_5195_; lean_object* v___x_5196_; uint8_t v___x_5197_; lean_object* v___x_5198_; 
v___x_5195_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__2));
v___x_5196_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Deriving_FromToJson_mkToJsonBodyForStruct_spec__0___redArg___closed__32));
v___x_5197_ = 1;
lean_inc(v_a_5193_);
lean_inc_ref(v_a_5192_);
lean_inc(v_a_5191_);
lean_inc_ref(v_a_5190_);
lean_inc(v_a_5189_);
lean_inc_ref(v_a_5188_);
lean_inc(v_declName_5187_);
v___x_5198_ = l_Lean_Elab_Deriving_mkContext(v___x_5195_, v___x_5196_, v_declName_5187_, v___x_5197_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_);
if (lean_obj_tag(v___x_5198_) == 0)
{
lean_object* v_a_5199_; lean_object* v___x_5200_; 
v_a_5199_ = lean_ctor_get(v___x_5198_, 0);
lean_inc(v_a_5199_);
lean_dec_ref(v___x_5198_);
lean_inc(v_a_5193_);
lean_inc_ref(v_a_5192_);
lean_inc(v_a_5191_);
lean_inc_ref(v_a_5190_);
lean_inc(v_a_5189_);
lean_inc_ref(v_a_5188_);
lean_inc(v_a_5199_);
v___x_5200_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonMutualBlock(v_a_5199_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_);
if (lean_obj_tag(v___x_5200_) == 0)
{
lean_object* v_a_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; 
v_a_5201_ = lean_ctor_get(v___x_5200_, 0);
lean_inc(v_a_5201_);
lean_dec_ref(v___x_5200_);
v___x_5202_ = lean_unsigned_to_nat(1u);
v___x_5203_ = lean_mk_empty_array_with_capacity(v___x_5202_);
lean_inc_ref(v___x_5203_);
v___x_5204_ = lean_array_push(v___x_5203_, v_declName_5187_);
lean_inc(v_a_5193_);
lean_inc_ref(v_a_5192_);
lean_inc(v_a_5191_);
lean_inc_ref(v_a_5190_);
v___x_5205_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_5199_, v___x_5195_, v___x_5204_, v___x_5197_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_);
lean_dec_ref(v___x_5204_);
if (lean_obj_tag(v___x_5205_) == 0)
{
lean_object* v_a_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v_a_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5242_; 
v_a_5206_ = lean_ctor_get(v___x_5205_, 0);
lean_inc(v_a_5206_);
lean_dec_ref(v___x_5205_);
v___x_5207_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__0));
v___x_5208_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg(v___x_5207_, v_a_5192_);
v_a_5209_ = lean_ctor_get(v___x_5208_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5208_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5211_ = v___x_5208_;
v_isShared_5212_ = v_isSharedCheck_5242_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_a_5209_);
lean_dec(v___x_5208_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5242_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___x_5213_; lean_object* v___x_5214_; uint8_t v___x_5215_; 
v___x_5213_ = lean_array_push(v___x_5203_, v_a_5201_);
v___x_5214_ = l_Array_append___redArg(v___x_5213_, v_a_5206_);
lean_dec(v_a_5206_);
v___x_5215_ = lean_unbox(v_a_5209_);
lean_dec(v_a_5209_);
if (v___x_5215_ == 0)
{
lean_object* v___x_5217_; 
lean_dec(v_a_5193_);
lean_dec_ref(v_a_5192_);
lean_dec(v_a_5191_);
lean_dec_ref(v_a_5190_);
if (v_isShared_5212_ == 0)
{
lean_ctor_set(v___x_5211_, 0, v___x_5214_);
v___x_5217_ = v___x_5211_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v___x_5214_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
else
{
lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
lean_del_object(v___x_5211_);
v___x_5219_ = lean_obj_once(&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2, &l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2_once, _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2);
lean_inc_ref(v___x_5214_);
v___x_5220_ = lean_array_to_list(v___x_5214_);
v___x_5221_ = lean_box(0);
v___x_5222_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__1(v___x_5220_, v___x_5221_);
v___x_5223_ = l_Lean_MessageData_ofList(v___x_5222_);
v___x_5224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5224_, 0, v___x_5219_);
lean_ctor_set(v___x_5224_, 1, v___x_5223_);
v___x_5225_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg(v___x_5207_, v___x_5224_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_);
lean_dec(v_a_5193_);
lean_dec_ref(v_a_5192_);
lean_dec(v_a_5191_);
lean_dec_ref(v_a_5190_);
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5232_; 
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5232_ == 0)
{
lean_object* v_unused_5233_; 
v_unused_5233_ = lean_ctor_get(v___x_5225_, 0);
lean_dec(v_unused_5233_);
v___x_5227_ = v___x_5225_;
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
else
{
lean_dec(v___x_5225_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5230_; 
if (v_isShared_5228_ == 0)
{
lean_ctor_set(v___x_5227_, 0, v___x_5214_);
v___x_5230_ = v___x_5227_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v___x_5214_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
else
{
lean_object* v_a_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5241_; 
lean_dec_ref(v___x_5214_);
v_a_5234_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5241_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5236_ = v___x_5225_;
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_a_5234_);
lean_dec(v___x_5225_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5239_; 
if (v_isShared_5237_ == 0)
{
v___x_5239_ = v___x_5236_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5240_; 
v_reuseFailAlloc_5240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5240_, 0, v_a_5234_);
v___x_5239_ = v_reuseFailAlloc_5240_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
return v___x_5239_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_5203_);
lean_dec(v_a_5201_);
lean_dec(v_a_5193_);
lean_dec_ref(v_a_5192_);
lean_dec(v_a_5191_);
lean_dec_ref(v_a_5190_);
return v___x_5205_;
}
}
else
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5250_; 
lean_dec(v_a_5199_);
lean_dec(v_a_5193_);
lean_dec_ref(v_a_5192_);
lean_dec(v_a_5191_);
lean_dec_ref(v_a_5190_);
lean_dec(v_a_5189_);
lean_dec_ref(v_a_5188_);
lean_dec(v_declName_5187_);
v_a_5243_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5245_ = v___x_5200_;
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5200_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v___x_5248_; 
if (v_isShared_5246_ == 0)
{
v___x_5248_ = v___x_5245_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_a_5243_);
v___x_5248_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
return v___x_5248_;
}
}
}
}
else
{
lean_object* v_a_5251_; lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5258_; 
lean_dec(v_a_5193_);
lean_dec_ref(v_a_5192_);
lean_dec(v_a_5191_);
lean_dec_ref(v_a_5190_);
lean_dec(v_a_5189_);
lean_dec_ref(v_a_5188_);
lean_dec(v_declName_5187_);
v_a_5251_ = lean_ctor_get(v___x_5198_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5198_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5253_ = v___x_5198_;
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
else
{
lean_inc(v_a_5251_);
lean_dec(v___x_5198_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
v_resetjp_5252_:
{
lean_object* v___x_5256_; 
if (v_isShared_5254_ == 0)
{
v___x_5256_ = v___x_5253_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v_a_5251_);
v___x_5256_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
return v___x_5256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___boxed(lean_object* v_declName_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v_res_5267_; 
v_res_5267_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance(v_declName_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_);
return v_res_5267_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2(lean_object* v_cls_5268_, lean_object* v_msg_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_){
_start:
{
lean_object* v___x_5277_; 
v___x_5277_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg(v_cls_5268_, v_msg_5269_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
return v___x_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___boxed(lean_object* v_cls_5278_, lean_object* v_msg_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_){
_start:
{
lean_object* v_res_5287_; 
v_res_5287_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2(v_cls_5278_, v_msg_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_);
lean_dec(v___y_5285_);
lean_dec_ref(v___y_5284_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
return v_res_5287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance(lean_object* v_declName_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_){
_start:
{
lean_object* v___x_5301_; lean_object* v___x_5302_; uint8_t v___x_5303_; lean_object* v___x_5304_; 
v___x_5301_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__1));
v___x_5302_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__0));
v___x_5303_ = 1;
lean_inc(v_a_5299_);
lean_inc_ref(v_a_5298_);
lean_inc(v_a_5297_);
lean_inc_ref(v_a_5296_);
lean_inc(v_a_5295_);
lean_inc_ref(v_a_5294_);
lean_inc(v_declName_5293_);
v___x_5304_ = l_Lean_Elab_Deriving_mkContext(v___x_5301_, v___x_5302_, v_declName_5293_, v___x_5303_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
if (lean_obj_tag(v___x_5304_) == 0)
{
lean_object* v_a_5305_; lean_object* v___x_5306_; 
v_a_5305_ = lean_ctor_get(v___x_5304_, 0);
lean_inc(v_a_5305_);
lean_dec_ref(v___x_5304_);
lean_inc(v_a_5299_);
lean_inc_ref(v_a_5298_);
lean_inc(v_a_5297_);
lean_inc_ref(v_a_5296_);
lean_inc(v_a_5295_);
lean_inc_ref(v_a_5294_);
lean_inc(v_a_5305_);
v___x_5306_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonMutualBlock(v_a_5305_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
if (lean_obj_tag(v___x_5306_) == 0)
{
lean_object* v_a_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; 
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
lean_inc(v_a_5307_);
lean_dec_ref(v___x_5306_);
v___x_5308_ = lean_unsigned_to_nat(1u);
v___x_5309_ = lean_mk_empty_array_with_capacity(v___x_5308_);
lean_inc_ref(v___x_5309_);
v___x_5310_ = lean_array_push(v___x_5309_, v_declName_5293_);
lean_inc(v_a_5299_);
lean_inc_ref(v_a_5298_);
lean_inc(v_a_5297_);
lean_inc_ref(v_a_5296_);
v___x_5311_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_5305_, v___x_5301_, v___x_5310_, v___x_5303_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
lean_dec_ref(v___x_5310_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v_a_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v_a_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5348_; 
v_a_5312_ = lean_ctor_get(v___x_5311_, 0);
lean_inc(v_a_5312_);
lean_dec_ref(v___x_5311_);
v___x_5313_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__1));
v___x_5314_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__0___redArg(v___x_5313_, v_a_5298_);
v_a_5315_ = lean_ctor_get(v___x_5314_, 0);
v_isSharedCheck_5348_ = !lean_is_exclusive(v___x_5314_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5317_ = v___x_5314_;
v_isShared_5318_ = v_isSharedCheck_5348_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_a_5315_);
lean_dec(v___x_5314_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5348_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v___x_5319_; lean_object* v___x_5320_; uint8_t v___x_5321_; 
v___x_5319_ = lean_array_push(v___x_5309_, v_a_5307_);
v___x_5320_ = l_Array_append___redArg(v___x_5319_, v_a_5312_);
lean_dec(v_a_5312_);
v___x_5321_ = lean_unbox(v_a_5315_);
lean_dec(v_a_5315_);
if (v___x_5321_ == 0)
{
lean_object* v___x_5323_; 
lean_dec(v_a_5299_);
lean_dec_ref(v_a_5298_);
lean_dec(v_a_5297_);
lean_dec_ref(v_a_5296_);
if (v_isShared_5318_ == 0)
{
lean_ctor_set(v___x_5317_, 0, v___x_5320_);
v___x_5323_ = v___x_5317_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v___x_5320_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
else
{
lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; 
lean_del_object(v___x_5317_);
v___x_5325_ = lean_obj_once(&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2, &l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2_once, _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__2);
lean_inc_ref(v___x_5320_);
v___x_5326_ = lean_array_to_list(v___x_5320_);
v___x_5327_ = lean_box(0);
v___x_5328_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__1(v___x_5326_, v___x_5327_);
v___x_5329_ = l_Lean_MessageData_ofList(v___x_5328_);
v___x_5330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5330_, 0, v___x_5325_);
lean_ctor_set(v___x_5330_, 1, v___x_5329_);
v___x_5331_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance_spec__2___redArg(v___x_5313_, v___x_5330_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
lean_dec(v_a_5299_);
lean_dec_ref(v_a_5298_);
lean_dec(v_a_5297_);
lean_dec_ref(v_a_5296_);
if (lean_obj_tag(v___x_5331_) == 0)
{
lean_object* v___x_5333_; uint8_t v_isShared_5334_; uint8_t v_isSharedCheck_5338_; 
v_isSharedCheck_5338_ = !lean_is_exclusive(v___x_5331_);
if (v_isSharedCheck_5338_ == 0)
{
lean_object* v_unused_5339_; 
v_unused_5339_ = lean_ctor_get(v___x_5331_, 0);
lean_dec(v_unused_5339_);
v___x_5333_ = v___x_5331_;
v_isShared_5334_ = v_isSharedCheck_5338_;
goto v_resetjp_5332_;
}
else
{
lean_dec(v___x_5331_);
v___x_5333_ = lean_box(0);
v_isShared_5334_ = v_isSharedCheck_5338_;
goto v_resetjp_5332_;
}
v_resetjp_5332_:
{
lean_object* v___x_5336_; 
if (v_isShared_5334_ == 0)
{
lean_ctor_set(v___x_5333_, 0, v___x_5320_);
v___x_5336_ = v___x_5333_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5337_; 
v_reuseFailAlloc_5337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5337_, 0, v___x_5320_);
v___x_5336_ = v_reuseFailAlloc_5337_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
return v___x_5336_;
}
}
}
else
{
lean_object* v_a_5340_; lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5347_; 
lean_dec_ref(v___x_5320_);
v_a_5340_ = lean_ctor_get(v___x_5331_, 0);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5331_);
if (v_isSharedCheck_5347_ == 0)
{
v___x_5342_ = v___x_5331_;
v_isShared_5343_ = v_isSharedCheck_5347_;
goto v_resetjp_5341_;
}
else
{
lean_inc(v_a_5340_);
lean_dec(v___x_5331_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5347_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
lean_object* v___x_5345_; 
if (v_isShared_5343_ == 0)
{
v___x_5345_ = v___x_5342_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5340_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_5309_);
lean_dec(v_a_5307_);
lean_dec(v_a_5299_);
lean_dec_ref(v_a_5298_);
lean_dec(v_a_5297_);
lean_dec_ref(v_a_5296_);
return v___x_5311_;
}
}
else
{
lean_object* v_a_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5356_; 
lean_dec(v_a_5305_);
lean_dec(v_a_5299_);
lean_dec_ref(v_a_5298_);
lean_dec(v_a_5297_);
lean_dec_ref(v_a_5296_);
lean_dec(v_a_5295_);
lean_dec_ref(v_a_5294_);
lean_dec(v_declName_5293_);
v_a_5349_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5351_ = v___x_5306_;
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5306_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
lean_object* v___x_5354_; 
if (v_isShared_5352_ == 0)
{
v___x_5354_ = v___x_5351_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
}
else
{
lean_object* v_a_5357_; lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5364_; 
lean_dec(v_a_5299_);
lean_dec_ref(v_a_5298_);
lean_dec(v_a_5297_);
lean_dec_ref(v_a_5296_);
lean_dec(v_a_5295_);
lean_dec_ref(v_a_5294_);
lean_dec(v_declName_5293_);
v_a_5357_ = lean_ctor_get(v___x_5304_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5359_ = v___x_5304_;
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
else
{
lean_inc(v_a_5357_);
lean_dec(v___x_5304_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v___x_5362_; 
if (v_isShared_5360_ == 0)
{
v___x_5362_ = v___x_5359_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5357_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___boxed(lean_object* v_declName_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_){
_start:
{
lean_object* v_res_5373_; 
v_res_5373_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance(v_declName_5365_, v_a_5366_, v_a_5367_, v_a_5368_, v_a_5369_, v_a_5370_, v_a_5371_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___redArg(lean_object* v_declName_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v___x_5377_; lean_object* v_env_5378_; uint8_t v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; 
v___x_5377_ = lean_st_ref_get(v___y_5375_);
v_env_5378_ = lean_ctor_get(v___x_5377_, 0);
lean_inc_ref(v_env_5378_);
lean_dec(v___x_5377_);
v___x_5379_ = l_Lean_isInductiveCore(v_env_5378_, v_declName_5374_);
v___x_5380_ = lean_box(v___x_5379_);
v___x_5381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5381_, 0, v___x_5380_);
return v___x_5381_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_){
_start:
{
lean_object* v_res_5385_; 
v_res_5385_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___redArg(v_declName_5382_, v___y_5383_);
lean_dec(v___y_5383_);
return v_res_5385_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0(lean_object* v_declName_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_){
_start:
{
lean_object* v___x_5390_; 
v___x_5390_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___redArg(v_declName_5386_, v___y_5388_);
return v___x_5390_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___boxed(lean_object* v_declName_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_){
_start:
{
lean_object* v_res_5395_; 
v_res_5395_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0(v_declName_5391_, v___y_5392_, v___y_5393_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(uint8_t v_____do__lift_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_){
_start:
{
if (v_____do__lift_5396_ == 0)
{
uint8_t v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5400_ = 1;
v___x_5401_ = lean_box(v___x_5400_);
v___x_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5401_);
return v___x_5402_;
}
else
{
uint8_t v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; 
v___x_5403_ = 0;
v___x_5404_ = lean_box(v___x_5403_);
v___x_5405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5405_, 0, v___x_5404_);
return v___x_5405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_){
_start:
{
uint8_t v_____do__lift_2982__boxed_5410_; lean_object* v_res_5411_; 
v_____do__lift_2982__boxed_5410_ = lean_unbox(v_____do__lift_5406_);
v_res_5411_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(v_____do__lift_2982__boxed_5410_, v___y_5407_, v___y_5408_);
lean_dec(v___y_5408_);
lean_dec_ref(v___y_5407_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__3(lean_object* v_as_5412_, size_t v_i_5413_, size_t v_stop_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_){
_start:
{
uint8_t v___x_5418_; 
v___x_5418_ = lean_usize_dec_eq(v_i_5413_, v_stop_5414_);
if (v___x_5418_ == 0)
{
uint8_t v___x_5419_; uint8_t v_a_5421_; lean_object* v___x_5427_; lean_object* v___x_5428_; 
v___x_5419_ = 1;
v___x_5427_ = lean_array_uget_borrowed(v_as_5412_, v_i_5413_);
lean_inc(v___x_5427_);
v___x_5428_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__0___redArg(v___x_5427_, v___y_5416_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5438_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5438_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5438_ == 0)
{
v___x_5431_ = v___x_5428_;
v_isShared_5432_ = v_isSharedCheck_5438_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5428_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5438_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
uint8_t v___x_5433_; 
v___x_5433_ = lean_unbox(v_a_5429_);
lean_dec(v_a_5429_);
if (v___x_5433_ == 0)
{
lean_object* v___x_5434_; lean_object* v___x_5436_; 
v___x_5434_ = lean_box(v___x_5419_);
if (v_isShared_5432_ == 0)
{
lean_ctor_set(v___x_5431_, 0, v___x_5434_);
v___x_5436_ = v___x_5431_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___x_5434_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
return v___x_5436_;
}
}
else
{
lean_del_object(v___x_5431_);
v_a_5421_ = v___x_5418_;
goto v___jp_5420_;
}
}
}
else
{
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5439_; uint8_t v___x_5440_; 
v_a_5439_ = lean_ctor_get(v___x_5428_, 0);
lean_inc(v_a_5439_);
lean_dec_ref(v___x_5428_);
v___x_5440_ = lean_unbox(v_a_5439_);
lean_dec(v_a_5439_);
v_a_5421_ = v___x_5440_;
goto v___jp_5420_;
}
else
{
return v___x_5428_;
}
}
v___jp_5420_:
{
if (v_a_5421_ == 0)
{
size_t v___x_5422_; size_t v___x_5423_; 
v___x_5422_ = ((size_t)1ULL);
v___x_5423_ = lean_usize_add(v_i_5413_, v___x_5422_);
v_i_5413_ = v___x_5423_;
goto _start;
}
else
{
lean_object* v___x_5425_; lean_object* v___x_5426_; 
v___x_5425_ = lean_box(v___x_5419_);
v___x_5426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5426_, 0, v___x_5425_);
return v___x_5426_;
}
}
}
else
{
uint8_t v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5441_ = 0;
v___x_5442_ = lean_box(v___x_5441_);
v___x_5443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5443_, 0, v___x_5442_);
return v___x_5443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__3___boxed(lean_object* v_as_5444_, lean_object* v_i_5445_, lean_object* v_stop_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_){
_start:
{
size_t v_i_boxed_5450_; size_t v_stop_boxed_5451_; lean_object* v_res_5452_; 
v_i_boxed_5450_ = lean_unbox_usize(v_i_5445_);
lean_dec(v_i_5445_);
v_stop_boxed_5451_ = lean_unbox_usize(v_stop_5446_);
lean_dec(v_stop_5446_);
v_res_5452_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__3(v_as_5444_, v_i_boxed_5450_, v_stop_boxed_5451_, v___y_5447_, v___y_5448_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec_ref(v_as_5444_);
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(lean_object* v_as_5453_, size_t v_i_5454_, size_t v_stop_5455_, lean_object* v_b_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_){
_start:
{
uint8_t v___x_5460_; 
v___x_5460_ = lean_usize_dec_eq(v_i_5454_, v_stop_5455_);
if (v___x_5460_ == 0)
{
lean_object* v___x_5461_; lean_object* v___x_5462_; 
v___x_5461_ = lean_array_uget_borrowed(v_as_5453_, v_i_5454_);
lean_inc(v___y_5458_);
lean_inc_ref(v___y_5457_);
lean_inc(v___x_5461_);
v___x_5462_ = l_Lean_Elab_Command_elabCommand(v___x_5461_, v___y_5457_, v___y_5458_);
if (lean_obj_tag(v___x_5462_) == 0)
{
lean_object* v_a_5463_; size_t v___x_5464_; size_t v___x_5465_; 
v_a_5463_ = lean_ctor_get(v___x_5462_, 0);
lean_inc(v_a_5463_);
lean_dec_ref(v___x_5462_);
v___x_5464_ = ((size_t)1ULL);
v___x_5465_ = lean_usize_add(v_i_5454_, v___x_5464_);
v_i_5454_ = v___x_5465_;
v_b_5456_ = v_a_5463_;
goto _start;
}
else
{
lean_dec(v___y_5458_);
lean_dec_ref(v___y_5457_);
return v___x_5462_;
}
}
else
{
lean_object* v___x_5467_; 
lean_dec(v___y_5458_);
lean_dec_ref(v___y_5457_);
v___x_5467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5467_, 0, v_b_5456_);
return v___x_5467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1___boxed(lean_object* v_as_5468_, lean_object* v_i_5469_, lean_object* v_stop_5470_, lean_object* v_b_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_){
_start:
{
size_t v_i_boxed_5475_; size_t v_stop_boxed_5476_; lean_object* v_res_5477_; 
v_i_boxed_5475_ = lean_unbox_usize(v_i_5469_);
lean_dec(v_i_5469_);
v_stop_boxed_5476_ = lean_unbox_usize(v_stop_5470_);
lean_dec(v_stop_5470_);
v_res_5477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(v_as_5468_, v_i_boxed_5475_, v_stop_boxed_5476_, v_b_5471_, v___y_5472_, v___y_5473_);
lean_dec_ref(v_as_5468_);
return v_res_5477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__2(lean_object* v_as_5478_, size_t v_sz_5479_, size_t v_i_5480_, lean_object* v_b_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_){
_start:
{
lean_object* v_a_5486_; uint8_t v___x_5490_; 
v___x_5490_ = lean_usize_dec_lt(v_i_5480_, v_sz_5479_);
if (v___x_5490_ == 0)
{
lean_object* v___x_5491_; 
lean_dec(v___y_5483_);
lean_dec_ref(v___y_5482_);
v___x_5491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5491_, 0, v_b_5481_);
return v___x_5491_;
}
else
{
lean_object* v_a_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; 
v_a_5492_ = lean_array_uget_borrowed(v_as_5478_, v_i_5480_);
lean_inc(v_a_5492_);
v___x_5493_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___boxed), 8, 1);
lean_closure_set(v___x_5493_, 0, v_a_5492_);
lean_inc_ref(v___y_5482_);
v___x_5494_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_5493_, v___y_5482_, v___y_5483_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v_a_5495_; lean_object* v___x_5496_; lean_object* v___y_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; uint8_t v___x_5501_; 
v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
lean_inc(v_a_5495_);
lean_dec_ref(v___x_5494_);
v___x_5496_ = lean_box(0);
v___x_5499_ = lean_unsigned_to_nat(0u);
v___x_5500_ = lean_array_get_size(v_a_5495_);
v___x_5501_ = lean_nat_dec_lt(v___x_5499_, v___x_5500_);
if (v___x_5501_ == 0)
{
lean_dec(v_a_5495_);
v_a_5486_ = v___x_5496_;
goto v___jp_5485_;
}
else
{
uint8_t v___x_5502_; 
v___x_5502_ = lean_nat_dec_le(v___x_5500_, v___x_5500_);
if (v___x_5502_ == 0)
{
if (v___x_5501_ == 0)
{
lean_dec(v_a_5495_);
v_a_5486_ = v___x_5496_;
goto v___jp_5485_;
}
else
{
size_t v___x_5503_; size_t v___x_5504_; lean_object* v___x_5505_; 
v___x_5503_ = ((size_t)0ULL);
v___x_5504_ = lean_usize_of_nat(v___x_5500_);
lean_inc(v___y_5483_);
lean_inc_ref(v___y_5482_);
v___x_5505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(v_a_5495_, v___x_5503_, v___x_5504_, v___x_5496_, v___y_5482_, v___y_5483_);
lean_dec(v_a_5495_);
v___y_5498_ = v___x_5505_;
goto v___jp_5497_;
}
}
else
{
size_t v___x_5506_; size_t v___x_5507_; lean_object* v___x_5508_; 
v___x_5506_ = ((size_t)0ULL);
v___x_5507_ = lean_usize_of_nat(v___x_5500_);
lean_inc(v___y_5483_);
lean_inc_ref(v___y_5482_);
v___x_5508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(v_a_5495_, v___x_5506_, v___x_5507_, v___x_5496_, v___y_5482_, v___y_5483_);
lean_dec(v_a_5495_);
v___y_5498_ = v___x_5508_;
goto v___jp_5497_;
}
}
v___jp_5497_:
{
if (lean_obj_tag(v___y_5498_) == 0)
{
lean_dec_ref(v___y_5498_);
v_a_5486_ = v___x_5496_;
goto v___jp_5485_;
}
else
{
lean_dec(v___y_5483_);
lean_dec_ref(v___y_5482_);
return v___y_5498_;
}
}
}
else
{
lean_object* v_a_5509_; lean_object* v___x_5511_; uint8_t v_isShared_5512_; uint8_t v_isSharedCheck_5516_; 
lean_dec(v___y_5483_);
lean_dec_ref(v___y_5482_);
v_a_5509_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5516_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5516_ == 0)
{
v___x_5511_ = v___x_5494_;
v_isShared_5512_ = v_isSharedCheck_5516_;
goto v_resetjp_5510_;
}
else
{
lean_inc(v_a_5509_);
lean_dec(v___x_5494_);
v___x_5511_ = lean_box(0);
v_isShared_5512_ = v_isSharedCheck_5516_;
goto v_resetjp_5510_;
}
v_resetjp_5510_:
{
lean_object* v___x_5514_; 
if (v_isShared_5512_ == 0)
{
v___x_5514_ = v___x_5511_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_a_5509_);
v___x_5514_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
return v___x_5514_;
}
}
}
}
v___jp_5485_:
{
size_t v___x_5487_; size_t v___x_5488_; 
v___x_5487_ = ((size_t)1ULL);
v___x_5488_ = lean_usize_add(v_i_5480_, v___x_5487_);
v_i_5480_ = v___x_5488_;
v_b_5481_ = v_a_5486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__2___boxed(lean_object* v_as_5517_, lean_object* v_sz_5518_, lean_object* v_i_5519_, lean_object* v_b_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_){
_start:
{
size_t v_sz_boxed_5524_; size_t v_i_boxed_5525_; lean_object* v_res_5526_; 
v_sz_boxed_5524_ = lean_unbox_usize(v_sz_5518_);
lean_dec(v_sz_5518_);
v_i_boxed_5525_ = lean_unbox_usize(v_i_5519_);
lean_dec(v_i_5519_);
v_res_5526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__2(v_as_5517_, v_sz_boxed_5524_, v_i_boxed_5525_, v_b_5520_, v___y_5521_, v___y_5522_);
lean_dec_ref(v_as_5517_);
return v_res_5526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler(lean_object* v_declNames_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_){
_start:
{
lean_object* v___x_5531_; lean_object* v___x_5532_; uint8_t v___x_5533_; uint8_t v_a_5535_; lean_object* v___y_5560_; 
v___x_5531_ = lean_unsigned_to_nat(0u);
v___x_5532_ = lean_array_get_size(v_declNames_5527_);
v___x_5533_ = lean_nat_dec_lt(v___x_5531_, v___x_5532_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5564_; 
v___x_5564_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(v___x_5533_, v_a_5528_, v_a_5529_);
v___y_5560_ = v___x_5564_;
goto v___jp_5559_;
}
else
{
if (v___x_5533_ == 0)
{
v_a_5535_ = v___x_5533_;
goto v___jp_5534_;
}
else
{
size_t v___x_5565_; size_t v___x_5566_; lean_object* v___x_5567_; 
v___x_5565_ = ((size_t)0ULL);
v___x_5566_ = lean_usize_of_nat(v___x_5532_);
v___x_5567_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__3(v_declNames_5527_, v___x_5565_, v___x_5566_, v_a_5528_, v_a_5529_);
if (lean_obj_tag(v___x_5567_) == 0)
{
lean_object* v_a_5568_; uint8_t v___x_5569_; lean_object* v___x_5570_; 
v_a_5568_ = lean_ctor_get(v___x_5567_, 0);
lean_inc(v_a_5568_);
lean_dec_ref(v___x_5567_);
v___x_5569_ = lean_unbox(v_a_5568_);
lean_dec(v_a_5568_);
v___x_5570_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(v___x_5569_, v_a_5528_, v_a_5529_);
v___y_5560_ = v___x_5570_;
goto v___jp_5559_;
}
else
{
v___y_5560_ = v___x_5567_;
goto v___jp_5559_;
}
}
}
v___jp_5534_:
{
if (v___x_5533_ == 0)
{
lean_object* v___x_5536_; lean_object* v___x_5537_; 
lean_dec(v_a_5529_);
lean_dec_ref(v_a_5528_);
v___x_5536_ = lean_box(v___x_5533_);
v___x_5537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5537_, 0, v___x_5536_);
return v___x_5537_;
}
else
{
lean_object* v___x_5538_; size_t v_sz_5539_; size_t v___x_5540_; lean_object* v___x_5541_; 
v___x_5538_ = lean_box(0);
v_sz_5539_ = lean_array_size(v_declNames_5527_);
v___x_5540_ = ((size_t)0ULL);
v___x_5541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__2(v_declNames_5527_, v_sz_5539_, v___x_5540_, v___x_5538_, v_a_5528_, v_a_5529_);
if (lean_obj_tag(v___x_5541_) == 0)
{
lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5549_; 
v_isSharedCheck_5549_ = !lean_is_exclusive(v___x_5541_);
if (v_isSharedCheck_5549_ == 0)
{
lean_object* v_unused_5550_; 
v_unused_5550_ = lean_ctor_get(v___x_5541_, 0);
lean_dec(v_unused_5550_);
v___x_5543_ = v___x_5541_;
v_isShared_5544_ = v_isSharedCheck_5549_;
goto v_resetjp_5542_;
}
else
{
lean_dec(v___x_5541_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5549_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5545_; lean_object* v___x_5547_; 
v___x_5545_ = lean_box(v_a_5535_);
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 0, v___x_5545_);
v___x_5547_ = v___x_5543_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v___x_5545_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
}
}
}
else
{
lean_object* v_a_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5558_; 
v_a_5551_ = lean_ctor_get(v___x_5541_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5541_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5553_ = v___x_5541_;
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_a_5551_);
lean_dec(v___x_5541_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5556_; 
if (v_isShared_5554_ == 0)
{
v___x_5556_ = v___x_5553_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_a_5551_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
}
v___jp_5559_:
{
if (lean_obj_tag(v___y_5560_) == 0)
{
lean_object* v_a_5561_; uint8_t v___x_5562_; 
v_a_5561_ = lean_ctor_get(v___y_5560_, 0);
v___x_5562_ = lean_unbox(v_a_5561_);
if (v___x_5562_ == 0)
{
lean_dec(v_a_5529_);
lean_dec_ref(v_a_5528_);
return v___y_5560_;
}
else
{
uint8_t v___x_5563_; 
lean_inc(v_a_5561_);
lean_dec_ref(v___y_5560_);
v___x_5563_ = lean_unbox(v_a_5561_);
lean_dec(v_a_5561_);
v_a_5535_ = v___x_5563_;
goto v___jp_5534_;
}
}
else
{
lean_dec(v_a_5529_);
lean_dec_ref(v_a_5528_);
return v___y_5560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___boxed(lean_object* v_declNames_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_){
_start:
{
lean_object* v_res_5575_; 
v_res_5575_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler(v_declNames_5571_, v_a_5572_, v_a_5573_);
lean_dec_ref(v_declNames_5571_);
return v_res_5575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler_spec__0(lean_object* v_as_5576_, size_t v_sz_5577_, size_t v_i_5578_, lean_object* v_b_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_){
_start:
{
lean_object* v_a_5584_; uint8_t v___x_5588_; 
v___x_5588_ = lean_usize_dec_lt(v_i_5578_, v_sz_5577_);
if (v___x_5588_ == 0)
{
lean_object* v___x_5589_; 
lean_dec(v___y_5581_);
lean_dec_ref(v___y_5580_);
v___x_5589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5589_, 0, v_b_5579_);
return v___x_5589_;
}
else
{
lean_object* v_a_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; 
v_a_5590_ = lean_array_uget_borrowed(v_as_5576_, v_i_5578_);
lean_inc(v_a_5590_);
v___x_5591_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___boxed), 8, 1);
lean_closure_set(v___x_5591_, 0, v_a_5590_);
lean_inc_ref(v___y_5580_);
v___x_5592_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_5591_, v___y_5580_, v___y_5581_);
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_object* v_a_5593_; lean_object* v___x_5594_; lean_object* v___y_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; uint8_t v___x_5599_; 
v_a_5593_ = lean_ctor_get(v___x_5592_, 0);
lean_inc(v_a_5593_);
lean_dec_ref(v___x_5592_);
v___x_5594_ = lean_box(0);
v___x_5597_ = lean_unsigned_to_nat(0u);
v___x_5598_ = lean_array_get_size(v_a_5593_);
v___x_5599_ = lean_nat_dec_lt(v___x_5597_, v___x_5598_);
if (v___x_5599_ == 0)
{
lean_dec(v_a_5593_);
v_a_5584_ = v___x_5594_;
goto v___jp_5583_;
}
else
{
uint8_t v___x_5600_; 
v___x_5600_ = lean_nat_dec_le(v___x_5598_, v___x_5598_);
if (v___x_5600_ == 0)
{
if (v___x_5599_ == 0)
{
lean_dec(v_a_5593_);
v_a_5584_ = v___x_5594_;
goto v___jp_5583_;
}
else
{
size_t v___x_5601_; size_t v___x_5602_; lean_object* v___x_5603_; 
v___x_5601_ = ((size_t)0ULL);
v___x_5602_ = lean_usize_of_nat(v___x_5598_);
lean_inc(v___y_5581_);
lean_inc_ref(v___y_5580_);
v___x_5603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(v_a_5593_, v___x_5601_, v___x_5602_, v___x_5594_, v___y_5580_, v___y_5581_);
lean_dec(v_a_5593_);
v___y_5596_ = v___x_5603_;
goto v___jp_5595_;
}
}
else
{
size_t v___x_5604_; size_t v___x_5605_; lean_object* v___x_5606_; 
v___x_5604_ = ((size_t)0ULL);
v___x_5605_ = lean_usize_of_nat(v___x_5598_);
lean_inc(v___y_5581_);
lean_inc_ref(v___y_5580_);
v___x_5606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__1(v_a_5593_, v___x_5604_, v___x_5605_, v___x_5594_, v___y_5580_, v___y_5581_);
lean_dec(v_a_5593_);
v___y_5596_ = v___x_5606_;
goto v___jp_5595_;
}
}
v___jp_5595_:
{
if (lean_obj_tag(v___y_5596_) == 0)
{
lean_dec_ref(v___y_5596_);
v_a_5584_ = v___x_5594_;
goto v___jp_5583_;
}
else
{
lean_dec(v___y_5581_);
lean_dec_ref(v___y_5580_);
return v___y_5596_;
}
}
}
else
{
lean_object* v_a_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5614_; 
lean_dec(v___y_5581_);
lean_dec_ref(v___y_5580_);
v_a_5607_ = lean_ctor_get(v___x_5592_, 0);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5614_ == 0)
{
v___x_5609_ = v___x_5592_;
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_a_5607_);
lean_dec(v___x_5592_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5612_; 
if (v_isShared_5610_ == 0)
{
v___x_5612_ = v___x_5609_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_a_5607_);
v___x_5612_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
return v___x_5612_;
}
}
}
}
v___jp_5583_:
{
size_t v___x_5585_; size_t v___x_5586_; 
v___x_5585_ = ((size_t)1ULL);
v___x_5586_ = lean_usize_add(v_i_5578_, v___x_5585_);
v_i_5578_ = v___x_5586_;
v_b_5579_ = v_a_5584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler_spec__0___boxed(lean_object* v_as_5615_, lean_object* v_sz_5616_, lean_object* v_i_5617_, lean_object* v_b_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_){
_start:
{
size_t v_sz_boxed_5622_; size_t v_i_boxed_5623_; lean_object* v_res_5624_; 
v_sz_boxed_5622_ = lean_unbox_usize(v_sz_5616_);
lean_dec(v_sz_5616_);
v_i_boxed_5623_ = lean_unbox_usize(v_i_5617_);
lean_dec(v_i_5617_);
v_res_5624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler_spec__0(v_as_5615_, v_sz_boxed_5622_, v_i_boxed_5623_, v_b_5618_, v___y_5619_, v___y_5620_);
lean_dec_ref(v_as_5615_);
return v_res_5624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler(lean_object* v_declNames_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_){
_start:
{
lean_object* v___x_5629_; lean_object* v___x_5630_; uint8_t v___x_5631_; uint8_t v_a_5633_; lean_object* v___y_5658_; 
v___x_5629_ = lean_unsigned_to_nat(0u);
v___x_5630_ = lean_array_get_size(v_declNames_5625_);
v___x_5631_ = lean_nat_dec_lt(v___x_5629_, v___x_5630_);
if (v___x_5631_ == 0)
{
lean_object* v___x_5662_; 
v___x_5662_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(v___x_5631_, v_a_5626_, v_a_5627_);
v___y_5658_ = v___x_5662_;
goto v___jp_5657_;
}
else
{
if (v___x_5631_ == 0)
{
v_a_5633_ = v___x_5631_;
goto v___jp_5632_;
}
else
{
size_t v___x_5663_; size_t v___x_5664_; lean_object* v___x_5665_; 
v___x_5663_ = ((size_t)0ULL);
v___x_5664_ = lean_usize_of_nat(v___x_5630_);
v___x_5665_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler_spec__3(v_declNames_5625_, v___x_5663_, v___x_5664_, v_a_5626_, v_a_5627_);
if (lean_obj_tag(v___x_5665_) == 0)
{
lean_object* v_a_5666_; uint8_t v___x_5667_; lean_object* v___x_5668_; 
v_a_5666_ = lean_ctor_get(v___x_5665_, 0);
lean_inc(v_a_5666_);
lean_dec_ref(v___x_5665_);
v___x_5667_ = lean_unbox(v_a_5666_);
lean_dec(v_a_5666_);
v___x_5668_ = l_Lean_Elab_Deriving_FromToJson_mkToJsonInstanceHandler___lam__0(v___x_5667_, v_a_5626_, v_a_5627_);
v___y_5658_ = v___x_5668_;
goto v___jp_5657_;
}
else
{
v___y_5658_ = v___x_5665_;
goto v___jp_5657_;
}
}
}
v___jp_5632_:
{
if (v___x_5631_ == 0)
{
lean_object* v___x_5634_; lean_object* v___x_5635_; 
lean_dec(v_a_5627_);
lean_dec_ref(v_a_5626_);
v___x_5634_ = lean_box(v___x_5631_);
v___x_5635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5635_, 0, v___x_5634_);
return v___x_5635_;
}
else
{
lean_object* v___x_5636_; size_t v_sz_5637_; size_t v___x_5638_; lean_object* v___x_5639_; 
v___x_5636_ = lean_box(0);
v_sz_5637_ = lean_array_size(v_declNames_5625_);
v___x_5638_ = ((size_t)0ULL);
v___x_5639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler_spec__0(v_declNames_5625_, v_sz_5637_, v___x_5638_, v___x_5636_, v_a_5626_, v_a_5627_);
if (lean_obj_tag(v___x_5639_) == 0)
{
lean_object* v___x_5641_; uint8_t v_isShared_5642_; uint8_t v_isSharedCheck_5647_; 
v_isSharedCheck_5647_ = !lean_is_exclusive(v___x_5639_);
if (v_isSharedCheck_5647_ == 0)
{
lean_object* v_unused_5648_; 
v_unused_5648_ = lean_ctor_get(v___x_5639_, 0);
lean_dec(v_unused_5648_);
v___x_5641_ = v___x_5639_;
v_isShared_5642_ = v_isSharedCheck_5647_;
goto v_resetjp_5640_;
}
else
{
lean_dec(v___x_5639_);
v___x_5641_ = lean_box(0);
v_isShared_5642_ = v_isSharedCheck_5647_;
goto v_resetjp_5640_;
}
v_resetjp_5640_:
{
lean_object* v___x_5643_; lean_object* v___x_5645_; 
v___x_5643_ = lean_box(v_a_5633_);
if (v_isShared_5642_ == 0)
{
lean_ctor_set(v___x_5641_, 0, v___x_5643_);
v___x_5645_ = v___x_5641_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v___x_5643_);
v___x_5645_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
return v___x_5645_;
}
}
}
else
{
lean_object* v_a_5649_; lean_object* v___x_5651_; uint8_t v_isShared_5652_; uint8_t v_isSharedCheck_5656_; 
v_a_5649_ = lean_ctor_get(v___x_5639_, 0);
v_isSharedCheck_5656_ = !lean_is_exclusive(v___x_5639_);
if (v_isSharedCheck_5656_ == 0)
{
v___x_5651_ = v___x_5639_;
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
else
{
lean_inc(v_a_5649_);
lean_dec(v___x_5639_);
v___x_5651_ = lean_box(0);
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
v_resetjp_5650_:
{
lean_object* v___x_5654_; 
if (v_isShared_5652_ == 0)
{
v___x_5654_ = v___x_5651_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_a_5649_);
v___x_5654_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
return v___x_5654_;
}
}
}
}
}
v___jp_5657_:
{
if (lean_obj_tag(v___y_5658_) == 0)
{
lean_object* v_a_5659_; uint8_t v___x_5660_; 
v_a_5659_ = lean_ctor_get(v___y_5658_, 0);
v___x_5660_ = lean_unbox(v_a_5659_);
if (v___x_5660_ == 0)
{
lean_dec(v_a_5627_);
lean_dec_ref(v_a_5626_);
return v___y_5658_;
}
else
{
uint8_t v___x_5661_; 
lean_inc(v_a_5659_);
lean_dec_ref(v___y_5658_);
v___x_5661_ = lean_unbox(v_a_5659_);
lean_dec(v_a_5659_);
v_a_5633_ = v___x_5661_;
goto v___jp_5632_;
}
}
else
{
lean_dec(v_a_5627_);
lean_dec_ref(v_a_5626_);
return v___y_5658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler___boxed(lean_object* v_declNames_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_){
_start:
{
lean_object* v_res_5673_; 
v_res_5673_ = l_Lean_Elab_Deriving_FromToJson_mkFromJsonInstanceHandler(v_declNames_5669_, v_a_5670_, v_a_5671_);
lean_dec_ref(v_declNames_5669_);
return v_res_5673_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__21_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; 
v___x_5727_ = lean_unsigned_to_nat(2304768170u);
v___x_5728_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__20_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_));
v___x_5729_ = l_Lean_Name_num___override(v___x_5728_, v___x_5727_);
return v___x_5729_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__23_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; 
v___x_5731_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__22_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_));
v___x_5732_ = lean_obj_once(&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__21_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__21_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__21_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_);
v___x_5733_ = l_Lean_Name_str___override(v___x_5732_, v___x_5731_);
return v___x_5733_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__25_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; 
v___x_5735_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__24_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_));
v___x_5736_ = lean_obj_once(&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__23_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__23_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__23_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_);
v___x_5737_ = l_Lean_Name_str___override(v___x_5736_, v___x_5735_);
return v___x_5737_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__26_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; 
v___x_5738_ = lean_unsigned_to_nat(2u);
v___x_5739_ = lean_obj_once(&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__25_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__25_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__25_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_);
v___x_5740_ = l_Lean_Name_num___override(v___x_5739_, v___x_5738_);
return v___x_5740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; 
v___x_5742_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkToJsonHeader___closed__2));
v___x_5743_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__0_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_));
v___x_5744_ = l_Lean_Elab_registerDerivingHandler(v___x_5742_, v___x_5743_);
if (lean_obj_tag(v___x_5744_) == 0)
{
lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; 
lean_dec_ref(v___x_5744_);
v___x_5745_ = ((lean_object*)(l_Lean_Elab_Deriving_FromToJson_mkFromJsonHeader___closed__1));
v___x_5746_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__1_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_));
v___x_5747_ = l_Lean_Elab_registerDerivingHandler(v___x_5745_, v___x_5746_);
if (lean_obj_tag(v___x_5747_) == 0)
{
lean_object* v___x_5748_; uint8_t v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; 
lean_dec_ref(v___x_5747_);
v___x_5748_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkToJsonInstance___closed__0));
v___x_5749_ = 0;
v___x_5750_ = lean_obj_once(&l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__26_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_, &l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__26_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn___closed__26_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_);
v___x_5751_ = l_Lean_registerTraceClass(v___x_5748_, v___x_5749_, v___x_5750_);
if (lean_obj_tag(v___x_5751_) == 0)
{
lean_object* v___x_5752_; lean_object* v___x_5753_; 
lean_dec_ref(v___x_5751_);
v___x_5752_ = ((lean_object*)(l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_mkFromJsonInstance___closed__1));
v___x_5753_ = l_Lean_registerTraceClass(v___x_5752_, v___x_5749_, v___x_5750_);
return v___x_5753_;
}
else
{
return v___x_5751_;
}
}
else
{
return v___x_5747_;
}
}
else
{
return v___x_5744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2____boxed(lean_object* v_a_5754_){
_start:
{
lean_object* v_res_5755_; 
v_res_5755_ = l___private_Lean_Elab_Deriving_FromToJson_0__Lean_Elab_Deriving_FromToJson_initFn_00___x40_Lean_Elab_Deriving_FromToJson_2304768170____hygCtx___hyg_2_();
return v_res_5755_;
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
