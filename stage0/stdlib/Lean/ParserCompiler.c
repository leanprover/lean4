// Lean compiler output
// Module: Lean.ParserCompiler
// Imports: public import Lean.Meta.ReduceEval public import Lean.Meta.WHNF public import Lean.KeyedDeclsAttribute public import Lean.ParserCompiler.Attribute public import Lean.Parser.Extension import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*, uint8_t);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(114, 164, 180, 82, 232, 106, 164, 24)}};
static const lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leadingNode"};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__0_value;
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(226, 41, 145, 230, 168, 227, 241, 30)}};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value;
static const lean_string_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "trailingNode"};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__2 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__2_value;
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(11, 103, 4, 79, 164, 122, 74, 107)}};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value;
static const lean_string_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "node"};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__4 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__4_value;
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(172, 125, 54, 68, 103, 5, 171, 140)}};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value;
static const lean_string_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withAntiquot"};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__6 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__6_value;
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(2, 88, 47, 17, 27, 77, 70, 127)}};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value;
static const lean_array_object l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__24;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__25 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__25_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__26;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__1 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__1_value;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__3 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__3_value;
static const lean_ctor_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__4 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__4_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "refusing to generate code for imported parser declaration `"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "`; use `@[run_parser_attribute_hooks]` on its definition instead."};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "don't know how to generate "};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = " for non-definition `"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "TrailingParser"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19_value;
static const lean_ctor_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 139, 135, 36, 12, 238, 116)}};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " for non-parser combinator `"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "call of unknown parser at `"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__23 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__23_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__24;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1;
static const lean_array_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3;
static lean_once_cell_t l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4;
static lean_once_cell_t l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5;
static lean_once_cell_t l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6;
static lean_once_cell_t l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7;
static const lean_string_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ParserDescr"};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(92, 191, 134, 190, 206, 60, 55, 123)}};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value;
static const lean_string_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "TrailingParserDescr"};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__10 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(73, 30, 7, 95, 84, 115, 124, 250)}};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName___redArg(lean_object* v_ctx_1_){
_start:
{
lean_object* v_categoryAttr_2_; lean_object* v_defn_3_; lean_object* v_valueTypeName_4_; 
v_categoryAttr_2_ = lean_ctor_get(v_ctx_1_, 1);
v_defn_3_ = lean_ctor_get(v_categoryAttr_2_, 0);
v_valueTypeName_4_ = lean_ctor_get(v_defn_3_, 3);
lean_inc(v_valueTypeName_4_);
return v_valueTypeName_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName___redArg___boxed(lean_object* v_ctx_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_5_);
lean_dec_ref(v_ctx_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName(lean_object* v_00_u03b1_7_, lean_object* v_ctx_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_Context_tyName___boxed(lean_object* v_00_u03b1_10_, lean_object* v_ctx_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_ParserCompiler_Context_tyName(v_00_u03b1_10_, v_ctx_11_);
lean_dec_ref(v_ctx_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0(lean_object* v_ctx_18_, lean_object* v_e_19_){
_start:
{
lean_object* v___y_21_; uint8_t v___x_29_; 
v___x_29_ = l_Lean_Expr_isOptParam(v_e_19_);
if (v___x_29_ == 0)
{
v___y_21_ = v_e_19_;
goto v___jp_20_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = l_Lean_Expr_appFn_x21(v_e_19_);
lean_dec_ref(v_e_19_);
v___x_31_ = l_Lean_Expr_appArg_x21(v___x_30_);
lean_dec_ref(v___x_30_);
v___y_21_ = v___x_31_;
goto v___jp_20_;
}
v___jp_20_:
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = ((lean_object*)(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2));
v___x_23_ = l_Lean_Expr_isConstOf(v___y_21_, v___x_22_);
lean_dec_ref(v___y_21_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; 
v___x_24_ = lean_box(0);
return v___x_24_;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_25_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_18_);
v___x_26_ = lean_box(0);
v___x_27_ = l_Lean_mkConst(v___x_25_, v___x_26_);
v___x_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___boxed(lean_object* v_ctx_32_, lean_object* v_e_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0(v_ctx_32_, v_e_33_);
lean_dec_ref(v_ctx_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg(lean_object* v_ctx_35_, lean_object* v_e_36_){
_start:
{
lean_object* v___f_37_; lean_object* v___x_38_; 
v___f_37_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_37_, 0, v_ctx_35_);
v___x_38_ = lean_replace_expr(v___f_37_, v_e_36_);
lean_dec_ref(v___f_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___boxed(lean_object* v_ctx_39_, lean_object* v_e_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_39_, v_e_40_);
lean_dec_ref(v_e_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy(lean_object* v_00_u03b1_42_, lean_object* v_ctx_43_, lean_object* v_e_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_43_, v_e_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_replaceParserTy___boxed(lean_object* v_00_u03b1_46_, lean_object* v_ctx_47_, lean_object* v_e_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_ParserCompiler_replaceParserTy(v_00_u03b1_46_, v_ctx_47_, v_e_48_);
lean_dec_ref(v_e_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0(lean_object* v_k_50_, lean_object* v_b_51_, lean_object* v_c_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
lean_inc(v___y_56_);
lean_inc_ref(v___y_55_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
v___x_58_ = lean_apply_7(v_k_50_, v_b_51_, v_c_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, lean_box(0));
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_k_59_, lean_object* v_b_60_, lean_object* v_c_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0(v_k_59_, v_b_60_, v_c_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(lean_object* v_e_68_, lean_object* v_k_69_, uint8_t v_cleanupAnnotations_70_, uint8_t v_preserveNondepLet_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___f_77_; uint8_t v___x_78_; uint8_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___f_77_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_77_, 0, v_k_69_);
v___x_78_ = 1;
v___x_79_ = 0;
v___x_80_ = lean_box(0);
v___x_81_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_68_, v___x_78_, v___x_78_, v_preserveNondepLet_71_, v___x_79_, v___x_80_, v___f_77_, v_cleanupAnnotations_70_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_89_ == 0)
{
v___x_84_ = v___x_81_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_82_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
else
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v_a_90_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v___x_81_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_81_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___boxed(lean_object* v_e_98_, lean_object* v_k_99_, lean_object* v_cleanupAnnotations_100_, lean_object* v_preserveNondepLet_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_107_; uint8_t v_preserveNondepLet_boxed_108_; lean_object* v_res_109_; 
v_cleanupAnnotations_boxed_107_ = lean_unbox(v_cleanupAnnotations_100_);
v_preserveNondepLet_boxed_108_ = lean_unbox(v_preserveNondepLet_101_);
v_res_109_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_e_98_, v_k_99_, v_cleanupAnnotations_boxed_107_, v_preserveNondepLet_boxed_108_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0(lean_object* v_00_u03b1_110_, lean_object* v_e_111_, lean_object* v_k_112_, uint8_t v_cleanupAnnotations_113_, uint8_t v_preserveNondepLet_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_e_111_, v_k_112_, v_cleanupAnnotations_113_, v_preserveNondepLet_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___boxed(lean_object* v_00_u03b1_121_, lean_object* v_e_122_, lean_object* v_k_123_, lean_object* v_cleanupAnnotations_124_, lean_object* v_preserveNondepLet_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_131_; uint8_t v_preserveNondepLet_boxed_132_; lean_object* v_res_133_; 
v_cleanupAnnotations_boxed_131_ = lean_unbox(v_cleanupAnnotations_124_);
v_preserveNondepLet_boxed_132_ = lean_unbox(v_preserveNondepLet_125_);
v_res_133_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0(v_00_u03b1_121_, v_e_122_, v_k_123_, v_cleanupAnnotations_boxed_131_, v_preserveNondepLet_boxed_132_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1(lean_object* v_e_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___y_141_; lean_object* v___x_158_; uint8_t v_transparency_159_; uint8_t v___x_160_; uint8_t v___x_161_; 
v___x_158_ = l_Lean_Meta_Context_config(v_a_135_);
v_transparency_159_ = lean_ctor_get_uint8(v___x_158_, 9);
lean_dec_ref(v___x_158_);
v___x_160_ = 1;
v___x_161_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_159_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
v___x_162_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
v___y_141_ = v___x_162_;
goto v___jp_140_;
}
else
{
lean_object* v_keyedConfig_163_; uint8_t v_trackZetaDelta_164_; lean_object* v_zetaDeltaSet_165_; lean_object* v_lctx_166_; lean_object* v_localInstances_167_; lean_object* v_defEqCtx_x3f_168_; lean_object* v_synthPendingDepth_169_; lean_object* v_customCanUnfoldPredicate_x3f_170_; uint8_t v_univApprox_171_; uint8_t v_inTypeClassResolution_172_; uint8_t v_cacheInferType_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_keyedConfig_163_ = lean_ctor_get(v_a_135_, 0);
v_trackZetaDelta_164_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*7);
v_zetaDeltaSet_165_ = lean_ctor_get(v_a_135_, 1);
v_lctx_166_ = lean_ctor_get(v_a_135_, 2);
v_localInstances_167_ = lean_ctor_get(v_a_135_, 3);
v_defEqCtx_x3f_168_ = lean_ctor_get(v_a_135_, 4);
v_synthPendingDepth_169_ = lean_ctor_get(v_a_135_, 5);
v_customCanUnfoldPredicate_x3f_170_ = lean_ctor_get(v_a_135_, 6);
v_univApprox_171_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_172_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*7 + 2);
v_cacheInferType_173_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_163_);
v___x_174_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_160_, v_keyedConfig_163_);
lean_inc(v_customCanUnfoldPredicate_x3f_170_);
lean_inc(v_synthPendingDepth_169_);
lean_inc(v_defEqCtx_x3f_168_);
lean_inc_ref(v_localInstances_167_);
lean_inc_ref(v_lctx_166_);
lean_inc(v_zetaDeltaSet_165_);
v___x_175_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v_zetaDeltaSet_165_);
lean_ctor_set(v___x_175_, 2, v_lctx_166_);
lean_ctor_set(v___x_175_, 3, v_localInstances_167_);
lean_ctor_set(v___x_175_, 4, v_defEqCtx_x3f_168_);
lean_ctor_set(v___x_175_, 5, v_synthPendingDepth_169_);
lean_ctor_set(v___x_175_, 6, v_customCanUnfoldPredicate_x3f_170_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*7, v_trackZetaDelta_164_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*7 + 1, v_univApprox_171_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*7 + 2, v_inTypeClassResolution_172_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*7 + 3, v_cacheInferType_173_);
v___x_176_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_134_, v___x_175_, v_a_136_, v_a_137_, v_a_138_);
lean_dec_ref_known(v___x_175_, 7);
v___y_141_ = v___x_176_;
goto v___jp_140_;
}
v___jp_140_:
{
if (lean_obj_tag(v___y_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_a_142_ = lean_ctor_get(v___y_141_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___y_141_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___y_141_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___y_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_150_ = lean_ctor_get(v___y_141_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___y_141_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___y_141_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___y_141_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1___boxed(lean_object* v_e_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1(v_e_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(lean_object* v_type_184_, lean_object* v_k_185_, uint8_t v_cleanupAnnotations_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___f_192_; uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___f_192_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_192_, 0, v_k_185_);
v___x_193_ = 0;
v___x_194_ = lean_box(0);
v___x_195_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_193_, v___x_194_, v_type_184_, v___f_192_, v_cleanupAnnotations_186_, v___x_193_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
v_a_204_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_195_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_195_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg___boxed(lean_object* v_type_212_, lean_object* v_k_213_, lean_object* v_cleanupAnnotations_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_220_; lean_object* v_res_221_; 
v_cleanupAnnotations_boxed_220_ = lean_unbox(v_cleanupAnnotations_214_);
v_res_221_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_type_212_, v_k_213_, v_cleanupAnnotations_boxed_220_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3(lean_object* v_00_u03b1_222_, lean_object* v_type_223_, lean_object* v_k_224_, uint8_t v_cleanupAnnotations_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_type_223_, v_k_224_, v_cleanupAnnotations_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___boxed(lean_object* v_00_u03b1_232_, lean_object* v_type_233_, lean_object* v_k_234_, lean_object* v_cleanupAnnotations_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_241_; lean_object* v_res_242_; 
v_cleanupAnnotations_boxed_241_ = lean_unbox(v_cleanupAnnotations_235_);
v_res_242_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3(v_00_u03b1_232_, v_type_233_, v_k_234_, v_cleanupAnnotations_boxed_241_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(lean_object* v___x_243_, lean_object* v_as_244_, size_t v_i_245_, size_t v_stop_246_, lean_object* v_b_247_){
_start:
{
lean_object* v___y_249_; uint8_t v___x_253_; 
v___x_253_ = lean_usize_dec_eq(v_i_245_, v_stop_246_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v_fst_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_254_ = lean_array_uget_borrowed(v_as_244_, v_i_245_);
v_fst_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc_ref(v___x_243_);
v___x_256_ = l_Lean_LocalContext_getFVar_x21(v___x_243_, v_fst_255_);
v___x_257_ = l_Lean_LocalDecl_type(v___x_256_);
lean_dec_ref(v___x_256_);
v___x_258_ = ((lean_object*)(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2));
v___x_259_ = l_Lean_Expr_isConstOf(v___x_257_, v___x_258_);
lean_dec_ref(v___x_257_);
if (v___x_259_ == 0)
{
v___y_249_ = v_b_247_;
goto v___jp_248_;
}
else
{
lean_object* v___x_260_; 
lean_inc(v___x_254_);
v___x_260_ = lean_array_push(v_b_247_, v___x_254_);
v___y_249_ = v___x_260_;
goto v___jp_248_;
}
}
else
{
lean_dec_ref(v___x_243_);
return v_b_247_;
}
v___jp_248_:
{
size_t v___x_250_; size_t v___x_251_; 
v___x_250_ = ((size_t)1ULL);
v___x_251_ = lean_usize_add(v_i_245_, v___x_250_);
v_i_245_ = v___x_251_;
v_b_247_ = v___y_249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2___boxed(lean_object* v___x_261_, lean_object* v_as_262_, lean_object* v_i_263_, lean_object* v_stop_264_, lean_object* v_b_265_){
_start:
{
size_t v_i_boxed_266_; size_t v_stop_boxed_267_; lean_object* v_res_268_; 
v_i_boxed_266_ = lean_unbox_usize(v_i_263_);
lean_dec(v_i_263_);
v_stop_boxed_267_ = lean_unbox_usize(v_stop_264_);
lean_dec(v_stop_264_);
v_res_268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v___x_261_, v_as_262_, v_i_boxed_266_, v_stop_boxed_267_, v_b_265_);
lean_dec_ref(v_as_262_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed(lean_object* v_x_269_, lean_object* v_e_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(v_x_269_, v_e_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec_ref(v_x_269_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(lean_object* v_a_299_, lean_object* v_params_300_, lean_object* v_x_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v___y_309_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_322_ = l_Array_zipIdx___redArg(v_params_300_, v___x_307_);
v___x_323_ = lean_array_get_size(v___x_322_);
v___x_324_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0));
v___x_325_ = lean_nat_dec_lt(v___x_307_, v___x_323_);
if (v___x_325_ == 0)
{
lean_dec_ref(v___x_322_);
v___y_309_ = v___x_324_;
goto v___jp_308_;
}
else
{
lean_object* v_lctx_326_; size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; 
v_lctx_326_ = lean_ctor_get(v___y_302_, 2);
v___x_327_ = ((size_t)0ULL);
v___x_328_ = lean_usize_of_nat(v___x_323_);
lean_inc_ref(v_lctx_326_);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v_lctx_326_, v___x_322_, v___x_327_, v___x_328_, v___x_324_);
lean_dec_ref(v___x_322_);
v___y_309_ = v___x_329_;
goto v___jp_308_;
}
v___jp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_310_ = lean_array_get_size(v___y_309_);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_dec_eq(v___x_310_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec_ref(v___y_309_);
v___x_313_ = lean_box(0);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; lean_object* v_snd_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_315_ = lean_array_fget(v___y_309_, v___x_307_);
lean_dec_ref(v___y_309_);
v_snd_316_ = lean_ctor_get(v___x_315_, 1);
lean_inc(v_snd_316_);
lean_dec(v___x_315_);
v___x_317_ = l_Lean_Expr_getAppNumArgs(v_a_299_);
v___x_318_ = lean_nat_sub(v___x_317_, v_snd_316_);
lean_dec(v_snd_316_);
lean_dec(v___x_317_);
v___x_319_ = lean_nat_sub(v___x_318_, v___x_311_);
lean_dec(v___x_318_);
v___x_320_ = l_Lean_Expr_getRevArg_x21(v_a_299_, v___x_319_);
v___x_321_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v___x_320_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed(lean_object* v_a_330_, lean_object* v_params_331_, lean_object* v_x_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(v_a_330_, v_params_331_, v_x_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec_ref(v_x_332_);
lean_dec_ref(v_a_330_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f(lean_object* v_e_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___f_345_; lean_object* v___x_346_; 
v___f_345_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed), 7, 0);
v___x_346_ = l_Lean_Meta_whnfCore(v_e_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_413_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_413_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_413_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_413_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
switch(lean_obj_tag(v_a_347_))
{
case 6:
{
lean_del_object(v___x_349_);
goto v___jp_380_;
}
case 8:
{
lean_del_object(v___x_349_);
goto v___jp_380_;
}
default: 
{
lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
lean_dec_ref(v___f_345_);
v___x_383_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1));
v___x_384_ = lean_unsigned_to_nat(3u);
v___x_385_ = l_Lean_Expr_isAppOfArity(v_a_347_, v___x_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_386_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3));
v___x_387_ = lean_unsigned_to_nat(4u);
v___x_388_ = l_Lean_Expr_isAppOfArity(v_a_347_, v___x_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_389_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5));
v___x_390_ = lean_unsigned_to_nat(2u);
v___x_391_ = l_Lean_Expr_isAppOfArity(v_a_347_, v___x_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; uint8_t v___x_393_; 
lean_del_object(v___x_349_);
v___x_392_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7));
v___x_393_ = l_Lean_Expr_isAppOfArity(v_a_347_, v___x_392_, v___x_390_);
if (v___x_393_ == 0)
{
lean_object* v___f_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
lean_inc(v_a_347_);
v___f_394_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed), 8, 1);
lean_closure_set(v___f_394_, 0, v_a_347_);
v___x_395_ = l_Lean_Expr_getAppFn(v_a_347_);
lean_dec(v_a_347_);
lean_inc(v_a_343_);
lean_inc_ref(v_a_342_);
lean_inc(v_a_341_);
lean_inc_ref(v_a_340_);
v___x_396_ = lean_infer_type(v___x_395_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_398_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref_known(v___x_396_, 1);
v___x_398_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_397_, v___f_394_, v___x_393_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
return v___x_398_;
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref(v___f_394_);
v_a_399_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_396_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_396_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = l_Lean_Expr_getAppNumArgs(v_a_347_);
v___x_409_ = lean_nat_sub(v___x_408_, v___x_407_);
lean_dec(v___x_408_);
v___x_410_ = lean_nat_sub(v___x_409_, v___x_407_);
lean_dec(v___x_409_);
v___x_411_ = l_Lean_Expr_getRevArg_x21(v_a_347_, v___x_410_);
lean_dec(v_a_347_);
v_e_339_ = v___x_411_;
goto _start;
}
}
else
{
goto v___jp_351_;
}
}
else
{
goto v___jp_351_;
}
}
else
{
goto v___jp_351_;
}
}
}
v___jp_351_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_352_ = l_Lean_Expr_getAppNumArgs(v_a_347_);
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_sub(v___x_352_, v___x_353_);
lean_dec(v___x_352_);
v___x_355_ = l_Lean_Expr_getRevArg_x21(v_a_347_, v___x_354_);
lean_dec(v_a_347_);
v___x_356_ = l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1(v___x_355_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_365_; 
lean_del_object(v___x_349_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_365_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v_a_357_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_361_);
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_379_; 
v_a_366_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_379_ == 0)
{
v___x_368_ = v___x_356_;
v_isShared_369_ = v_isSharedCheck_379_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_356_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_379_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
lean_inc(v_a_366_);
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_378_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
uint8_t v___x_372_; 
v___x_372_ = l_Lean_Exception_isInterrupt(v_a_366_);
if (v___x_372_ == 0)
{
uint8_t v___x_373_; 
v___x_373_ = l_Lean_Exception_isRuntime(v_a_366_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_376_; 
lean_dec_ref(v___x_371_);
v___x_374_ = lean_box(0);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_374_);
v___x_376_ = v___x_349_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_del_object(v___x_349_);
return v___x_371_;
}
}
else
{
lean_dec(v_a_366_);
lean_del_object(v___x_349_);
return v___x_371_;
}
}
}
}
}
v___jp_380_:
{
uint8_t v___x_381_; lean_object* v___x_382_; 
v___x_381_ = 0;
v___x_382_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_a_347_, v___f_345_, v___x_381_, v___x_381_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
return v___x_382_;
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref(v___f_345_);
v_a_414_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_346_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_346_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(lean_object* v_x_422_, lean_object* v_e_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v_e_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___boxed(lean_object* v_e_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v_e_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(lean_object* v_x_437_, lean_object* v_b_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v_b_438_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed(lean_object* v_x_445_, lean_object* v_b_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(v_x_445_, v_b_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec_ref(v_x_445_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(lean_object* v_ctx_456_, lean_object* v_as_457_, size_t v_i_458_, size_t v_stop_459_, lean_object* v_b_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = lean_usize_dec_eq(v_i_458_, v_stop_459_);
if (v___x_466_ == 0)
{
size_t v___x_467_; size_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_sub(v_i_458_, v___x_467_);
v___x_469_ = lean_array_uget_borrowed(v_as_457_, v___x_468_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
lean_inc(v___y_462_);
lean_inc_ref(v___y_461_);
lean_inc(v___x_469_);
v___x_470_ = lean_infer_type(v___x_469_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; lean_object* v___x_475_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
lean_inc_ref(v_ctx_456_);
v___x_472_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_456_, v_a_471_);
lean_dec(v_a_471_);
v___x_473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__1));
v___x_474_ = 0;
v___x_475_ = l_Lean_mkForall(v___x_473_, v___x_474_, v___x_472_, v_b_460_);
v_i_458_ = v___x_468_;
v_b_460_ = v___x_475_;
goto _start;
}
else
{
lean_dec_ref(v_b_460_);
lean_dec_ref(v_ctx_456_);
return v___x_470_;
}
}
else
{
lean_object* v___x_477_; 
lean_dec_ref(v_ctx_456_);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v_b_460_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___boxed(lean_object* v_ctx_478_, lean_object* v_as_479_, lean_object* v_i_480_, lean_object* v_stop_481_, lean_object* v_b_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
size_t v_i_boxed_488_; size_t v_stop_boxed_489_; lean_object* v_res_490_; 
v_i_boxed_488_ = lean_unbox_usize(v_i_480_);
lean_dec(v_i_480_);
v_stop_boxed_489_ = lean_unbox_usize(v_stop_481_);
lean_dec(v_stop_481_);
v_res_490_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_478_, v_as_479_, v_i_boxed_488_, v_stop_boxed_489_, v_b_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec_ref(v_as_479_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3(lean_object* v_ctx_491_, lean_object* v_params_492_, lean_object* v_x_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_499_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_491_);
v___x_500_ = lean_box(0);
v___x_501_ = l_Lean_mkConst(v___x_499_, v___x_500_);
v___x_502_ = lean_array_get_size(v_params_492_);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_nat_dec_lt(v___x_503_, v___x_502_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec_ref(v_ctx_491_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_501_);
return v___x_505_;
}
else
{
size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_usize_of_nat(v___x_502_);
v___x_507_ = ((size_t)0ULL);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_491_, v_params_492_, v___x_506_, v___x_507_, v___x_501_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3___boxed(lean_object* v_ctx_509_, lean_object* v_params_510_, lean_object* v_x_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3(v_ctx_509_, v_params_510_, v_x_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec_ref(v_x_511_);
lean_dec_ref(v_params_510_);
return v_res_517_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_518_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg(){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__1);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___boxed(lean_object* v___dummy_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg();
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0(lean_object* v_k_525_, uint8_t v_usedLetOnly_526_, lean_object* v_xs_527_, lean_object* v_b_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; 
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
lean_inc_ref(v_xs_527_);
v___x_534_ = lean_apply_7(v_k_525_, v_xs_527_, v_b_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, lean_box(0));
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; uint8_t v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
v___x_536_ = 0;
v___x_537_ = 1;
v___x_538_ = l_Lean_Meta_mkLambdaFVars(v_xs_527_, v_a_535_, v___x_536_, v_usedLetOnly_526_, v___x_536_, v___x_536_, v___x_537_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec_ref(v_xs_527_);
return v___x_538_;
}
else
{
lean_dec_ref(v_xs_527_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0___boxed(lean_object* v_k_539_, lean_object* v_usedLetOnly_540_, lean_object* v_xs_541_, lean_object* v_b_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
uint8_t v_usedLetOnly_boxed_548_; lean_object* v_res_549_; 
v_usedLetOnly_boxed_548_ = lean_unbox(v_usedLetOnly_540_);
v_res_549_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0(v_k_539_, v_usedLetOnly_boxed_548_, v_xs_541_, v_b_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(lean_object* v_e_550_, lean_object* v_k_551_, uint8_t v_cleanupAnnotations_552_, uint8_t v_preserveNondepLet_553_, uint8_t v_usedLetOnly_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; lean_object* v___f_561_; lean_object* v___x_562_; 
v___x_560_ = lean_box(v_usedLetOnly_554_);
v___f_561_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0___boxed), 9, 2);
lean_closure_set(v___f_561_, 0, v_k_551_);
lean_closure_set(v___f_561_, 1, v___x_560_);
v___x_562_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_e_550_, v___f_561_, v_cleanupAnnotations_552_, v_preserveNondepLet_553_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___boxed(lean_object* v_e_563_, lean_object* v_k_564_, lean_object* v_cleanupAnnotations_565_, lean_object* v_preserveNondepLet_566_, lean_object* v_usedLetOnly_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_573_; uint8_t v_preserveNondepLet_boxed_574_; uint8_t v_usedLetOnly_boxed_575_; lean_object* v_res_576_; 
v_cleanupAnnotations_boxed_573_ = lean_unbox(v_cleanupAnnotations_565_);
v_preserveNondepLet_boxed_574_ = lean_unbox(v_preserveNondepLet_566_);
v_usedLetOnly_boxed_575_ = lean_unbox(v_usedLetOnly_567_);
v_res_576_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_e_563_, v_k_564_, v_cleanupAnnotations_boxed_573_, v_preserveNondepLet_boxed_574_, v_usedLetOnly_boxed_575_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5_spec__7(lean_object* v_msgData_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; lean_object* v_env_584_; uint8_t v___x_585_; lean_object* v_env_586_; lean_object* v___x_587_; lean_object* v_toCold_588_; lean_object* v_mctx_589_; lean_object* v_lctx_590_; lean_object* v_options_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_583_ = lean_st_ref_get(v___y_581_);
v_env_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc_ref(v_env_584_);
lean_dec(v___x_583_);
v___x_585_ = 0;
v_env_586_ = l_Lean_Environment_setRecordingDeps(v_env_584_, v___x_585_);
v___x_587_ = lean_st_ref_get(v___y_579_);
v_toCold_588_ = lean_ctor_get(v___y_580_, 0);
v_mctx_589_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_mctx_589_);
lean_dec(v___x_587_);
v_lctx_590_ = lean_ctor_get(v___y_578_, 2);
v_options_591_ = lean_ctor_get(v_toCold_588_, 2);
lean_inc_ref(v_options_591_);
lean_inc_ref(v_lctx_590_);
v___x_592_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_592_, 0, v_env_586_);
lean_ctor_set(v___x_592_, 1, v_mctx_589_);
lean_ctor_set(v___x_592_, 2, v_lctx_590_);
lean_ctor_set(v___x_592_, 3, v_options_591_);
v___x_593_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v_msgData_577_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5_spec__7___boxed(lean_object* v_msgData_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5_spec__7(v_msgData_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___redArg(lean_object* v_msg_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_ref_608_; lean_object* v___x_609_; lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_618_; 
v_ref_608_ = lean_ctor_get(v___y_605_, 2);
v___x_609_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5_spec__7(v_msg_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_618_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_618_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_618_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_616_; 
lean_inc(v_ref_608_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v_ref_608_);
lean_ctor_set(v___x_614_, 1, v_a_610_);
if (v_isShared_613_ == 0)
{
lean_ctor_set_tag(v___x_612_, 1);
lean_ctor_set(v___x_612_, 0, v___x_614_);
v___x_616_ = v___x_612_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___redArg___boxed(lean_object* v_msg_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___redArg(v_msg_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__11___redArg(lean_object* v_ref_626_, lean_object* v_msg_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_toCold_633_; lean_object* v_currRecDepth_634_; lean_object* v_ref_635_; uint16_t v_optionFlags_636_; uint8_t v_suppressElabErrors_637_; uint8_t v_checkDeprecated_638_; uint8_t v_isRecordingDeps_639_; lean_object* v_ref_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_toCold_633_ = lean_ctor_get(v___y_630_, 0);
v_currRecDepth_634_ = lean_ctor_get(v___y_630_, 1);
v_ref_635_ = lean_ctor_get(v___y_630_, 2);
v_optionFlags_636_ = lean_ctor_get_uint16(v___y_630_, sizeof(void*)*3);
v_suppressElabErrors_637_ = lean_ctor_get_uint8(v___y_630_, sizeof(void*)*3 + 2);
v_checkDeprecated_638_ = lean_ctor_get_uint8(v___y_630_, sizeof(void*)*3 + 3);
v_isRecordingDeps_639_ = lean_ctor_get_uint8(v___y_630_, sizeof(void*)*3 + 4);
v_ref_640_ = l_Lean_replaceRef(v_ref_626_, v_ref_635_);
lean_inc(v_currRecDepth_634_);
lean_inc_ref(v_toCold_633_);
v___x_641_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_641_, 0, v_toCold_633_);
lean_ctor_set(v___x_641_, 1, v_currRecDepth_634_);
lean_ctor_set(v___x_641_, 2, v_ref_640_);
lean_ctor_set_uint16(v___x_641_, sizeof(void*)*3, v_optionFlags_636_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*3 + 2, v_suppressElabErrors_637_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*3 + 3, v_checkDeprecated_638_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*3 + 4, v_isRecordingDeps_639_);
v___x_642_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___redArg(v_msg_627_, v___y_628_, v___y_629_, v___x_641_, v___y_631_);
lean_dec_ref_known(v___x_641_, 3);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_ref_643_, lean_object* v_msg_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__11___redArg(v_ref_643_, v_msg_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v_ref_643_);
return v_res_650_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__0);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
lean_ctor_set(v___x_655_, 2, v___x_654_);
lean_ctor_set(v___x_655_, 3, v___x_654_);
lean_ctor_set(v___x_655_, 4, v___x_653_);
lean_ctor_set(v___x_655_, 5, v___x_653_);
lean_ctor_set(v___x_655_, 6, v___x_653_);
lean_ctor_set(v___x_655_, 7, v___x_653_);
lean_ctor_set(v___x_655_, 8, v___x_653_);
lean_ctor_set(v___x_655_, 9, v___x_653_);
lean_ctor_set(v___x_655_, 10, v___x_653_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_unsigned_to_nat(32u);
v___x_657_ = lean_mk_empty_array_with_capacity(v___x_656_);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3(void){
_start:
{
size_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_659_ = ((size_t)5ULL);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_unsigned_to_nat(32u);
v___x_662_ = lean_mk_empty_array_with_capacity(v___x_661_);
v___x_663_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__2);
v___x_664_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___x_662_);
lean_ctor_set(v___x_664_, 2, v___x_660_);
lean_ctor_set(v___x_664_, 3, v___x_660_);
lean_ctor_set_usize(v___x_664_, 4, v___x_659_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__4(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_665_ = lean_box(1);
v___x_666_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3);
v___x_667_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__0);
v___x_668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v___x_666_);
lean_ctor_set(v___x_668_, 2, v___x_665_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__5));
v___x_671_ = l_Lean_stringToMessageData(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__8(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__7));
v___x_674_ = l_Lean_stringToMessageData(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__10(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__9));
v___x_677_ = l_Lean_stringToMessageData(v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__12(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__11));
v___x_680_ = l_Lean_stringToMessageData(v___x_679_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__14(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__13));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__16(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__15));
v___x_686_ = l_Lean_stringToMessageData(v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__18(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__17));
v___x_689_ = l_Lean_stringToMessageData(v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__20(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__19));
v___x_692_ = l_Lean_stringToMessageData(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__22(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__21));
v___x_695_ = l_Lean_stringToMessageData(v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__24(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__23));
v___x_698_ = l_Lean_stringToMessageData(v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__26(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__25));
v___x_701_ = l_Lean_stringToMessageData(v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg(lean_object* v_msg_702_, lean_object* v_declHint_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_env_708_; uint8_t v___x_709_; 
v___x_706_ = lean_box(0);
v___x_707_ = lean_st_ref_get(v___y_704_);
v_env_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc_ref(v_env_708_);
lean_dec(v___x_707_);
v___x_709_ = l_Lean_Name_isAnonymous(v_declHint_703_);
if (v___x_709_ == 0)
{
uint8_t v_isExporting_710_; 
v_isExporting_710_ = lean_ctor_get_uint8(v_env_708_, sizeof(void*)*13);
if (v_isExporting_710_ == 0)
{
lean_object* v___x_711_; 
lean_dec_ref(v_env_708_);
lean_dec(v_declHint_703_);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v_msg_702_);
return v___x_711_;
}
else
{
lean_object* v___x_712_; uint8_t v___x_713_; 
lean_inc_ref(v_env_708_);
v___x_712_ = l_Lean_Environment_setExporting(v_env_708_, v___x_709_);
lean_inc(v_declHint_703_);
lean_inc_ref(v___x_712_);
v___x_713_ = l_Lean_Environment_contains(v___x_712_, v_declHint_703_, v_isExporting_710_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
lean_dec_ref(v___x_712_);
lean_dec_ref(v_env_708_);
lean_dec(v_declHint_703_);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v_msg_702_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_c_720_; lean_object* v___x_721_; 
v___x_715_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__1);
v___x_716_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__4);
v___x_717_ = l_Lean_Options_empty;
lean_inc_ref(v___x_712_);
v___x_718_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_718_, 0, v___x_712_);
lean_ctor_set(v___x_718_, 1, v___x_715_);
lean_ctor_set(v___x_718_, 2, v___x_716_);
lean_ctor_set(v___x_718_, 3, v___x_717_);
lean_inc(v_declHint_703_);
v___x_719_ = l_Lean_MessageData_ofConstName(v_declHint_703_, v___x_709_);
v_c_720_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_720_, 0, v___x_718_);
lean_ctor_set(v_c_720_, 1, v___x_719_);
v___x_721_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_712_, v_declHint_703_);
lean_dec_ref(v___x_712_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec_ref(v_env_708_);
lean_dec(v_declHint_703_);
v___x_722_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v_c_720_);
v___x_724_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__8);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = l_Lean_MessageData_note(v___x_725_);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v_msg_702_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
else
{
lean_object* v_val_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_782_; 
v_val_729_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_782_ == 0)
{
v___x_731_ = v___x_721_;
v_isShared_732_ = v_isSharedCheck_782_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_val_729_);
lean_dec(v___x_721_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_782_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v_modules_734_; lean_object* v_moduleNames_735_; lean_object* v_mod_736_; uint8_t v___x_751_; 
v___x_733_ = l_Lean_Environment_header(v_env_708_);
lean_dec_ref(v_env_708_);
v_modules_734_ = lean_ctor_get(v___x_733_, 3);
lean_inc_ref(v_modules_734_);
v_moduleNames_735_ = lean_ctor_get(v___x_733_, 4);
lean_inc_ref(v_moduleNames_735_);
lean_dec_ref(v___x_733_);
v_mod_736_ = lean_array_get(v___x_706_, v_moduleNames_735_, v_val_729_);
lean_dec_ref(v_moduleNames_735_);
v___x_751_ = l_Lean_isPrivateName(v_declHint_703_);
lean_dec(v_declHint_703_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = lean_array_get_size(v_modules_734_);
v___x_753_ = lean_nat_dec_lt(v_val_729_, v___x_752_);
if (v___x_753_ == 0)
{
lean_dec_ref(v_modules_734_);
lean_dec(v_val_729_);
goto v___jp_737_;
}
else
{
lean_object* v___x_754_; lean_object* v_toImport_755_; uint8_t v_isExported_756_; 
v___x_754_ = lean_array_fget(v_modules_734_, v_val_729_);
lean_dec(v_val_729_);
lean_dec_ref(v_modules_734_);
v_toImport_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc_ref(v_toImport_755_);
lean_dec(v___x_754_);
v_isExported_756_ = lean_ctor_get_uint8(v_toImport_755_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_755_);
if (v_isExported_756_ == 0)
{
goto v___jp_737_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_del_object(v___x_731_);
v___x_757_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__16);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v_c_720_);
v___x_759_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__18);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_MessageData_ofName(v_mod_736_);
lean_inc_ref(v___x_761_);
v___x_762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__20);
v___x_764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_761_);
v___x_766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__22);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = l_Lean_MessageData_note(v___x_767_);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v_msg_702_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec_ref(v_modules_734_);
lean_del_object(v___x_731_);
lean_dec(v_val_729_);
v___x_771_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6);
v___x_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v_c_720_);
v___x_773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__24);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = l_Lean_MessageData_ofName(v_mod_736_);
v___x_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__26);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Lean_MessageData_note(v___x_778_);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v_msg_702_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
v___jp_737_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_738_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__10);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v_c_720_);
v___x_740_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__12);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_MessageData_ofName(v_mod_736_);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__14);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = l_Lean_MessageData_note(v___x_745_);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v_msg_702_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 0);
lean_ctor_set(v___x_731_, 0, v___x_747_);
v___x_749_ = v___x_731_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_783_; 
lean_dec_ref(v_env_708_);
lean_dec(v_declHint_703_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v_msg_702_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___boxed(lean_object* v_msg_784_, lean_object* v_declHint_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg(v_msg_784_, v_declHint_785_, v___y_786_);
lean_dec(v___y_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10(lean_object* v_msg_789_, lean_object* v_declHint_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_806_; 
v___x_796_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg(v_msg_789_, v_declHint_790_, v___y_794_);
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_806_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_806_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_806_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_801_ = l_Lean_unknownIdentifierMessageTag;
v___x_802_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v_a_797_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_802_);
v___x_804_ = v___x_799_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10___boxed(lean_object* v_msg_807_, lean_object* v_declHint_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10(v_msg_807_, v_declHint_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9___redArg(lean_object* v_ref_815_, lean_object* v_msg_816_, lean_object* v_declHint_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; lean_object* v_a_824_; lean_object* v___x_825_; 
v___x_823_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10(v_msg_816_, v_declHint_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref(v___x_823_);
v___x_825_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__11___redArg(v_ref_815_, v_a_824_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9___redArg___boxed(lean_object* v_ref_826_, lean_object* v_msg_827_, lean_object* v_declHint_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9___redArg(v_ref_826_, v_msg_827_, v_declHint_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v_ref_826_);
return v_res_834_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__0));
v___x_837_ = l_Lean_stringToMessageData(v___x_836_);
return v___x_837_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__2));
v___x_840_ = l_Lean_stringToMessageData(v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_841_, lean_object* v_constName_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_848_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_849_ = 0;
lean_inc(v_constName_842_);
v___x_850_ = l_Lean_MessageData_ofConstName(v_constName_842_, v___x_849_);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_848_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9___redArg(v_ref_841_, v___x_853_, v_constName_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_855_, lean_object* v_constName_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_855_, v_constName_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v_ref_855_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(lean_object* v_constName_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_ref_869_; lean_object* v___x_870_; 
v_ref_869_ = lean_ctor_get(v___y_866_, 2);
v___x_870_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_869_, v_constName_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg___boxed(lean_object* v_constName_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(lean_object* v_constName_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; lean_object* v_env_885_; uint8_t v___x_886_; lean_object* v___x_887_; 
v___x_884_ = lean_st_ref_get(v___y_882_);
v_env_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc_ref(v_env_885_);
lean_dec(v___x_884_);
v___x_886_ = 0;
lean_inc(v_constName_878_);
v___x_887_ = l_Lean_Environment_find_x3f(v_env_885_, v_constName_878_, v___x_886_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
return v___x_888_;
}
else
{
lean_object* v_val_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v_constName_878_);
v_val_889_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_887_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_val_889_);
lean_dec(v___x_887_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 0);
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_val_889_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3___boxed(lean_object* v_constName_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(v_constName_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(lean_object* v_b_904_, lean_object* v_arg_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = l_Lean_Expr_app___override(v_b_904_, v_arg_905_);
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1___boxed(lean_object* v_b_914_, lean_object* v_arg_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_914_, v_arg_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed(lean_object* v_ctx_923_, lean_object* v_builtin_924_, lean_object* v_force_925_, lean_object* v_x_926_, lean_object* v_b_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
uint8_t v_builtin_boxed_933_; uint8_t v_force_boxed_934_; lean_object* v_res_935_; 
v_builtin_boxed_933_ = lean_unbox(v_builtin_924_);
v_force_boxed_934_ = lean_unbox(v_force_925_);
v_res_935_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(v_ctx_923_, v_builtin_boxed_933_, v_force_boxed_934_, v_x_926_, v_b_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec_ref(v_x_926_);
return v_res_935_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_936_; lean_object* v_dummy_937_; 
v___x_936_ = lean_box(0);
v_dummy_937_ = l_Lean_Expr_sort___override(v___x_936_);
return v_dummy_937_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(lean_object* v_upperBound_938_, lean_object* v_params_939_, lean_object* v___x_940_, lean_object* v_ctx_941_, uint8_t v_builtin_942_, uint8_t v_force_943_, lean_object* v_a_944_, lean_object* v_b_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___y_952_; uint8_t v___x_974_; 
v___x_974_ = lean_nat_dec_lt(v_a_944_, v_upperBound_938_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
lean_dec(v_a_944_);
lean_dec_ref(v_ctx_941_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_b_945_);
return v___x_975_;
}
else
{
lean_object* v___f_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___f_976_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0));
v___x_977_ = l_Lean_instInhabitedExpr;
v___x_978_ = lean_array_get_borrowed(v___x_977_, v_params_939_, v_a_944_);
v___x_979_ = lean_array_get_borrowed(v___x_977_, v___x_940_, v_a_944_);
lean_inc(v___y_949_);
lean_inc_ref(v___y_948_);
lean_inc(v___y_947_);
lean_inc_ref(v___y_946_);
lean_inc(v___x_978_);
v___x_980_ = lean_infer_type(v___x_978_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; uint8_t v___x_982_; lean_object* v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = 0;
v___x_983_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_981_, v___f_976_, v___x_982_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_941_);
v___x_986_ = l_Lean_Expr_isConstOf(v_a_984_, v___x_985_);
lean_dec(v___x_985_);
lean_dec(v_a_984_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
lean_inc(v___x_979_);
v___x_987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_945_, v___x_979_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
v___y_952_ = v___x_987_;
goto v___jp_951_;
}
else
{
lean_object* v___x_988_; 
lean_inc(v___x_979_);
lean_inc_ref(v_ctx_941_);
v___x_988_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_941_, v_builtin_942_, v_force_943_, v___x_979_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_945_, v_a_989_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
v___y_952_ = v___x_990_;
goto v___jp_951_;
}
else
{
lean_dec_ref(v_b_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_ctx_941_);
return v___x_988_;
}
}
}
else
{
lean_dec_ref(v_b_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_ctx_941_);
return v___x_983_;
}
}
else
{
lean_dec_ref(v_b_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_ctx_941_);
return v___x_980_;
}
}
v___jp_951_:
{
if (lean_obj_tag(v___y_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_965_; 
v_a_953_ = lean_ctor_get(v___y_952_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___y_952_);
if (v_isSharedCheck_965_ == 0)
{
v___x_955_ = v___y_952_;
v_isShared_956_ = v_isSharedCheck_965_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___y_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_965_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
if (lean_obj_tag(v_a_953_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; 
lean_dec(v_a_944_);
lean_dec_ref(v_ctx_941_);
v_a_957_ = lean_ctor_get(v_a_953_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v_a_953_, 1);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v_a_957_);
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_del_object(v___x_955_);
v_a_961_ = lean_ctor_get(v_a_953_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v_a_953_, 1);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_add(v_a_944_, v___x_962_);
lean_dec(v_a_944_);
v_a_944_ = v___x_963_;
v_b_945_ = v_a_961_;
goto _start;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_a_944_);
lean_dec_ref(v_ctx_941_);
v_a_966_ = lean_ctor_get(v___y_952_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___y_952_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___y_952_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___y_952_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(lean_object* v_a_991_, lean_object* v_ctx_992_, uint8_t v_builtin_993_, uint8_t v_force_994_, lean_object* v___x_995_, lean_object* v_params_996_, lean_object* v_x_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_dummy_1003_; lean_object* v_nargs_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___y_1010_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v_dummy_1003_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0, &l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0);
v_nargs_1004_ = l_Lean_Expr_getAppNumArgs(v_a_991_);
lean_inc(v_nargs_1004_);
v___x_1005_ = lean_mk_array(v_nargs_1004_, v_dummy_1003_);
v___x_1006_ = lean_unsigned_to_nat(1u);
v___x_1007_ = lean_nat_sub(v_nargs_1004_, v___x_1006_);
lean_dec(v_nargs_1004_);
v___x_1008_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_991_, v___x_1005_, v___x_1007_);
v___x_1013_ = lean_array_get_size(v_params_996_);
v___x_1014_ = lean_array_get_size(v___x_1008_);
v___x_1015_ = lean_nat_dec_le(v___x_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
v___y_1010_ = v___x_1014_;
goto v___jp_1009_;
}
else
{
v___y_1010_ = v___x_1013_;
goto v___jp_1009_;
}
v___jp_1009_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v___y_1010_, v_params_996_, v___x_1008_, v_ctx_992_, v_builtin_993_, v_force_994_, v___x_1011_, v___x_995_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec_ref(v___x_1008_);
lean_dec(v___y_1010_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed(lean_object* v_a_1016_, lean_object* v_ctx_1017_, lean_object* v_builtin_1018_, lean_object* v_force_1019_, lean_object* v___x_1020_, lean_object* v_params_1021_, lean_object* v_x_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
uint8_t v_builtin_boxed_1028_; uint8_t v_force_boxed_1029_; lean_object* v_res_1030_; 
v_builtin_boxed_1028_ = lean_unbox(v_builtin_1018_);
v_force_boxed_1029_ = lean_unbox(v_force_1019_);
v_res_1030_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(v_a_1016_, v_ctx_1017_, v_builtin_boxed_1028_, v_force_boxed_1029_, v___x_1020_, v_params_1021_, v_x_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec_ref(v_x_1022_);
lean_dec_ref(v_params_1021_);
return v_res_1030_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5);
v___x_1047_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
lean_ctor_set(v___x_1047_, 2, v___x_1045_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg();
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1051_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9);
v___x_1052_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8);
v___x_1053_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5);
v___x_1054_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
v___x_1055_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v___x_1053_);
lean_ctor_set(v___x_1055_, 2, v___x_1052_);
lean_ctor_set(v___x_1055_, 3, v___x_1053_);
lean_ctor_set(v___x_1055_, 4, v___x_1053_);
lean_ctor_set(v___x_1055_, 5, v___x_1053_);
lean_ctor_set(v___x_1055_, 6, v___x_1051_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11));
v___x_1058_ = l_Lean_stringToMessageData(v___x_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13));
v___x_1061_ = l_Lean_stringToMessageData(v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__24(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__23));
v___x_1078_ = l_Lean_stringToMessageData(v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg(lean_object* v_ctx_1079_, uint8_t v_builtin_1080_, uint8_t v_force_1081_, lean_object* v_e_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___f_1091_; lean_object* v___f_1092_; lean_object* v___x_1093_; 
v___f_1088_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0));
v___x_1089_ = lean_box(v_builtin_1080_);
v___x_1090_ = lean_box(v_force_1081_);
lean_inc_ref_n(v_ctx_1079_, 2);
v___f_1091_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1091_, 0, v_ctx_1079_);
lean_closure_set(v___f_1091_, 1, v___x_1089_);
lean_closure_set(v___f_1091_, 2, v___x_1090_);
v___f_1092_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_1092_, 0, v_ctx_1079_);
v___x_1093_ = l_Lean_Meta_whnfCore(v_e_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v_p_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
switch(lean_obj_tag(v_a_1094_))
{
case 6:
{
uint8_t v___x_1110_; uint8_t v___x_1111_; lean_object* v___x_1112_; 
lean_inc_ref(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
lean_dec_ref(v___f_1092_);
lean_dec_ref(v_ctx_1079_);
v___x_1110_ = 0;
v___x_1111_ = 1;
v___x_1112_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_a_1094_, v___f_1091_, v___x_1110_, v___x_1110_, v___x_1111_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1112_;
}
case 8:
{
uint8_t v___x_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; 
lean_inc_ref(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
lean_dec_ref(v___f_1092_);
lean_dec_ref(v_ctx_1079_);
v___x_1113_ = 0;
v___x_1114_ = 1;
v___x_1115_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_a_1094_, v___f_1091_, v___x_1113_, v___x_1113_, v___x_1114_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1115_;
}
case 1:
{
lean_dec_ref(v___f_1092_);
lean_dec_ref(v___f_1091_);
lean_dec_ref(v_ctx_1079_);
return v___x_1093_;
}
default: 
{
lean_object* v___x_1116_; 
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
lean_dec_ref(v___f_1091_);
v___x_1116_ = l_Lean_Expr_getAppFn(v_a_1094_);
if (lean_obj_tag(v___x_1116_) == 4)
{
lean_object* v_declName_1117_; lean_object* v___x_1118_; lean_object* v_env_1119_; lean_object* v_varName_1120_; lean_object* v_categoryAttr_1121_; lean_object* v_combinatorAttr_1122_; lean_object* v___x_1123_; 
v_declName_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_declName_1117_);
lean_dec_ref_known(v___x_1116_, 2);
v___x_1118_ = lean_st_ref_get(v_a_1086_);
v_env_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc_ref_n(v_env_1119_, 2);
lean_dec(v___x_1118_);
v_varName_1120_ = lean_ctor_get(v_ctx_1079_, 0);
v_categoryAttr_1121_ = lean_ctor_get(v_ctx_1079_, 1);
v_combinatorAttr_1122_ = lean_ctor_get(v_ctx_1079_, 2);
v___x_1123_ = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(v_combinatorAttr_1122_, v_env_1119_, v_declName_1117_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_inc(v_varName_1120_);
lean_inc_n(v_declName_1117_, 2);
v___x_1124_ = l_Lean_Name_append(v_declName_1117_, v_varName_1120_);
v___x_1125_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(v_declName_1117_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v___x_1127_ = l_Lean_ConstantInfo_type(v_a_1126_);
v___x_1128_ = 0;
lean_inc_ref(v___x_1127_);
v___x_1129_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v___x_1127_, v___f_1088_, v___x_1128_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1163_; uint8_t v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1254_; uint8_t v___y_1255_; uint8_t v___y_1271_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___x_1286_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20));
v___x_1287_ = l_Lean_Expr_isConstOf(v_a_1130_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = ((lean_object*)(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2));
v___x_1289_ = l_Lean_Expr_isConstOf(v_a_1130_, v___x_1288_);
lean_dec(v_a_1130_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_dec_ref(v___x_1127_);
lean_dec(v_a_1126_);
lean_dec(v___x_1124_);
lean_dec_ref(v_env_1119_);
lean_dec(v_declName_1117_);
lean_dec_ref(v___f_1092_);
lean_inc(v_a_1094_);
v___x_1290_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_1094_, v___x_1128_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
if (lean_obj_tag(v_a_1291_) == 1)
{
lean_object* v_val_1292_; 
lean_dec(v_a_1094_);
v_val_1292_ = lean_ctor_get(v_a_1291_, 0);
lean_inc(v_val_1292_);
lean_dec_ref_known(v_a_1291_, 1);
v_e_1082_ = v_val_1292_;
goto _start;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_inc(v_varName_1120_);
lean_dec(v_a_1291_);
lean_dec_ref(v_ctx_1079_);
v___x_1294_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16);
v___x_1295_ = l_Lean_MessageData_ofName(v_varName_1120_);
v___x_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22);
v___x_1298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = l_Lean_MessageData_ofExpr(v_a_1094_);
v___x_1300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1300_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___x_1303_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___redArg(v___x_1302_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1303_;
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_a_1094_);
lean_dec_ref(v_ctx_1079_);
v_a_1304_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1290_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1290_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
v___y_1271_ = v___x_1289_;
goto v___jp_1270_;
}
}
else
{
lean_dec(v_a_1130_);
v___y_1271_ = v___x_1287_;
goto v___jp_1270_;
}
v___jp_1131_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; lean_object* v___x_1153_; 
v___x_1138_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2));
lean_inc(v___y_1137_);
v___x_1139_ = l_Lean_mkIdent(v___y_1137_);
v___x_1140_ = l_Lean_mkIdent(v___y_1135_);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_mk_empty_array_with_capacity(v___x_1141_);
v___x_1143_ = lean_array_push(v___x_1142_, v___x_1140_);
v___x_1144_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__4));
v___x_1145_ = lean_box(2);
v___x_1146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v___x_1144_);
lean_ctor_set(v___x_1146_, 2, v___x_1143_);
v___x_1147_ = lean_unsigned_to_nat(2u);
v___x_1148_ = lean_mk_empty_array_with_capacity(v___x_1147_);
v___x_1149_ = lean_array_push(v___x_1148_, v___x_1139_);
v___x_1150_ = lean_array_push(v___x_1149_, v___x_1146_);
v___x_1151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1145_);
lean_ctor_set(v___x_1151_, 1, v___x_1138_);
lean_ctor_set(v___x_1151_, 2, v___x_1150_);
v___x_1152_ = 0;
lean_inc(v___x_1124_);
v___x_1153_ = l_Lean_Attribute_add(v___x_1124_, v___y_1137_, v___x_1151_, v___x_1152_, v___y_1136_, v___y_1132_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_dec_ref_known(v___x_1153_, 1);
v_p_1096_ = v___x_1124_;
v___y_1097_ = v___y_1134_;
v___y_1098_ = v___y_1133_;
v___y_1099_ = v___y_1136_;
v___y_1100_ = v___y_1132_;
goto v___jp_1095_;
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v___x_1124_);
lean_dec(v_a_1094_);
lean_dec_ref(v_ctx_1079_);
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
v___jp_1162_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_inc_ref_n(v_ctx_1079_, 2);
v___x_1169_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_1079_, v___y_1163_);
lean_dec_ref(v___y_1163_);
v___x_1170_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1079_, v_builtin_1080_, v_force_1081_, v___x_1169_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1172_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
lean_inc_ref(v___x_1127_);
v___x_1172_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v___x_1127_, v___f_1092_, v___x_1128_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1252_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1252_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1252_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1177_ = lean_box(0);
lean_inc_n(v___x_1124_, 2);
v___x_1178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1124_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
lean_ctor_set(v___x_1178_, 2, v_a_1173_);
v___x_1179_ = lean_box(0);
v___x_1180_ = 1;
v___x_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1124_);
lean_ctor_set(v___x_1181_, 1, v___x_1177_);
v___x_1182_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1182_, 0, v___x_1178_);
lean_ctor_set(v___x_1182_, 1, v_a_1171_);
lean_ctor_set(v___x_1182_, 2, v___x_1179_);
lean_ctor_set(v___x_1182_, 3, v___x_1181_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*4, v___x_1180_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set_tag(v___x_1175_, 1);
lean_ctor_set(v___x_1175_, 0, v___x_1182_);
v___x_1184_ = v___x_1175_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; lean_object* v_env_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; 
v___x_1185_ = lean_st_ref_get(v___y_1168_);
v_env_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc_ref(v_env_1186_);
lean_dec(v___x_1185_);
lean_inc(v_declName_1117_);
v___x_1187_ = l_Lean_isMarkedMeta(v_env_1186_, v_declName_1117_);
v___x_1188_ = l_Lean_addAndCompile(v___x_1184_, v___y_1164_, v___x_1187_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v___x_1189_; lean_object* v_env_1190_; lean_object* v_nextMacroScope_1191_; lean_object* v_ngen_1192_; lean_object* v_auxDeclNGen_1193_; lean_object* v_traceState_1194_; lean_object* v_recordedDeps_1195_; lean_object* v_messages_1196_; lean_object* v_infoState_1197_; lean_object* v_snapshotTasks_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref_known(v___x_1188_, 1);
v___x_1189_ = lean_st_ref_take(v___y_1168_);
v_env_1190_ = lean_ctor_get(v___x_1189_, 0);
v_nextMacroScope_1191_ = lean_ctor_get(v___x_1189_, 1);
v_ngen_1192_ = lean_ctor_get(v___x_1189_, 2);
v_auxDeclNGen_1193_ = lean_ctor_get(v___x_1189_, 3);
v_traceState_1194_ = lean_ctor_get(v___x_1189_, 4);
v_recordedDeps_1195_ = lean_ctor_get(v___x_1189_, 6);
v_messages_1196_ = lean_ctor_get(v___x_1189_, 7);
v_infoState_1197_ = lean_ctor_get(v___x_1189_, 8);
v_snapshotTasks_1198_ = lean_ctor_get(v___x_1189_, 9);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v___x_1189_, 5);
lean_dec(v_unused_1242_);
v___x_1200_ = v___x_1189_;
v_isShared_1201_ = v_isSharedCheck_1241_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_snapshotTasks_1198_);
lean_inc(v_infoState_1197_);
lean_inc(v_messages_1196_);
lean_inc(v_recordedDeps_1195_);
lean_inc(v_traceState_1194_);
lean_inc(v_auxDeclNGen_1193_);
lean_inc(v_ngen_1192_);
lean_inc(v_nextMacroScope_1191_);
lean_inc(v_env_1190_);
lean_dec(v___x_1189_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1241_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
lean_inc(v___x_1124_);
lean_inc_ref(v_combinatorAttr_1122_);
v___x_1202_ = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(v_combinatorAttr_1122_, v_env_1190_, v_declName_1117_, v___x_1124_);
v___x_1203_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 5, v___x_1203_);
lean_ctor_set(v___x_1200_, 0, v___x_1202_);
v___x_1205_ = v___x_1200_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_nextMacroScope_1191_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_ngen_1192_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_auxDeclNGen_1193_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_traceState_1194_);
lean_ctor_set(v_reuseFailAlloc_1240_, 5, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1240_, 6, v_recordedDeps_1195_);
lean_ctor_set(v_reuseFailAlloc_1240_, 7, v_messages_1196_);
lean_ctor_set(v_reuseFailAlloc_1240_, 8, v_infoState_1197_);
lean_ctor_set(v_reuseFailAlloc_1240_, 9, v_snapshotTasks_1198_);
v___x_1205_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_mctx_1208_; lean_object* v_zetaDeltaFVarIds_1209_; lean_object* v_postponed_1210_; lean_object* v_diag_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1238_; 
v___x_1206_ = lean_st_ref_put(v___y_1168_, v___x_1205_);
v___x_1207_ = lean_st_ref_take(v___y_1166_);
v_mctx_1208_ = lean_ctor_get(v___x_1207_, 0);
v_zetaDeltaFVarIds_1209_ = lean_ctor_get(v___x_1207_, 2);
v_postponed_1210_ = lean_ctor_get(v___x_1207_, 3);
v_diag_1211_ = lean_ctor_get(v___x_1207_, 4);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v___x_1207_, 1);
lean_dec(v_unused_1239_);
v___x_1213_ = v___x_1207_;
v_isShared_1214_ = v_isSharedCheck_1238_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_diag_1211_);
lean_inc(v_postponed_1210_);
lean_inc(v_zetaDeltaFVarIds_1209_);
lean_inc(v_mctx_1208_);
lean_dec(v___x_1207_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1238_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v___x_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_mctx_1208_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_zetaDeltaFVarIds_1209_);
lean_ctor_set(v_reuseFailAlloc_1237_, 3, v_postponed_1210_);
lean_ctor_set(v_reuseFailAlloc_1237_, 4, v_diag_1211_);
v___x_1217_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = lean_st_ref_put(v___y_1166_, v___x_1217_);
v___x_1219_ = l_Lean_Expr_isConst(v___x_1127_);
lean_dec_ref(v___x_1127_);
if (v___x_1219_ == 0)
{
lean_dec(v_a_1126_);
v_p_1096_ = v___x_1124_;
v___y_1097_ = v___y_1165_;
v___y_1098_ = v___y_1166_;
v___y_1099_ = v___y_1167_;
v___y_1100_ = v___y_1168_;
goto v___jp_1095_;
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = l_Lean_ConstantInfo_value_x21(v_a_1126_, v___x_1128_);
lean_dec(v_a_1126_);
v___x_1221_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v___x_1220_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
if (lean_obj_tag(v_a_1222_) == 1)
{
if (v_builtin_1080_ == 0)
{
lean_object* v_defn_1223_; lean_object* v_val_1224_; lean_object* v_name_1225_; 
v_defn_1223_ = lean_ctor_get(v_categoryAttr_1121_, 0);
v_val_1224_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_val_1224_);
lean_dec_ref_known(v_a_1222_, 1);
v_name_1225_ = lean_ctor_get(v_defn_1223_, 1);
lean_inc(v_name_1225_);
v___y_1132_ = v___y_1168_;
v___y_1133_ = v___y_1166_;
v___y_1134_ = v___y_1165_;
v___y_1135_ = v_val_1224_;
v___y_1136_ = v___y_1167_;
v___y_1137_ = v_name_1225_;
goto v___jp_1131_;
}
else
{
lean_object* v_defn_1226_; lean_object* v_val_1227_; lean_object* v_builtinName_1228_; 
v_defn_1226_ = lean_ctor_get(v_categoryAttr_1121_, 0);
v_val_1227_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v_a_1222_, 1);
v_builtinName_1228_ = lean_ctor_get(v_defn_1226_, 0);
lean_inc(v_builtinName_1228_);
v___y_1132_ = v___y_1168_;
v___y_1133_ = v___y_1166_;
v___y_1134_ = v___y_1165_;
v___y_1135_ = v_val_1227_;
v___y_1136_ = v___y_1167_;
v___y_1137_ = v_builtinName_1228_;
goto v___jp_1131_;
}
}
else
{
lean_dec(v_a_1222_);
v_p_1096_ = v___x_1124_;
v___y_1097_ = v___y_1165_;
v___y_1098_ = v___y_1166_;
v___y_1099_ = v___y_1167_;
v___y_1100_ = v___y_1168_;
goto v___jp_1095_;
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v___x_1124_);
lean_dec(v_a_1094_);
lean_dec_ref(v_ctx_1079_);
v_a_1229_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1221_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1221_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
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
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v___x_1127_);
lean_dec(v_a_1126_);
lean_dec(v___x_1124_);
lean_dec(v_declName_1117_);
lean_dec(v_a_1094_);
lean_dec_ref(v_ctx_1079_);
v_a_1243_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1188_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1188_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1171_);
lean_dec_ref(v___x_1127_);
lean_dec(v_a_1126_);
lean_dec(v___x_1124_);
lean_dec(v_declName_1117_);
lean_dec(v_a_1094_);
lean_dec_ref(v_ctx_1079_);
return v___x_1172_;
}
}
else
{
lean_dec_ref(v___x_1127_);
lean_dec(v_a_1126_);
lean_dec(v___x_1124_);
lean_dec(v_declName_1117_);
lean_dec(v_a_1094_);
lean_dec_ref(v___f_1092_);
lean_dec_ref(v_ctx_1079_);
return v___x_1170_;
}
}
v___jp_1253_:
{
if (v_force_1081_ == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1256_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12);
lean_inc(v_declName_1117_);
v___x_1257_ = l_Lean_MessageData_ofName(v_declName_1117_);
v___x_1258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1256_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___redArg(v___x_1260_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_dec_ref_known(v___x_1261_, 1);
v___y_1163_ = v___y_1254_;
v___y_1164_ = v___y_1255_;
v___y_1165_ = v_a_1083_;
v___y_1166_ = v_a_1084_;
v___y_1167_ = v_a_1085_;
v___y_1168_ = v_a_1086_;
goto v___jp_1162_;
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v___y_1254_);
lean_dec_ref(v___x_1127_);
lean_dec(v_a_1126_);
lean_dec(v___x_1124_);
lean_dec(v_declName_1117_);
lean_dec(v_a_1094_);
lean_dec_ref(v___f_1092_);
lean_dec_ref(v_ctx_1079_);
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
v___y_1163_ = v___y_1254_;
v___y_1164_ = v___y_1255_;
v___y_1165_ = v_a_1083_;
v___y_1166_ = v_a_1084_;
v___y_1167_ = v_a_1085_;
v___y_1168_ = v_a_1086_;
goto v___jp_1162_;
}
}
v___jp_1270_:
{
lean_object* v___x_1272_; 
lean_inc(v_a_1126_);
v___x_1272_ = l_Lean_ConstantInfo_value_x3f(v_a_1126_, v___x_1128_);
if (lean_obj_tag(v___x_1272_) == 1)
{
lean_object* v_val_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; 
v_val_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = 1;
v___x_1275_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1119_, v_declName_1117_);
lean_dec_ref(v_env_1119_);
if (lean_obj_tag(v___x_1275_) == 0)
{
if (v___y_1271_ == 0)
{
v___y_1254_ = v_val_1273_;
v___y_1255_ = v___x_1274_;
goto v___jp_1253_;
}
else
{
v___y_1163_ = v_val_1273_;
v___y_1164_ = v___x_1274_;
v___y_1165_ = v_a_1083_;
v___y_1166_ = v_a_1084_;
v___y_1167_ = v_a_1085_;
v___y_1168_ = v_a_1086_;
goto v___jp_1162_;
}
}
else
{
lean_dec_ref_known(v___x_1275_, 1);
v___y_1254_ = v_val_1273_;
v___y_1255_ = v___x_1274_;
goto v___jp_1253_;
}
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_inc(v_varName_1120_);
lean_dec(v___x_1272_);
lean_dec_ref(v___x_1127_);
lean_dec(v_a_1126_);
lean_dec(v___x_1124_);
lean_dec_ref(v_env_1119_);
lean_dec(v_declName_1117_);
lean_dec_ref(v___f_1092_);
lean_dec_ref(v_ctx_1079_);
v___x_1276_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16);
v___x_1277_ = l_Lean_MessageData_ofName(v_varName_1120_);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = l_Lean_MessageData_ofExpr(v_a_1094_);
v___x_1282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___redArg(v___x_1284_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1285_;
}
}
}
else
{
lean_dec_ref(v___x_1127_);
lean_dec(v_a_1126_);
lean_dec(v___x_1124_);
lean_dec_ref(v_env_1119_);
lean_dec(v_declName_1117_);
lean_dec(v_a_1094_);
lean_dec_ref(v___f_1092_);
lean_dec_ref(v_ctx_1079_);
return v___x_1129_;
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v___x_1124_);
lean_dec_ref(v_env_1119_);
lean_dec(v_declName_1117_);
lean_dec(v_a_1094_);
lean_dec_ref(v___f_1092_);
lean_dec_ref(v_ctx_1079_);
v_a_1312_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1125_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1125_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_object* v_val_1320_; 
lean_dec_ref(v_env_1119_);
lean_dec(v_declName_1117_);
lean_dec_ref(v___f_1092_);
v_val_1320_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_val_1320_);
lean_dec_ref_known(v___x_1123_, 1);
v_p_1096_ = v_val_1320_;
v___y_1097_ = v_a_1083_;
v___y_1098_ = v_a_1084_;
v___y_1099_ = v_a_1085_;
v___y_1100_ = v_a_1086_;
goto v___jp_1095_;
}
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec_ref(v___x_1116_);
lean_dec_ref(v___f_1092_);
lean_dec_ref(v_ctx_1079_);
v___x_1321_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__24, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__24_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__24);
v___x_1322_ = l_Lean_MessageData_ofExpr(v_a_1094_);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1321_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1323_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___redArg(v___x_1325_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1326_;
}
}
}
v___jp_1095_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___f_1105_; lean_object* v___x_1106_; 
v___x_1101_ = lean_box(0);
v___x_1102_ = l_Lean_mkConst(v_p_1096_, v___x_1101_);
v___x_1103_ = lean_box(v_builtin_1080_);
v___x_1104_ = lean_box(v_force_1081_);
lean_inc_ref(v___x_1102_);
v___f_1105_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed), 12, 5);
lean_closure_set(v___f_1105_, 0, v_a_1094_);
lean_closure_set(v___f_1105_, 1, v_ctx_1079_);
lean_closure_set(v___f_1105_, 2, v___x_1103_);
lean_closure_set(v___f_1105_, 3, v___x_1104_);
lean_closure_set(v___f_1105_, 4, v___x_1102_);
lean_inc(v___y_1100_);
lean_inc_ref(v___y_1099_);
lean_inc(v___y_1098_);
lean_inc_ref(v___y_1097_);
v___x_1106_ = lean_infer_type(v___x_1102_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; uint8_t v___x_1108_; lean_object* v___x_1109_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1106_, 1);
v___x_1108_ = 0;
v___x_1109_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_1107_, v___f_1105_, v___x_1108_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1109_;
}
else
{
lean_dec_ref(v___f_1105_);
return v___x_1106_;
}
}
}
else
{
lean_dec_ref(v___f_1092_);
lean_dec_ref(v___f_1091_);
lean_dec_ref(v_ctx_1079_);
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(lean_object* v_ctx_1327_, uint8_t v_builtin_1328_, uint8_t v_force_1329_, lean_object* v_x_1330_, lean_object* v_b_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1327_, v_builtin_1328_, v_force_1329_, v_b_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___boxed(lean_object* v_upperBound_1338_, lean_object* v_params_1339_, lean_object* v___x_1340_, lean_object* v_ctx_1341_, lean_object* v_builtin_1342_, lean_object* v_force_1343_, lean_object* v_a_1344_, lean_object* v_b_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v_builtin_boxed_1351_; uint8_t v_force_boxed_1352_; lean_object* v_res_1353_; 
v_builtin_boxed_1351_ = lean_unbox(v_builtin_1342_);
v_force_boxed_1352_ = lean_unbox(v_force_1343_);
v_res_1353_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v_upperBound_1338_, v_params_1339_, v___x_1340_, v_ctx_1341_, v_builtin_boxed_1351_, v_force_boxed_1352_, v_a_1344_, v_b_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec_ref(v___x_1340_);
lean_dec_ref(v_params_1339_);
lean_dec(v_upperBound_1338_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___boxed(lean_object* v_ctx_1354_, lean_object* v_builtin_1355_, lean_object* v_force_1356_, lean_object* v_e_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
uint8_t v_builtin_boxed_1363_; uint8_t v_force_boxed_1364_; lean_object* v_res_1365_; 
v_builtin_boxed_1363_ = lean_unbox(v_builtin_1355_);
v_force_boxed_1364_ = lean_unbox(v_force_1356_);
v_res_1365_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1354_, v_builtin_boxed_1363_, v_force_boxed_1364_, v_e_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr(lean_object* v_00_u03b1_1366_, lean_object* v_ctx_1367_, uint8_t v_builtin_1368_, uint8_t v_force_1369_, lean_object* v_e_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1367_, v_builtin_1368_, v_force_1369_, v_e_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_ctx_1378_, lean_object* v_builtin_1379_, lean_object* v_force_1380_, lean_object* v_e_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
uint8_t v_builtin_boxed_1387_; uint8_t v_force_boxed_1388_; lean_object* v_res_1389_; 
v_builtin_boxed_1387_ = lean_unbox(v_builtin_1379_);
v_force_boxed_1388_ = lean_unbox(v_force_1380_);
v_res_1389_ = l_Lean_ParserCompiler_compileParserExpr(v_00_u03b1_1377_, v_ctx_1378_, v_builtin_boxed_1387_, v_force_boxed_1388_, v_e_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(lean_object* v_00_u03b1_1390_, lean_object* v_ctx_1391_, lean_object* v_as_1392_, size_t v_i_1393_, size_t v_stop_1394_, lean_object* v_b_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_1391_, v_as_1392_, v_i_1393_, v_stop_1394_, v_b_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___boxed(lean_object* v_00_u03b1_1402_, lean_object* v_ctx_1403_, lean_object* v_as_1404_, lean_object* v_i_1405_, lean_object* v_stop_1406_, lean_object* v_b_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
size_t v_i_boxed_1413_; size_t v_stop_boxed_1414_; lean_object* v_res_1415_; 
v_i_boxed_1413_ = lean_unbox_usize(v_i_1405_);
lean_dec(v_i_1405_);
v_stop_boxed_1414_ = lean_unbox_usize(v_stop_1406_);
lean_dec(v_stop_1406_);
v_res_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(v_00_u03b1_1402_, v_ctx_1403_, v_as_1404_, v_i_boxed_1413_, v_stop_boxed_1414_, v_b_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec_ref(v_as_1404_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(lean_object* v_upperBound_1416_, lean_object* v_params_1417_, lean_object* v___x_1418_, lean_object* v_00_u03b1_1419_, lean_object* v_ctx_1420_, uint8_t v_builtin_1421_, uint8_t v_force_1422_, lean_object* v_inst_1423_, lean_object* v_R_1424_, lean_object* v_a_1425_, lean_object* v_b_1426_, lean_object* v_c_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v_upperBound_1416_, v_params_1417_, v___x_1418_, v_ctx_1420_, v_builtin_1421_, v_force_1422_, v_a_1425_, v_b_1426_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1434_ = _args[0];
lean_object* v_params_1435_ = _args[1];
lean_object* v___x_1436_ = _args[2];
lean_object* v_00_u03b1_1437_ = _args[3];
lean_object* v_ctx_1438_ = _args[4];
lean_object* v_builtin_1439_ = _args[5];
lean_object* v_force_1440_ = _args[6];
lean_object* v_inst_1441_ = _args[7];
lean_object* v_R_1442_ = _args[8];
lean_object* v_a_1443_ = _args[9];
lean_object* v_b_1444_ = _args[10];
lean_object* v_c_1445_ = _args[11];
lean_object* v___y_1446_ = _args[12];
lean_object* v___y_1447_ = _args[13];
lean_object* v___y_1448_ = _args[14];
lean_object* v___y_1449_ = _args[15];
lean_object* v___y_1450_ = _args[16];
_start:
{
uint8_t v_builtin_boxed_1451_; uint8_t v_force_boxed_1452_; lean_object* v_res_1453_; 
v_builtin_boxed_1451_ = lean_unbox(v_builtin_1439_);
v_force_boxed_1452_ = lean_unbox(v_force_1440_);
v_res_1453_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(v_upperBound_1434_, v_params_1435_, v___x_1436_, v_00_u03b1_1437_, v_ctx_1438_, v_builtin_boxed_1451_, v_force_boxed_1452_, v_inst_1441_, v_R_1442_, v_a_1443_, v_b_1444_, v_c_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v_params_1435_);
lean_dec(v_upperBound_1434_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(lean_object* v_00_u03b2_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg___boxed(lean_object* v___dummy_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg();
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4(lean_object* v_00_u03b2_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5(lean_object* v_00_u03b1_1462_, lean_object* v_msg_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___redArg(v_msg_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5___boxed(lean_object* v_00_u03b1_1470_, lean_object* v_msg_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__5(v_00_u03b1_1470_, v_msg_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(lean_object* v_00_u03b1_1478_, lean_object* v_constName_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1486_, lean_object* v_constName_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(v_00_u03b1_1486_, v_constName_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_1494_, lean_object* v_ref_1495_, lean_object* v_constName_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_1495_, v_constName_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1503_, lean_object* v_ref_1504_, lean_object* v_constName_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(v_00_u03b1_1503_, v_ref_1504_, v_constName_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v_ref_1504_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9(lean_object* v_00_u03b1_1512_, lean_object* v_ref_1513_, lean_object* v_msg_1514_, lean_object* v_declHint_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9___redArg(v_ref_1513_, v_msg_1514_, v_declHint_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9___boxed(lean_object* v_00_u03b1_1522_, lean_object* v_ref_1523_, lean_object* v_msg_1524_, lean_object* v_declHint_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9(v_00_u03b1_1522_, v_ref_1523_, v_msg_1524_, v_declHint_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v_ref_1523_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11(lean_object* v_msg_1532_, lean_object* v_declHint_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg(v_msg_1532_, v_declHint_1533_, v___y_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___boxed(lean_object* v_msg_1540_, lean_object* v_declHint_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11(v_msg_1540_, v_declHint_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__11(lean_object* v_00_u03b1_1548_, lean_object* v_ref_1549_, lean_object* v_msg_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__11___redArg(v_ref_1549_, v_msg_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1557_, lean_object* v_ref_1558_, lean_object* v_msg_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__11(v_00_u03b1_1557_, v_ref_1558_, v_msg_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v_ref_1558_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(lean_object* v_ctx_1566_, uint8_t v_builtin_1567_, lean_object* v_x_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_p_1575_; lean_object* v_psep_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; 
switch(lean_obj_tag(v_x_1568_))
{
case 1:
{
lean_object* v_p_1583_; 
v_p_1583_ = lean_ctor_get(v_x_1568_, 1);
lean_inc_ref(v_p_1583_);
lean_dec_ref_known(v_x_1568_, 2);
v_x_1568_ = v_p_1583_;
goto _start;
}
case 2:
{
lean_object* v_p_u2081_1585_; lean_object* v_p_u2082_1586_; lean_object* v___x_1587_; 
v_p_u2081_1585_ = lean_ctor_get(v_x_1568_, 1);
lean_inc_ref(v_p_u2081_1585_);
v_p_u2082_1586_ = lean_ctor_get(v_x_1568_, 2);
lean_inc_ref(v_p_u2082_1586_);
lean_dec_ref_known(v_x_1568_, 3);
lean_inc_ref(v_ctx_1566_);
v___x_1587_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1566_, v_builtin_1567_, v_p_u2081_1585_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_dec_ref_known(v___x_1587_, 1);
v_x_1568_ = v_p_u2082_1586_;
goto _start;
}
else
{
lean_dec_ref(v_p_u2082_1586_);
lean_dec_ref(v_ctx_1566_);
return v___x_1587_;
}
}
case 3:
{
lean_object* v_p_1589_; 
v_p_1589_ = lean_ctor_get(v_x_1568_, 2);
lean_inc_ref(v_p_1589_);
lean_dec_ref_known(v_x_1568_, 3);
v_x_1568_ = v_p_1589_;
goto _start;
}
case 4:
{
lean_object* v_p_1591_; 
v_p_1591_ = lean_ctor_get(v_x_1568_, 3);
lean_inc_ref(v_p_1591_);
lean_dec_ref_known(v_x_1568_, 4);
v_x_1568_ = v_p_1591_;
goto _start;
}
case 8:
{
lean_object* v_declName_1593_; uint8_t v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_declName_1593_ = lean_ctor_get(v_x_1568_, 0);
lean_inc(v_declName_1593_);
lean_dec_ref_known(v_x_1568_, 1);
v___x_1594_ = 0;
v___x_1595_ = lean_box(0);
v___x_1596_ = l_Lean_mkConst(v_declName_1593_, v___x_1595_);
v___x_1597_ = lean_box(0);
v___x_1598_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1566_, v_builtin_1567_, v___x_1594_, v___x_1596_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v___x_1598_, 0);
lean_dec(v_unused_1606_);
v___x_1600_ = v___x_1598_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_dec(v___x_1598_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1597_);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1597_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_a_1607_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1598_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1598_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
case 9:
{
lean_object* v_p_1615_; 
v_p_1615_ = lean_ctor_get(v_x_1568_, 2);
lean_inc_ref(v_p_1615_);
lean_dec_ref_known(v_x_1568_, 3);
v_x_1568_ = v_p_1615_;
goto _start;
}
case 10:
{
lean_object* v_p_1617_; lean_object* v_psep_1618_; 
v_p_1617_ = lean_ctor_get(v_x_1568_, 0);
lean_inc_ref(v_p_1617_);
v_psep_1618_ = lean_ctor_get(v_x_1568_, 2);
lean_inc_ref(v_psep_1618_);
lean_dec_ref_known(v_x_1568_, 3);
v_p_1575_ = v_p_1617_;
v_psep_1576_ = v_psep_1618_;
v___y_1577_ = v_a_1569_;
v___y_1578_ = v_a_1570_;
v___y_1579_ = v_a_1571_;
v___y_1580_ = v_a_1572_;
goto v___jp_1574_;
}
case 11:
{
lean_object* v_p_1619_; lean_object* v_psep_1620_; 
v_p_1619_ = lean_ctor_get(v_x_1568_, 0);
lean_inc_ref(v_p_1619_);
v_psep_1620_ = lean_ctor_get(v_x_1568_, 2);
lean_inc_ref(v_psep_1620_);
lean_dec_ref_known(v_x_1568_, 3);
v_p_1575_ = v_p_1619_;
v_psep_1576_ = v_psep_1620_;
v___y_1577_ = v_a_1569_;
v___y_1578_ = v_a_1570_;
v___y_1579_ = v_a_1571_;
v___y_1580_ = v_a_1572_;
goto v___jp_1574_;
}
default: 
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v_x_1568_);
lean_dec_ref(v_ctx_1566_);
v___x_1621_ = lean_box(0);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
v___jp_1574_:
{
lean_object* v___x_1581_; 
lean_inc_ref(v_ctx_1566_);
v___x_1581_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1566_, v_builtin_1567_, v_p_1575_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_dec_ref_known(v___x_1581_, 1);
v_x_1568_ = v_psep_1576_;
v_a_1569_ = v___y_1577_;
v_a_1570_ = v___y_1578_;
v_a_1571_ = v___y_1579_;
v_a_1572_ = v___y_1580_;
goto _start;
}
else
{
lean_dec_ref(v_psep_1576_);
lean_dec_ref(v_ctx_1566_);
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg___boxed(lean_object* v_ctx_1623_, lean_object* v_builtin_1624_, lean_object* v_x_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
uint8_t v_builtin_boxed_1631_; lean_object* v_res_1632_; 
v_builtin_boxed_1631_ = lean_unbox(v_builtin_1624_);
v_res_1632_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1623_, v_builtin_boxed_1631_, v_x_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers(lean_object* v_00_u03b1_1633_, lean_object* v_ctx_1634_, uint8_t v_builtin_1635_, lean_object* v_x_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1634_, v_builtin_1635_, v_x_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___boxed(lean_object* v_00_u03b1_1643_, lean_object* v_ctx_1644_, lean_object* v_builtin_1645_, lean_object* v_x_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
uint8_t v_builtin_boxed_1652_; lean_object* v_res_1653_; 
v_builtin_boxed_1652_ = lean_unbox(v_builtin_1645_);
v_res_1653_ = l_Lean_ParserCompiler_compileEmbeddedParsers(v_00_u03b1_1643_, v_ctx_1644_, v_builtin_boxed_1652_, v_x_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
return v_res_1653_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_box(0);
v___x_1655_ = l_Lean_Elab_abortCommandExceptionId;
v___x_1656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v___x_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg(){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0);
v___x_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___boxed(lean_object* v___y_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(lean_object* v_msgData_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; lean_object* v_toCold_1667_; lean_object* v_env_1668_; lean_object* v_options_1669_; uint8_t v___x_1670_; lean_object* v_env_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1666_ = lean_st_ref_get(v___y_1664_);
v_toCold_1667_ = lean_ctor_get(v___y_1663_, 0);
v_env_1668_ = lean_ctor_get(v___x_1666_, 0);
lean_inc_ref(v_env_1668_);
lean_dec(v___x_1666_);
v_options_1669_ = lean_ctor_get(v_toCold_1667_, 2);
v___x_1670_ = 0;
v_env_1671_ = l_Lean_Environment_setRecordingDeps(v_env_1668_, v___x_1670_);
v___x_1672_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__1);
v___x_1673_ = lean_unsigned_to_nat(32u);
v___x_1674_ = lean_mk_empty_array_with_capacity(v___x_1673_);
lean_dec_ref(v___x_1674_);
v___x_1675_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__4);
lean_inc_ref(v_options_1669_);
v___x_1676_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1676_, 0, v_env_1671_);
lean_ctor_set(v___x_1676_, 1, v___x_1672_);
lean_ctor_set(v___x_1676_, 2, v___x_1675_);
lean_ctor_set(v___x_1676_, 3, v_options_1669_);
v___x_1677_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v_msgData_1662_);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9___boxed(lean_object* v_msgData_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(v_msgData_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(lean_object* v_msg_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_ref_1688_; lean_object* v___x_1689_; lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1698_; 
v_ref_1688_ = lean_ctor_get(v___y_1685_, 2);
v___x_1689_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(v_msg_1684_, v___y_1685_, v___y_1686_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
lean_inc(v_ref_1688_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_ref_1688_);
lean_ctor_set(v___x_1694_, 1, v_a_1690_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 1);
lean_ctor_set(v___x_1692_, 0, v___x_1694_);
v___x_1696_ = v___x_1692_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msg_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(lean_object* v_x_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
if (lean_obj_tag(v_x_1704_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_a_1708_ = lean_ctor_get(v_x_1704_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v_x_1704_, 1);
v___x_1709_ = l_Lean_stringToMessageData(v_a_1708_);
v___x_1710_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v___x_1709_, v___y_1705_, v___y_1706_);
return v___x_1710_;
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
v_a_1711_ = lean_ctor_get(v_x_1704_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_x_1704_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v_x_1704_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v_x_1704_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 0);
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg___boxed(lean_object* v_x_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v_x_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(lean_object* v_typeName_1724_, lean_object* v_constName_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v_env_1730_; uint8_t v___x_1731_; 
v___x_1729_ = lean_st_ref_get(v___y_1727_);
v_env_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc_ref(v_env_1730_);
lean_dec(v___x_1729_);
lean_inc(v_constName_1725_);
v___x_1731_ = lean_has_compile_error(v_env_1730_, v_constName_1725_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v_env_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1732_ = lean_st_ref_get(v___y_1727_);
v_env_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc_ref(v_env_1733_);
lean_dec(v___x_1732_);
v___x_1734_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1726_);
v___x_1735_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1733_, v___x_1734_, v_typeName_1724_, v_constName_1725_);
lean_dec_ref(v___x_1734_);
v___x_1736_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v___x_1735_, v___y_1726_, v___y_1727_);
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v___x_1738_; lean_object* v_env_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_dec_ref_known(v___x_1737_, 1);
v___x_1738_ = lean_st_ref_get(v___y_1727_);
v_env_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc_ref(v_env_1739_);
lean_dec(v___x_1738_);
v___x_1740_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1726_);
v___x_1741_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1739_, v___x_1740_, v_typeName_1724_, v_constName_1725_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v___x_1741_, v___y_1726_, v___y_1727_);
return v___x_1742_;
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec(v_constName_1725_);
lean_dec(v_typeName_1724_);
v_a_1743_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1737_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1737_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg___boxed(lean_object* v_typeName_1751_, lean_object* v_constName_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v_typeName_1751_, v_constName_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(lean_object* v_ref_1757_, lean_object* v_msg_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_toCold_1762_; lean_object* v_currRecDepth_1763_; lean_object* v_ref_1764_; uint16_t v_optionFlags_1765_; uint8_t v_suppressElabErrors_1766_; uint8_t v_checkDeprecated_1767_; uint8_t v_isRecordingDeps_1768_; lean_object* v_ref_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_toCold_1762_ = lean_ctor_get(v___y_1759_, 0);
v_currRecDepth_1763_ = lean_ctor_get(v___y_1759_, 1);
v_ref_1764_ = lean_ctor_get(v___y_1759_, 2);
v_optionFlags_1765_ = lean_ctor_get_uint16(v___y_1759_, sizeof(void*)*3);
v_suppressElabErrors_1766_ = lean_ctor_get_uint8(v___y_1759_, sizeof(void*)*3 + 2);
v_checkDeprecated_1767_ = lean_ctor_get_uint8(v___y_1759_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1768_ = lean_ctor_get_uint8(v___y_1759_, sizeof(void*)*3 + 4);
v_ref_1769_ = l_Lean_replaceRef(v_ref_1757_, v_ref_1764_);
lean_inc(v_currRecDepth_1763_);
lean_inc_ref(v_toCold_1762_);
v___x_1770_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1770_, 0, v_toCold_1762_);
lean_ctor_set(v___x_1770_, 1, v_currRecDepth_1763_);
lean_ctor_set(v___x_1770_, 2, v_ref_1769_);
lean_ctor_set_uint16(v___x_1770_, sizeof(void*)*3, v_optionFlags_1765_);
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*3 + 2, v_suppressElabErrors_1766_);
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*3 + 3, v_checkDeprecated_1767_);
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*3 + 4, v_isRecordingDeps_1768_);
v___x_1771_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_1758_, v___x_1770_, v___y_1760_);
lean_dec_ref_known(v___x_1770_, 3);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg___boxed(lean_object* v_ref_1772_, lean_object* v_msg_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_1772_, v_msg_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v_ref_1772_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(lean_object* v_msg_1778_, lean_object* v_declHint_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v_env_1784_; uint8_t v___x_1785_; 
v___x_1782_ = lean_box(0);
v___x_1783_ = lean_st_ref_get(v___y_1780_);
v_env_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc_ref(v_env_1784_);
lean_dec(v___x_1783_);
v___x_1785_ = l_Lean_Name_isAnonymous(v_declHint_1779_);
if (v___x_1785_ == 0)
{
uint8_t v_isExporting_1786_; 
v_isExporting_1786_ = lean_ctor_get_uint8(v_env_1784_, sizeof(void*)*13);
if (v_isExporting_1786_ == 0)
{
lean_object* v___x_1787_; 
lean_dec_ref(v_env_1784_);
lean_dec(v_declHint_1779_);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v_msg_1778_);
return v___x_1787_;
}
else
{
lean_object* v___x_1788_; uint8_t v___x_1789_; 
lean_inc_ref(v_env_1784_);
v___x_1788_ = l_Lean_Environment_setExporting(v_env_1784_, v___x_1785_);
lean_inc(v_declHint_1779_);
lean_inc_ref(v___x_1788_);
v___x_1789_ = l_Lean_Environment_contains(v___x_1788_, v_declHint_1779_, v_isExporting_1786_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; 
lean_dec_ref(v___x_1788_);
lean_dec_ref(v_env_1784_);
lean_dec(v_declHint_1779_);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_msg_1778_);
return v___x_1790_;
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v_c_1798_; lean_object* v___x_1799_; 
v___x_1791_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__1);
v___x_1792_ = lean_unsigned_to_nat(32u);
v___x_1793_ = lean_mk_empty_array_with_capacity(v___x_1792_);
lean_dec_ref(v___x_1793_);
v___x_1794_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__4);
v___x_1795_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1788_);
v___x_1796_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1788_);
lean_ctor_set(v___x_1796_, 1, v___x_1791_);
lean_ctor_set(v___x_1796_, 2, v___x_1794_);
lean_ctor_set(v___x_1796_, 3, v___x_1795_);
lean_inc(v_declHint_1779_);
v___x_1797_ = l_Lean_MessageData_ofConstName(v_declHint_1779_, v___x_1785_);
v_c_1798_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1798_, 0, v___x_1796_);
lean_ctor_set(v_c_1798_, 1, v___x_1797_);
v___x_1799_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1788_, v_declHint_1779_);
lean_dec_ref(v___x_1788_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec_ref(v_env_1784_);
lean_dec(v_declHint_1779_);
v___x_1800_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v_c_1798_);
v___x_1802_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__8);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1801_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Lean_MessageData_note(v___x_1803_);
v___x_1805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1805_, 0, v_msg_1778_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
else
{
lean_object* v_val_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1860_; 
v_val_1807_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1809_ = v___x_1799_;
v_isShared_1810_ = v_isSharedCheck_1860_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_val_1807_);
lean_dec(v___x_1799_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1860_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v_modules_1812_; lean_object* v_moduleNames_1813_; lean_object* v_mod_1814_; uint8_t v___x_1829_; 
v___x_1811_ = l_Lean_Environment_header(v_env_1784_);
lean_dec_ref(v_env_1784_);
v_modules_1812_ = lean_ctor_get(v___x_1811_, 3);
lean_inc_ref(v_modules_1812_);
v_moduleNames_1813_ = lean_ctor_get(v___x_1811_, 4);
lean_inc_ref(v_moduleNames_1813_);
lean_dec_ref(v___x_1811_);
v_mod_1814_ = lean_array_get(v___x_1782_, v_moduleNames_1813_, v_val_1807_);
lean_dec_ref(v_moduleNames_1813_);
v___x_1829_ = l_Lean_isPrivateName(v_declHint_1779_);
lean_dec(v_declHint_1779_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = lean_array_get_size(v_modules_1812_);
v___x_1831_ = lean_nat_dec_lt(v_val_1807_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_dec_ref(v_modules_1812_);
lean_dec(v_val_1807_);
goto v___jp_1815_;
}
else
{
lean_object* v___x_1832_; lean_object* v_toImport_1833_; uint8_t v_isExported_1834_; 
v___x_1832_ = lean_array_fget(v_modules_1812_, v_val_1807_);
lean_dec(v_val_1807_);
lean_dec_ref(v_modules_1812_);
v_toImport_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc_ref(v_toImport_1833_);
lean_dec(v___x_1832_);
v_isExported_1834_ = lean_ctor_get_uint8(v_toImport_1833_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1833_);
if (v_isExported_1834_ == 0)
{
goto v___jp_1815_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_del_object(v___x_1809_);
v___x_1835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__16);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v_c_1798_);
v___x_1837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__18);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_MessageData_ofName(v_mod_1814_);
lean_inc_ref(v___x_1839_);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__20);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v___x_1839_);
v___x_1844_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__22);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1843_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = l_Lean_MessageData_note(v___x_1845_);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v_msg_1778_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
}
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec_ref(v_modules_1812_);
lean_del_object(v___x_1809_);
lean_dec(v_val_1807_);
v___x_1849_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__6);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v_c_1798_);
v___x_1851_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__24);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Lean_MessageData_ofName(v_mod_1814_);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__26);
v___x_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = l_Lean_MessageData_note(v___x_1856_);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v_msg_1778_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
return v___x_1859_;
}
v___jp_1815_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1816_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__10);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set(v___x_1817_, 1, v_c_1798_);
v___x_1818_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__12);
v___x_1819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = l_Lean_MessageData_ofName(v_mod_1814_);
v___x_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__14);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = l_Lean_MessageData_note(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_msg_1778_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1825_);
v___x_1827_ = v___x_1809_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1861_; 
lean_dec_ref(v_env_1784_);
lean_dec(v_declHint_1779_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_msg_1778_);
return v___x_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg___boxed(lean_object* v_msg_1862_, lean_object* v_declHint_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_1862_, v_declHint_1863_, v___y_1864_);
lean_dec(v___y_1864_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(lean_object* v_msg_1867_, lean_object* v_declHint_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1882_; 
v___x_1872_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_1867_, v_declHint_1868_, v___y_1870_);
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1882_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1877_ = l_Lean_unknownIdentifierMessageTag;
v___x_1878_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v_a_1873_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1878_);
v___x_1880_ = v___x_1875_;
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
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8___boxed(lean_object* v_msg_1883_, lean_object* v_declHint_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_1883_, v_declHint_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_ref_1889_, lean_object* v_msg_1890_, lean_object* v_declHint_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v_a_1896_; lean_object* v___x_1897_; 
v___x_1895_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_1890_, v_declHint_1891_, v___y_1892_, v___y_1893_);
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___x_1895_);
v___x_1897_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_1889_, v_a_1896_, v___y_1892_, v___y_1893_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_ref_1898_, lean_object* v_msg_1899_, lean_object* v_declHint_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1898_, v_msg_1899_, v_declHint_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v_ref_1898_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1905_, lean_object* v_constName_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1910_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_1911_ = 0;
lean_inc(v_constName_1906_);
v___x_1912_ = l_Lean_MessageData_ofConstName(v_constName_1906_, v___x_1911_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1910_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1905_, v___x_1915_, v_constName_1906_, v___y_1907_, v___y_1908_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1917_, lean_object* v_constName_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_1917_, v_constName_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v_ref_1917_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(lean_object* v_constName_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_ref_1927_; lean_object* v___x_1928_; 
v_ref_1927_ = lean_ctor_get(v___y_1924_, 2);
v___x_1928_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_1927_, v_constName_1923_, v___y_1924_, v___y_1925_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(lean_object* v_constName_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v_env_1939_; uint8_t v___x_1940_; lean_object* v___x_1941_; 
v___x_1938_ = lean_st_ref_get(v___y_1936_);
v_env_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc_ref(v_env_1939_);
lean_dec(v___x_1938_);
v___x_1940_ = 0;
lean_inc(v_constName_1934_);
v___x_1941_ = l_Lean_Environment_find_x3f(v_env_1939_, v_constName_1934_, v___x_1940_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_1934_, v___y_1935_, v___y_1936_);
return v___x_1942_;
}
else
{
lean_object* v_val_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_constName_1934_);
v_val_1943_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1941_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_val_1943_);
lean_dec(v___x_1941_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set_tag(v___x_1945_, 0);
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_val_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0___boxed(lean_object* v_constName_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(v_constName_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
return v_res_1955_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___redArg___closed__0);
v___x_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
return v___x_1957_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1958_ = lean_box(1);
v___x_1959_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3);
v___x_1960_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v___x_1959_);
lean_ctor_set(v___x_1961_, 2, v___x_1958_);
return v___x_1961_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1964_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
lean_ctor_set(v___x_1966_, 2, v___x_1965_);
lean_ctor_set(v___x_1966_, 3, v___x_1965_);
lean_ctor_set(v___x_1966_, 4, v___x_1964_);
lean_ctor_set(v___x_1966_, 5, v___x_1964_);
lean_ctor_set(v___x_1966_, 6, v___x_1964_);
lean_ctor_set(v___x_1966_, 7, v___x_1964_);
lean_ctor_set(v___x_1966_, 8, v___x_1964_);
lean_ctor_set(v___x_1966_, 9, v___x_1964_);
lean_ctor_set(v___x_1966_, 10, v___x_1964_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = lean_unsigned_to_nat(0u);
v___x_1970_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
lean_ctor_set(v___x_1971_, 2, v___x_1969_);
return v___x_1971_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1972_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5);
v___x_1973_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4);
v___x_1974_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1975_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
v___x_1976_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v___x_1974_);
lean_ctor_set(v___x_1976_, 2, v___x_1973_);
lean_ctor_set(v___x_1976_, 3, v___x_1974_);
lean_ctor_set(v___x_1976_, 4, v___x_1974_);
lean_ctor_set(v___x_1976_, 5, v___x_1974_);
lean_ctor_set(v___x_1976_, 6, v___x_1972_);
return v___x_1976_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
lean_ctor_set(v___x_1978_, 2, v___x_1977_);
lean_ctor_set(v___x_1978_, 3, v___x_1977_);
lean_ctor_set(v___x_1978_, 4, v___x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(lean_object* v___x_1987_, lean_object* v_ctx_1988_, uint8_t v_builtin_1989_, lean_object* v_constName_1990_, lean_object* v_catName_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
uint8_t v___y_1996_; uint8_t v___y_1997_; lean_object* v_a_1998_; lean_object* v___x_2027_; 
lean_inc(v_constName_1990_);
v___x_2027_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(v_constName_1990_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; uint8_t v___y_2032_; uint8_t v___x_2060_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2029_ = l_Lean_ConstantInfo_type(v_a_2028_);
lean_dec(v_a_2028_);
v___x_2030_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9));
v___x_2060_ = l_Lean_Expr_isConstOf(v___x_2029_, v___x_2030_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11));
v___x_2062_ = l_Lean_Expr_isConstOf(v___x_2029_, v___x_2061_);
lean_dec_ref(v___x_2029_);
if (v___x_2062_ == 0)
{
uint8_t v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; uint8_t v___x_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; uint64_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2063_ = 1;
v___x_2064_ = l_Lean_Name_isAnonymous(v_catName_1991_);
v___x_2065_ = lean_box(0);
v___x_2066_ = l_Lean_mkConst(v_constName_1990_, v___x_2065_);
v___x_2067_ = 1;
v___x_2068_ = 0;
v___x_2069_ = 2;
v___x_2070_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_2070_, 0, v___x_2062_);
lean_ctor_set_uint8(v___x_2070_, 1, v___x_2062_);
lean_ctor_set_uint8(v___x_2070_, 2, v___x_2062_);
lean_ctor_set_uint8(v___x_2070_, 3, v___x_2062_);
lean_ctor_set_uint8(v___x_2070_, 4, v___x_2062_);
lean_ctor_set_uint8(v___x_2070_, 5, v___x_2063_);
lean_ctor_set_uint8(v___x_2070_, 6, v___x_2063_);
lean_ctor_set_uint8(v___x_2070_, 7, v___x_2062_);
lean_ctor_set_uint8(v___x_2070_, 8, v___x_2063_);
lean_ctor_set_uint8(v___x_2070_, 9, v___x_2067_);
lean_ctor_set_uint8(v___x_2070_, 10, v___x_2068_);
lean_ctor_set_uint8(v___x_2070_, 11, v___x_2063_);
lean_ctor_set_uint8(v___x_2070_, 12, v___x_2063_);
lean_ctor_set_uint8(v___x_2070_, 13, v___x_2063_);
lean_ctor_set_uint8(v___x_2070_, 14, v___x_2069_);
lean_ctor_set_uint8(v___x_2070_, 15, v___x_2063_);
lean_ctor_set_uint8(v___x_2070_, 16, v___x_2063_);
lean_ctor_set_uint8(v___x_2070_, 17, v___x_2063_);
lean_ctor_set_uint8(v___x_2070_, 18, v___x_2063_);
lean_ctor_set_uint8(v___x_2070_, 19, v___x_2062_);
lean_ctor_set_uint8(v___x_2070_, 20, v___x_2063_);
v___x_2071_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2070_);
v___x_2072_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set_uint64(v___x_2072_, sizeof(void*)*1, v___x_2071_);
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2074_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3);
v___x_2075_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_2076_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2));
v___x_2077_ = lean_box(0);
lean_inc(v___x_1987_);
v___x_2078_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2078_, 0, v___x_2072_);
lean_ctor_set(v___x_2078_, 1, v___x_1987_);
lean_ctor_set(v___x_2078_, 2, v___x_2075_);
lean_ctor_set(v___x_2078_, 3, v___x_2076_);
lean_ctor_set(v___x_2078_, 4, v___x_2077_);
lean_ctor_set(v___x_2078_, 5, v___x_2073_);
lean_ctor_set(v___x_2078_, 6, v___x_2077_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*7, v___x_2062_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*7 + 1, v___x_2062_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*7 + 2, v___x_2062_);
lean_ctor_set_uint8(v___x_2078_, sizeof(void*)*7 + 3, v___x_2063_);
v___x_2079_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3);
v___x_2080_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6);
v___x_2081_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7);
v___x_2082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2079_);
lean_ctor_set(v___x_2082_, 1, v___x_2080_);
lean_ctor_set(v___x_2082_, 2, v___x_1987_);
lean_ctor_set(v___x_2082_, 3, v___x_2074_);
lean_ctor_set(v___x_2082_, 4, v___x_2081_);
v___x_2083_ = lean_box(0);
v___x_2084_ = lean_st_mk_ref(v___x_2082_);
v___x_2085_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1988_, v_builtin_1989_, v___x_2064_, v___x_2066_, v___x_2078_, v___x_2084_, v___y_1992_, v___y_1993_);
lean_dec_ref_known(v___x_2078_, 7);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2093_; 
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; 
v_unused_2094_ = lean_ctor_get(v___x_2085_, 0);
lean_dec(v_unused_2094_);
v___x_2087_ = v___x_2085_;
v_isShared_2088_ = v_isSharedCheck_2093_;
goto v_resetjp_2086_;
}
else
{
lean_dec(v___x_2085_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2093_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_st_ref_get(v___x_2084_);
lean_dec(v___x_2084_);
lean_dec(v___x_2089_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2083_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2083_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v___x_2084_);
v_a_2095_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2085_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2085_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
v___y_2032_ = v___x_2062_;
goto v___jp_2031_;
}
}
else
{
lean_dec_ref(v___x_2029_);
v___y_2032_ = v___x_2060_;
goto v___jp_2031_;
}
v___jp_2031_:
{
uint8_t v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = 1;
lean_inc(v_constName_1990_);
v___x_2034_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v___x_2030_, v_constName_1990_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; 
lean_dec(v_constName_1990_);
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___y_1996_ = v___x_2033_;
v___y_1997_ = v___y_2032_;
v_a_1998_ = v_a_2035_;
goto v___jp_1995_;
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2059_; 
v_a_2036_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2038_ = v___x_2034_;
v_isShared_2039_ = v_isSharedCheck_2059_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2034_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2059_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
uint8_t v___x_2040_; 
v___x_2040_ = l_Lean_Exception_isInterrupt(v_a_2036_);
if (v___x_2040_ == 0)
{
uint8_t v___x_2041_; 
lean_inc(v_a_2036_);
v___x_2041_ = l_Lean_Exception_isRuntime(v_a_2036_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_del_object(v___x_2038_);
lean_dec(v_a_2036_);
v___x_2042_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11));
v___x_2043_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v___x_2042_, v_constName_1990_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___y_1996_ = v___x_2033_;
v___y_1997_ = v___y_2032_;
v_a_1998_ = v_a_2044_;
goto v___jp_1995_;
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref(v_ctx_1988_);
lean_dec(v___x_1987_);
v_a_2045_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2043_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2043_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v___x_2054_; 
lean_dec(v_constName_1990_);
lean_dec_ref(v_ctx_1988_);
lean_dec(v___x_1987_);
if (v_isShared_2039_ == 0)
{
v___x_2054_ = v___x_2038_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2036_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
else
{
lean_object* v___x_2057_; 
lean_dec(v_constName_1990_);
lean_dec_ref(v_ctx_1988_);
lean_dec(v___x_1987_);
if (v_isShared_2039_ == 0)
{
v___x_2057_ = v___x_2038_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2036_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec(v_constName_1990_);
lean_dec_ref(v_ctx_1988_);
lean_dec(v___x_1987_);
v_a_2103_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2027_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2027_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
v___jp_1995_:
{
uint8_t v___x_1999_; uint8_t v___x_2000_; uint8_t v___x_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; uint64_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_1999_ = 0;
v___x_2000_ = 1;
v___x_2001_ = 0;
v___x_2002_ = 2;
v___x_2003_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v___x_2003_, 0, v___x_1999_);
lean_ctor_set_uint8(v___x_2003_, 1, v___x_1999_);
lean_ctor_set_uint8(v___x_2003_, 2, v___x_1999_);
lean_ctor_set_uint8(v___x_2003_, 3, v___x_1999_);
lean_ctor_set_uint8(v___x_2003_, 4, v___x_1999_);
lean_ctor_set_uint8(v___x_2003_, 5, v___y_1997_);
lean_ctor_set_uint8(v___x_2003_, 6, v___y_1997_);
lean_ctor_set_uint8(v___x_2003_, 7, v___x_1999_);
lean_ctor_set_uint8(v___x_2003_, 8, v___y_1997_);
lean_ctor_set_uint8(v___x_2003_, 9, v___x_2000_);
lean_ctor_set_uint8(v___x_2003_, 10, v___x_2001_);
lean_ctor_set_uint8(v___x_2003_, 11, v___y_1997_);
lean_ctor_set_uint8(v___x_2003_, 12, v___y_1997_);
lean_ctor_set_uint8(v___x_2003_, 13, v___y_1997_);
lean_ctor_set_uint8(v___x_2003_, 14, v___x_2002_);
lean_ctor_set_uint8(v___x_2003_, 15, v___y_1997_);
lean_ctor_set_uint8(v___x_2003_, 16, v___y_1997_);
lean_ctor_set_uint8(v___x_2003_, 17, v___y_1997_);
lean_ctor_set_uint8(v___x_2003_, 18, v___y_1997_);
lean_ctor_set_uint8(v___x_2003_, 19, v___x_1999_);
lean_ctor_set_uint8(v___x_2003_, 20, v___y_1997_);
v___x_2004_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2003_);
v___x_2005_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set_uint64(v___x_2005_, sizeof(void*)*1, v___x_2004_);
v___x_2006_ = lean_unsigned_to_nat(0u);
v___x_2007_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__9_spec__10_spec__11___redArg___closed__3);
v___x_2008_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_2009_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2));
v___x_2010_ = lean_box(0);
lean_inc(v___x_1987_);
v___x_2011_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2011_, 0, v___x_2005_);
lean_ctor_set(v___x_2011_, 1, v___x_1987_);
lean_ctor_set(v___x_2011_, 2, v___x_2008_);
lean_ctor_set(v___x_2011_, 3, v___x_2009_);
lean_ctor_set(v___x_2011_, 4, v___x_2010_);
lean_ctor_set(v___x_2011_, 5, v___x_2006_);
lean_ctor_set(v___x_2011_, 6, v___x_2010_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*7, v___x_1999_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*7 + 1, v___x_1999_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*7 + 2, v___x_1999_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*7 + 3, v___y_1996_);
v___x_2012_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3);
v___x_2013_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6);
v___x_2014_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7);
v___x_2015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2012_);
lean_ctor_set(v___x_2015_, 1, v___x_2013_);
lean_ctor_set(v___x_2015_, 2, v___x_1987_);
lean_ctor_set(v___x_2015_, 3, v___x_2007_);
lean_ctor_set(v___x_2015_, 4, v___x_2014_);
v___x_2016_ = lean_st_mk_ref(v___x_2015_);
v___x_2017_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1988_, v_builtin_1989_, v_a_1998_, v___x_2011_, v___x_2016_, v___y_1992_, v___y_1993_);
lean_dec_ref_known(v___x_2011_, 7);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2026_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = lean_st_ref_get(v___x_2016_);
lean_dec(v___x_2016_);
lean_dec(v___x_2022_);
if (v_isShared_2021_ == 0)
{
v___x_2024_ = v___x_2020_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2018_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
else
{
lean_dec(v___x_2016_);
return v___x_2017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed(lean_object* v___x_2111_, lean_object* v_ctx_2112_, lean_object* v_builtin_2113_, lean_object* v_constName_2114_, lean_object* v_catName_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
uint8_t v_builtin_boxed_2119_; lean_object* v_res_2120_; 
v_builtin_boxed_2119_ = lean_unbox(v_builtin_2113_);
v_res_2120_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(v___x_2111_, v_ctx_2112_, v_builtin_boxed_2119_, v_constName_2114_, v_catName_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v_catName_2115_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(lean_object* v___y_2121_, uint8_t v_isExporting_2122_, lean_object* v___x_2123_, lean_object* v_a_x3f_2124_){
_start:
{
lean_object* v___x_2126_; lean_object* v_env_2127_; lean_object* v_nextMacroScope_2128_; lean_object* v_ngen_2129_; lean_object* v_auxDeclNGen_2130_; lean_object* v_traceState_2131_; lean_object* v_recordedDeps_2132_; lean_object* v_messages_2133_; lean_object* v_infoState_2134_; lean_object* v_snapshotTasks_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2146_; 
v___x_2126_ = lean_st_ref_take(v___y_2121_);
v_env_2127_ = lean_ctor_get(v___x_2126_, 0);
v_nextMacroScope_2128_ = lean_ctor_get(v___x_2126_, 1);
v_ngen_2129_ = lean_ctor_get(v___x_2126_, 2);
v_auxDeclNGen_2130_ = lean_ctor_get(v___x_2126_, 3);
v_traceState_2131_ = lean_ctor_get(v___x_2126_, 4);
v_recordedDeps_2132_ = lean_ctor_get(v___x_2126_, 6);
v_messages_2133_ = lean_ctor_get(v___x_2126_, 7);
v_infoState_2134_ = lean_ctor_get(v___x_2126_, 8);
v_snapshotTasks_2135_ = lean_ctor_get(v___x_2126_, 9);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2146_ == 0)
{
lean_object* v_unused_2147_; 
v_unused_2147_ = lean_ctor_get(v___x_2126_, 5);
lean_dec(v_unused_2147_);
v___x_2137_ = v___x_2126_;
v_isShared_2138_ = v_isSharedCheck_2146_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_snapshotTasks_2135_);
lean_inc(v_infoState_2134_);
lean_inc(v_messages_2133_);
lean_inc(v_recordedDeps_2132_);
lean_inc(v_traceState_2131_);
lean_inc(v_auxDeclNGen_2130_);
lean_inc(v_ngen_2129_);
lean_inc(v_nextMacroScope_2128_);
lean_inc(v_env_2127_);
lean_dec(v___x_2126_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2146_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2139_ = lean_box(0);
v___x_2140_ = l_Lean_Environment_setExporting(v_env_2127_, v_isExporting_2122_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 5, v___x_2123_);
lean_ctor_set(v___x_2137_, 0, v___x_2140_);
v___x_2142_ = v___x_2137_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_nextMacroScope_2128_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_ngen_2129_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v_auxDeclNGen_2130_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v_traceState_2131_);
lean_ctor_set(v_reuseFailAlloc_2145_, 5, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2145_, 6, v_recordedDeps_2132_);
lean_ctor_set(v_reuseFailAlloc_2145_, 7, v_messages_2133_);
lean_ctor_set(v_reuseFailAlloc_2145_, 8, v_infoState_2134_);
lean_ctor_set(v_reuseFailAlloc_2145_, 9, v_snapshotTasks_2135_);
v___x_2142_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_st_ref_put(v___y_2121_, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2139_);
return v___x_2144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v___y_2148_, lean_object* v_isExporting_2149_, lean_object* v___x_2150_, lean_object* v_a_x3f_2151_, lean_object* v___y_2152_){
_start:
{
uint8_t v_isExporting_boxed_2153_; lean_object* v_res_2154_; 
v_isExporting_boxed_2153_ = lean_unbox(v_isExporting_2149_);
v_res_2154_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2148_, v_isExporting_boxed_2153_, v___x_2150_, v_a_x3f_2151_);
lean_dec(v_a_x3f_2151_);
lean_dec(v___y_2148_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(lean_object* v_x_2155_, uint8_t v_isExporting_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; lean_object* v_env_2161_; lean_object* v___x_2162_; uint8_t v_isModule_2163_; 
v___x_2160_ = lean_st_ref_get(v___y_2158_);
v_env_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc_ref(v_env_2161_);
lean_dec(v___x_2160_);
v___x_2162_ = l_Lean_Environment_header(v_env_2161_);
v_isModule_2163_ = lean_ctor_get_uint8(v___x_2162_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2162_);
if (v_isModule_2163_ == 0)
{
lean_object* v___x_2164_; 
lean_dec_ref(v_env_2161_);
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
v___x_2164_ = lean_apply_3(v_x_2155_, v___y_2157_, v___y_2158_, lean_box(0));
return v___x_2164_;
}
else
{
uint8_t v_isExporting_2165_; 
v_isExporting_2165_ = lean_ctor_get_uint8(v_env_2161_, sizeof(void*)*13);
lean_dec_ref(v_env_2161_);
if (v_isExporting_2156_ == 0)
{
if (v_isExporting_2165_ == 0)
{
lean_object* v___x_2217_; 
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
v___x_2217_ = lean_apply_3(v_x_2155_, v___y_2157_, v___y_2158_, lean_box(0));
return v___x_2217_;
}
else
{
goto v___jp_2166_;
}
}
else
{
if (v_isExporting_2165_ == 0)
{
goto v___jp_2166_;
}
else
{
lean_object* v___x_2218_; 
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
v___x_2218_ = lean_apply_3(v_x_2155_, v___y_2157_, v___y_2158_, lean_box(0));
return v___x_2218_;
}
}
v___jp_2166_:
{
lean_object* v___x_2167_; lean_object* v_env_2168_; lean_object* v_nextMacroScope_2169_; lean_object* v_ngen_2170_; lean_object* v_auxDeclNGen_2171_; lean_object* v_traceState_2172_; lean_object* v_recordedDeps_2173_; lean_object* v_messages_2174_; lean_object* v_infoState_2175_; lean_object* v_snapshotTasks_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2215_; 
v___x_2167_ = lean_st_ref_take(v___y_2158_);
v_env_2168_ = lean_ctor_get(v___x_2167_, 0);
v_nextMacroScope_2169_ = lean_ctor_get(v___x_2167_, 1);
v_ngen_2170_ = lean_ctor_get(v___x_2167_, 2);
v_auxDeclNGen_2171_ = lean_ctor_get(v___x_2167_, 3);
v_traceState_2172_ = lean_ctor_get(v___x_2167_, 4);
v_recordedDeps_2173_ = lean_ctor_get(v___x_2167_, 6);
v_messages_2174_ = lean_ctor_get(v___x_2167_, 7);
v_infoState_2175_ = lean_ctor_get(v___x_2167_, 8);
v_snapshotTasks_2176_ = lean_ctor_get(v___x_2167_, 9);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; 
v_unused_2216_ = lean_ctor_get(v___x_2167_, 5);
lean_dec(v_unused_2216_);
v___x_2178_ = v___x_2167_;
v_isShared_2179_ = v_isSharedCheck_2215_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_snapshotTasks_2176_);
lean_inc(v_infoState_2175_);
lean_inc(v_messages_2174_);
lean_inc(v_recordedDeps_2173_);
lean_inc(v_traceState_2172_);
lean_inc(v_auxDeclNGen_2171_);
lean_inc(v_ngen_2170_);
lean_inc(v_nextMacroScope_2169_);
lean_inc(v_env_2168_);
lean_dec(v___x_2167_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2215_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2180_ = l_Lean_Environment_setExporting(v_env_2168_, v_isExporting_2156_);
v___x_2181_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 5, v___x_2181_);
lean_ctor_set(v___x_2178_, 0, v___x_2180_);
v___x_2183_ = v___x_2178_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_nextMacroScope_2169_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_ngen_2170_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v_auxDeclNGen_2171_);
lean_ctor_set(v_reuseFailAlloc_2214_, 4, v_traceState_2172_);
lean_ctor_set(v_reuseFailAlloc_2214_, 5, v___x_2181_);
lean_ctor_set(v_reuseFailAlloc_2214_, 6, v_recordedDeps_2173_);
lean_ctor_set(v_reuseFailAlloc_2214_, 7, v_messages_2174_);
lean_ctor_set(v_reuseFailAlloc_2214_, 8, v_infoState_2175_);
lean_ctor_set(v_reuseFailAlloc_2214_, 9, v_snapshotTasks_2176_);
v___x_2183_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; lean_object* v_r_2185_; 
v___x_2184_ = lean_st_ref_put(v___y_2158_, v___x_2183_);
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
v_r_2185_ = lean_apply_3(v_x_2155_, v___y_2157_, v___y_2158_, lean_box(0));
if (lean_obj_tag(v_r_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2202_; 
v_a_2186_ = lean_ctor_get(v_r_2185_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_r_2185_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2188_ = v_r_2185_;
v_isShared_2189_ = v_isSharedCheck_2202_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v_r_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2202_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
lean_inc(v_a_2186_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set_tag(v___x_2188_, 1);
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
v___x_2192_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2158_, v_isExporting_2165_, v___x_2181_, v___x_2191_);
lean_dec_ref(v___x_2191_);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v___x_2192_, 0);
lean_dec(v_unused_2200_);
v___x_2194_ = v___x_2192_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_dec(v___x_2192_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v_a_2186_);
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2186_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_a_2203_ = lean_ctor_get(v_r_2185_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v_r_2185_, 1);
v___x_2204_ = lean_box(0);
v___x_2205_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2158_, v_isExporting_2165_, v___x_2181_, v___x_2204_);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v___x_2205_, 0);
lean_dec(v_unused_2213_);
v___x_2207_ = v___x_2205_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_dec(v___x_2205_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set_tag(v___x_2207_, 1);
lean_ctor_set(v___x_2207_, 0, v_a_2203_);
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2203_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___boxed(lean_object* v_x_2219_, lean_object* v_isExporting_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
uint8_t v_isExporting_boxed_2224_; lean_object* v_res_2225_; 
v_isExporting_boxed_2224_ = lean_unbox(v_isExporting_2220_);
v_res_2225_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2219_, v_isExporting_boxed_2224_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(lean_object* v_x_2226_, uint8_t v_when_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
if (v_when_2227_ == 0)
{
lean_object* v___x_2231_; 
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
v___x_2231_ = lean_apply_3(v_x_2226_, v___y_2228_, v___y_2229_, lean_box(0));
return v___x_2231_;
}
else
{
uint8_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = 0;
v___x_2233_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2226_, v___x_2232_, v___y_2228_, v___y_2229_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg___boxed(lean_object* v_x_2234_, lean_object* v_when_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
uint8_t v_when_boxed_2239_; lean_object* v_res_2240_; 
v_when_boxed_2239_ = lean_unbox(v_when_2235_);
v_res_2240_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v_x_2234_, v_when_boxed_2239_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(lean_object* v___x_2241_, lean_object* v_ctx_2242_, lean_object* v_catName_2243_, lean_object* v_constName_2244_, uint8_t v_builtin_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; lean_object* v___f_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; 
v___x_2249_ = lean_box(v_builtin_2245_);
v___f_2250_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed), 8, 5);
lean_closure_set(v___f_2250_, 0, v___x_2241_);
lean_closure_set(v___f_2250_, 1, v_ctx_2242_);
lean_closure_set(v___f_2250_, 2, v___x_2249_);
lean_closure_set(v___f_2250_, 3, v_constName_2244_);
lean_closure_set(v___f_2250_, 4, v_catName_2243_);
v___x_2251_ = 1;
v___x_2252_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v___f_2250_, v___x_2251_, v___y_2246_, v___y_2247_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed(lean_object* v___x_2253_, lean_object* v_ctx_2254_, lean_object* v_catName_2255_, lean_object* v_constName_2256_, lean_object* v_builtin_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
uint8_t v_builtin_boxed_2261_; lean_object* v_res_2262_; 
v_builtin_boxed_2261_ = lean_unbox(v_builtin_2257_);
v_res_2262_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(v___x_2253_, v_ctx_2254_, v_catName_2255_, v_constName_2256_, v_builtin_boxed_2261_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg(lean_object* v_ctx_2263_){
_start:
{
lean_object* v___x_2265_; lean_object* v___f_2266_; lean_object* v___x_2267_; 
v___x_2265_ = lean_box(1);
v___f_2266_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed), 8, 2);
lean_closure_set(v___f_2266_, 0, v___x_2265_);
lean_closure_set(v___f_2266_, 1, v_ctx_2263_);
v___x_2267_ = l_Lean_Parser_registerParserAttributeHook(v___f_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___boxed(lean_object* v_ctx_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v_ctx_2268_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object* v_00_u03b1_2271_, lean_object* v_ctx_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v_ctx_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___boxed(lean_object* v_00_u03b1_2275_, lean_object* v_ctx_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_ParserCompiler_registerParserCompiler(v_00_u03b1_2275_, v_ctx_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(lean_object* v_00_u03b1_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(v_00_u03b1_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(lean_object* v_00_u03b1_2289_, lean_object* v_typeName_2290_, lean_object* v_constName_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v_typeName_2290_, v_constName_2291_, v___y_2292_, v___y_2293_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___boxed(lean_object* v_00_u03b1_2296_, lean_object* v_typeName_2297_, lean_object* v_constName_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(v_00_u03b1_2296_, v_typeName_2297_, v_constName_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(lean_object* v_00_u03b1_2303_, lean_object* v_x_2304_, uint8_t v_isExporting_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2304_, v_isExporting_2305_, v___y_2306_, v___y_2307_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2310_, lean_object* v_x_2311_, lean_object* v_isExporting_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
uint8_t v_isExporting_boxed_2316_; lean_object* v_res_2317_; 
v_isExporting_boxed_2316_ = lean_unbox(v_isExporting_2312_);
v_res_2317_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(v_00_u03b1_2310_, v_x_2311_, v_isExporting_boxed_2316_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(lean_object* v_00_u03b1_2318_, lean_object* v_x_2319_, uint8_t v_when_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v_x_2319_, v_when_2320_, v___y_2321_, v___y_2322_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___boxed(lean_object* v_00_u03b1_2325_, lean_object* v_x_2326_, lean_object* v_when_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
uint8_t v_when_boxed_2331_; lean_object* v_res_2332_; 
v_when_boxed_2331_ = lean_unbox(v_when_2327_);
v_res_2332_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(v_00_u03b1_2325_, v_x_2326_, v_when_boxed_2331_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(lean_object* v_00_u03b1_2333_, lean_object* v_constName_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_2334_, v___y_2335_, v___y_2336_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2339_, lean_object* v_constName_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(v_00_u03b1_2339_, v_constName_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(lean_object* v_00_u03b1_2345_, lean_object* v_x_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v_x_2346_, v___y_2347_, v___y_2348_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2351_, lean_object* v_x_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(v_00_u03b1_2351_, v_x_2352_, v___y_2353_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2357_, lean_object* v_ref_2358_, lean_object* v_constName_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_2358_, v_constName_2359_, v___y_2360_, v___y_2361_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2364_, lean_object* v_ref_2365_, lean_object* v_constName_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(v_00_u03b1_2364_, v_ref_2365_, v_constName_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v_ref_2365_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2371_, lean_object* v_msg_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_2372_, v___y_2373_, v___y_2374_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2377_, lean_object* v_msg_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(v_00_u03b1_2377_, v_msg_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b1_2383_, lean_object* v_ref_2384_, lean_object* v_msg_2385_, lean_object* v_declHint_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_2384_, v_msg_2385_, v_declHint_2386_, v___y_2387_, v___y_2388_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b1_2391_, lean_object* v_ref_2392_, lean_object* v_msg_2393_, lean_object* v_declHint_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_2391_, v_ref_2392_, v_msg_2393_, v_declHint_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v_ref_2392_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(lean_object* v_msg_2399_, lean_object* v_declHint_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_2399_, v_declHint_2400_, v___y_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___boxed(lean_object* v_msg_2405_, lean_object* v_declHint_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(v_msg_2405_, v_declHint_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_2411_, lean_object* v_ref_2412_, lean_object* v_msg_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_2412_, v_msg_2413_, v___y_2414_, v___y_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2418_, lean_object* v_ref_2419_, lean_object* v_msg_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(v_00_u03b1_2418_, v_ref_2419_, v_msg_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v_ref_2419_);
return v_res_2424_;
}
}
lean_object* runtime_initialize_Lean_Meta_ReduceEval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_ParserCompiler_Attribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ParserCompiler(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_ReduceEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_KeyedDeclsAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ParserCompiler_Attribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ParserCompiler(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_ReduceEval(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* initialize_Lean_ParserCompiler_Attribute(uint8_t builtin);
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ParserCompiler(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_ReduceEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler_Attribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ParserCompiler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ParserCompiler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ParserCompiler(builtin);
}
#ifdef __cplusplus
}
#endif
