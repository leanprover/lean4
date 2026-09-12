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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
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
static const lean_array_object l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "node"};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__0_value;
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 125, 54, 68, 103, 5, 171, 140)}};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value;
static const lean_string_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withAntiquot"};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__2 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__2_value;
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(2, 88, 47, 17, 27, 77, 70, 127)}};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value;
static const lean_string_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leadingNode"};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__4 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__4_value;
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(226, 41, 145, 230, 168, 227, 241, 30)}};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value;
static const lean_string_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "trailingNode"};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__6 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__6_value;
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(11, 103, 4, 79, 164, 122, 74, 107)}};
static const lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7 = (const lean_object*)&l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "don't know how to generate "};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " for non-parser combinator `"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "refusing to generate code for imported parser declaration `"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "`; use `@[run_parser_attribute_hooks]` on its definition instead."};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = " for non-definition `"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "TrailingParser"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 139, 135, 36, 12, 238, 116)}};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19_value;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "call of unknown parser at `"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "TrailingParserDescr"};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(73, 30, 7, 95, 84, 115, 124, 250)}};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_value;
static const lean_string_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ParserDescr"};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(92, 191, 134, 190, 206, 60, 55, 123)}};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value;
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
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(lean_object* v_a_279_, lean_object* v_params_280_, lean_object* v_x_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; lean_object* v___y_289_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_302_ = l_Array_zipIdx___redArg(v_params_280_, v___x_287_);
v___x_303_ = lean_array_get_size(v___x_302_);
v___x_304_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0));
v___x_305_ = lean_nat_dec_lt(v___x_287_, v___x_303_);
if (v___x_305_ == 0)
{
lean_dec_ref(v___x_302_);
v___y_289_ = v___x_304_;
goto v___jp_288_;
}
else
{
lean_object* v_lctx_306_; uint8_t v___x_307_; 
v_lctx_306_ = lean_ctor_get(v___y_282_, 2);
v___x_307_ = lean_nat_dec_le(v___x_303_, v___x_303_);
if (v___x_307_ == 0)
{
if (v___x_305_ == 0)
{
lean_dec_ref(v___x_302_);
v___y_289_ = v___x_304_;
goto v___jp_288_;
}
else
{
size_t v___x_308_; size_t v___x_309_; lean_object* v___x_310_; 
v___x_308_ = ((size_t)0ULL);
v___x_309_ = lean_usize_of_nat(v___x_303_);
lean_inc_ref(v_lctx_306_);
v___x_310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v_lctx_306_, v___x_302_, v___x_308_, v___x_309_, v___x_304_);
lean_dec_ref(v___x_302_);
v___y_289_ = v___x_310_;
goto v___jp_288_;
}
}
else
{
size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; 
v___x_311_ = ((size_t)0ULL);
v___x_312_ = lean_usize_of_nat(v___x_303_);
lean_inc_ref(v_lctx_306_);
v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v_lctx_306_, v___x_302_, v___x_311_, v___x_312_, v___x_304_);
lean_dec_ref(v___x_302_);
v___y_289_ = v___x_313_;
goto v___jp_288_;
}
}
v___jp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_290_ = lean_array_get_size(v___y_289_);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_dec_eq(v___x_290_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec_ref(v___y_289_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
else
{
lean_object* v___x_295_; lean_object* v_snd_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_295_ = lean_array_fget(v___y_289_, v___x_287_);
lean_dec_ref(v___y_289_);
v_snd_296_ = lean_ctor_get(v___x_295_, 1);
lean_inc(v_snd_296_);
lean_dec(v___x_295_);
v___x_297_ = l_Lean_Expr_getAppNumArgs(v_a_279_);
v___x_298_ = lean_nat_sub(v___x_297_, v_snd_296_);
lean_dec(v_snd_296_);
lean_dec(v___x_297_);
v___x_299_ = lean_nat_sub(v___x_298_, v___x_291_);
lean_dec(v___x_298_);
v___x_300_ = l_Lean_Expr_getRevArg_x21(v_a_279_, v___x_299_);
v___x_301_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v___x_300_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed(lean_object* v_a_314_, lean_object* v_params_315_, lean_object* v_x_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(v_a_314_, v_params_315_, v_x_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec_ref(v_x_316_);
lean_dec_ref(v_a_314_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f(lean_object* v_e_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___y_350_; uint8_t v___y_351_; lean_object* v___f_354_; lean_object* v___x_355_; 
v___f_354_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed), 7, 0);
v___x_355_ = l_Lean_Meta_whnfCore(v_e_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
switch(lean_obj_tag(v_a_356_))
{
case 6:
{
goto v___jp_357_;
}
case 8:
{
goto v___jp_357_;
}
default: 
{
lean_object* v___f_385_; uint8_t v___y_387_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
lean_dec_ref(v___f_354_);
lean_inc(v_a_356_);
v___f_385_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed), 8, 1);
lean_closure_set(v___f_385_, 0, v_a_356_);
v___x_411_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5));
v___x_412_ = lean_unsigned_to_nat(3u);
v___x_413_ = l_Lean_Expr_isAppOfArity(v_a_356_, v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_414_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7));
v___x_415_ = lean_unsigned_to_nat(4u);
v___x_416_ = l_Lean_Expr_isAppOfArity(v_a_356_, v___x_414_, v___x_415_);
v___y_387_ = v___x_416_;
goto v___jp_386_;
}
else
{
v___y_387_ = v___x_413_;
goto v___jp_386_;
}
v___jp_386_:
{
if (v___y_387_ == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_388_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1));
v___x_389_ = lean_unsigned_to_nat(2u);
v___x_390_ = l_Lean_Expr_isAppOfArity(v_a_356_, v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3));
v___x_392_ = l_Lean_Expr_isAppOfArity(v_a_356_, v___x_391_, v___x_389_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = l_Lean_Expr_getAppFn(v_a_356_);
lean_dec(v_a_356_);
lean_inc(v_a_347_);
lean_inc_ref(v_a_346_);
lean_inc(v_a_345_);
lean_inc_ref(v_a_344_);
v___x_394_ = lean_infer_type(v___x_393_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_396_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v___x_396_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_395_, v___f_385_, v___x_392_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
return v___x_396_;
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec_ref(v___f_385_);
v_a_397_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_394_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_394_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec_ref(v___f_385_);
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = l_Lean_Expr_getAppNumArgs(v_a_356_);
v___x_407_ = lean_nat_sub(v___x_406_, v___x_405_);
lean_dec(v___x_406_);
v___x_408_ = lean_nat_sub(v___x_407_, v___x_405_);
lean_dec(v___x_407_);
v___x_409_ = l_Lean_Expr_getRevArg_x21(v_a_356_, v___x_408_);
lean_dec(v_a_356_);
v_e_343_ = v___x_409_;
goto _start;
}
}
else
{
lean_dec_ref(v___f_385_);
goto v___jp_360_;
}
}
else
{
lean_dec_ref(v___f_385_);
goto v___jp_360_;
}
}
}
}
v___jp_357_:
{
uint8_t v___x_358_; lean_object* v___x_359_; 
v___x_358_ = 0;
v___x_359_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_a_356_, v___f_354_, v___x_358_, v___x_358_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
return v___x_359_;
}
v___jp_360_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_361_ = l_Lean_Expr_getAppNumArgs(v_a_356_);
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_sub(v___x_361_, v___x_362_);
lean_dec(v___x_361_);
v___x_364_ = l_Lean_Expr_getRevArg_x21(v_a_356_, v___x_363_);
lean_dec(v_a_356_);
v___x_365_ = l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1(v___x_364_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_374_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_374_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v_a_366_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_370_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_384_; 
v_a_375_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_384_ == 0)
{
v___x_377_ = v___x_365_;
v_isShared_378_ = v_isSharedCheck_384_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_365_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_384_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
lean_inc(v_a_375_);
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_383_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
uint8_t v___x_381_; 
v___x_381_ = l_Lean_Exception_isInterrupt(v_a_375_);
if (v___x_381_ == 0)
{
uint8_t v___x_382_; 
v___x_382_ = l_Lean_Exception_isRuntime(v_a_375_);
v___y_350_ = v___x_380_;
v___y_351_ = v___x_382_;
goto v___jp_349_;
}
else
{
lean_dec(v_a_375_);
v___y_350_ = v___x_380_;
v___y_351_ = v___x_381_;
goto v___jp_349_;
}
}
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec_ref(v___f_354_);
v_a_417_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_355_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_355_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
v___jp_349_:
{
if (v___y_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec_ref(v___y_350_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
else
{
return v___y_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(lean_object* v_x_425_, lean_object* v_e_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v_e_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___boxed(lean_object* v_e_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v_e_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(lean_object* v_x_440_, lean_object* v_b_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v_b_441_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed(lean_object* v_x_448_, lean_object* v_b_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(v_x_448_, v_b_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec_ref(v_x_448_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(lean_object* v_ctx_459_, lean_object* v_as_460_, size_t v_i_461_, size_t v_stop_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_usize_dec_eq(v_i_461_, v_stop_462_);
if (v___x_469_ == 0)
{
size_t v___x_470_; size_t v___x_471_; lean_object* v_a_473_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_470_ = ((size_t)1ULL);
v___x_471_ = lean_usize_sub(v_i_461_, v___x_470_);
v___x_478_ = lean_array_uget_borrowed(v_as_460_, v___x_471_);
lean_inc(v___y_467_);
lean_inc_ref(v___y_466_);
lean_inc(v___y_465_);
lean_inc_ref(v___y_464_);
lean_inc(v___x_478_);
v___x_479_ = lean_infer_type(v___x_478_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_481_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
lean_inc_ref(v_ctx_459_);
v___x_481_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_459_, v_a_480_);
lean_dec(v_a_480_);
v_a_473_ = v___x_481_;
goto v___jp_472_;
}
else
{
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_482_; 
v_a_482_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_482_);
lean_dec_ref_known(v___x_479_, 1);
v_a_473_ = v_a_482_;
goto v___jp_472_;
}
else
{
lean_dec_ref(v_b_463_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_483_; 
v_a_483_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_479_, 1);
v_i_461_ = v___x_471_;
v_b_463_ = v_a_483_;
goto _start;
}
else
{
lean_dec_ref(v_ctx_459_);
return v___x_479_;
}
}
}
v___jp_472_:
{
lean_object* v___x_474_; uint8_t v___x_475_; lean_object* v___x_476_; 
v___x_474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__1));
v___x_475_ = 0;
v___x_476_ = l_Lean_mkForall(v___x_474_, v___x_475_, v_a_473_, v_b_463_);
v_i_461_ = v___x_471_;
v_b_463_ = v___x_476_;
goto _start;
}
}
else
{
lean_object* v___x_485_; 
lean_dec_ref(v_ctx_459_);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v_b_463_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___boxed(lean_object* v_ctx_486_, lean_object* v_as_487_, lean_object* v_i_488_, lean_object* v_stop_489_, lean_object* v_b_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
size_t v_i_boxed_496_; size_t v_stop_boxed_497_; lean_object* v_res_498_; 
v_i_boxed_496_ = lean_unbox_usize(v_i_488_);
lean_dec(v_i_488_);
v_stop_boxed_497_ = lean_unbox_usize(v_stop_489_);
lean_dec(v_stop_489_);
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_486_, v_as_487_, v_i_boxed_496_, v_stop_boxed_497_, v_b_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec_ref(v_as_487_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3(lean_object* v_ctx_499_, lean_object* v_params_500_, lean_object* v_x_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_507_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_499_);
v___x_508_ = lean_box(0);
v___x_509_ = l_Lean_mkConst(v___x_507_, v___x_508_);
v___x_510_ = lean_array_get_size(v_params_500_);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_nat_dec_lt(v___x_511_, v___x_510_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec_ref(v_ctx_499_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_509_);
return v___x_513_;
}
else
{
size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_usize_of_nat(v___x_510_);
v___x_515_ = ((size_t)0ULL);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_499_, v_params_500_, v___x_514_, v___x_515_, v___x_509_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3___boxed(lean_object* v_ctx_517_, lean_object* v_params_518_, lean_object* v_x_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3(v_ctx_517_, v_params_518_, v_x_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec_ref(v_x_519_);
lean_dec_ref(v_params_518_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0(lean_object* v_k_526_, uint8_t v_usedLetOnly_527_, lean_object* v_xs_528_, lean_object* v_b_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; 
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc_ref(v_xs_528_);
v___x_535_ = lean_apply_7(v_k_526_, v_xs_528_, v_b_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, lean_box(0));
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; uint8_t v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v___x_535_, 1);
v___x_537_ = 0;
v___x_538_ = 1;
v___x_539_ = l_Lean_Meta_mkLambdaFVars(v_xs_528_, v_a_536_, v___x_537_, v_usedLetOnly_527_, v___x_537_, v___x_537_, v___x_538_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec_ref(v_xs_528_);
return v___x_539_;
}
else
{
lean_dec_ref(v_xs_528_);
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0___boxed(lean_object* v_k_540_, lean_object* v_usedLetOnly_541_, lean_object* v_xs_542_, lean_object* v_b_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
uint8_t v_usedLetOnly_boxed_549_; lean_object* v_res_550_; 
v_usedLetOnly_boxed_549_ = lean_unbox(v_usedLetOnly_541_);
v_res_550_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0(v_k_540_, v_usedLetOnly_boxed_549_, v_xs_542_, v_b_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(lean_object* v_e_551_, lean_object* v_k_552_, uint8_t v_cleanupAnnotations_553_, uint8_t v_preserveNondepLet_554_, uint8_t v_usedLetOnly_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; lean_object* v___f_562_; lean_object* v___x_563_; 
v___x_561_ = lean_box(v_usedLetOnly_555_);
v___f_562_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0___boxed), 9, 2);
lean_closure_set(v___f_562_, 0, v_k_552_);
lean_closure_set(v___f_562_, 1, v___x_561_);
v___x_563_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_e_551_, v___f_562_, v_cleanupAnnotations_553_, v_preserveNondepLet_554_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___boxed(lean_object* v_e_564_, lean_object* v_k_565_, lean_object* v_cleanupAnnotations_566_, lean_object* v_preserveNondepLet_567_, lean_object* v_usedLetOnly_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_574_; uint8_t v_preserveNondepLet_boxed_575_; uint8_t v_usedLetOnly_boxed_576_; lean_object* v_res_577_; 
v_cleanupAnnotations_boxed_574_ = lean_unbox(v_cleanupAnnotations_566_);
v_preserveNondepLet_boxed_575_ = lean_unbox(v_preserveNondepLet_567_);
v_usedLetOnly_boxed_576_ = lean_unbox(v_usedLetOnly_568_);
v_res_577_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_e_564_, v_k_565_, v_cleanupAnnotations_boxed_574_, v_preserveNondepLet_boxed_575_, v_usedLetOnly_boxed_576_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v_res_577_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_578_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
lean_ctor_set(v___x_583_, 3, v___x_582_);
lean_ctor_set(v___x_583_, 4, v___x_581_);
lean_ctor_set(v___x_583_, 5, v___x_581_);
lean_ctor_set(v___x_583_, 6, v___x_581_);
lean_ctor_set(v___x_583_, 7, v___x_581_);
lean_ctor_set(v___x_583_, 8, v___x_581_);
lean_ctor_set(v___x_583_, 9, v___x_581_);
lean_ctor_set(v___x_583_, 10, v___x_581_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_unsigned_to_nat(32u);
v___x_585_ = lean_mk_empty_array_with_capacity(v___x_584_);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_587_ = ((size_t)5ULL);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_unsigned_to_nat(32u);
v___x_590_ = lean_mk_empty_array_with_capacity(v___x_589_);
v___x_591_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_592_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_590_);
lean_ctor_set(v___x_592_, 2, v___x_588_);
lean_ctor_set(v___x_592_, 3, v___x_588_);
lean_ctor_set_usize(v___x_592_, 4, v___x_587_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_593_ = lean_box(1);
v___x_594_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_595_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_594_);
lean_ctor_set(v___x_596_, 2, v___x_593_);
return v___x_596_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_599_ = l_Lean_stringToMessageData(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_602_ = l_Lean_stringToMessageData(v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_605_ = l_Lean_stringToMessageData(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_608_ = l_Lean_stringToMessageData(v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_611_ = l_Lean_stringToMessageData(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_614_ = l_Lean_stringToMessageData(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_617_ = l_Lean_stringToMessageData(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_618_, lean_object* v_declHint_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v_env_624_; uint8_t v___x_625_; 
v___x_622_ = lean_box(0);
v___x_623_ = lean_st_ref_get(v___y_620_);
v_env_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc_ref(v_env_624_);
lean_dec(v___x_623_);
v___x_625_ = l_Lean_Name_isAnonymous(v_declHint_619_);
if (v___x_625_ == 0)
{
uint8_t v_isExporting_626_; 
v_isExporting_626_ = lean_ctor_get_uint8(v_env_624_, sizeof(void*)*8);
if (v_isExporting_626_ == 0)
{
lean_object* v___x_627_; 
lean_dec_ref(v_env_624_);
lean_dec(v_declHint_619_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_msg_618_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; uint8_t v___x_629_; 
lean_inc_ref(v_env_624_);
v___x_628_ = l_Lean_Environment_setExporting(v_env_624_, v___x_625_);
lean_inc(v_declHint_619_);
lean_inc_ref(v___x_628_);
v___x_629_ = l_Lean_Environment_contains(v___x_628_, v_declHint_619_, v_isExporting_626_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; 
lean_dec_ref(v___x_628_);
lean_dec_ref(v_env_624_);
lean_dec(v_declHint_619_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v_msg_618_);
return v___x_630_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v_c_636_; lean_object* v___x_637_; 
v___x_631_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_632_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_633_ = l_Lean_Options_empty;
v___x_634_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_634_, 0, v___x_628_);
lean_ctor_set(v___x_634_, 1, v___x_631_);
lean_ctor_set(v___x_634_, 2, v___x_632_);
lean_ctor_set(v___x_634_, 3, v___x_633_);
lean_inc(v_declHint_619_);
v___x_635_ = l_Lean_MessageData_ofConstName(v_declHint_619_, v___x_625_);
v_c_636_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_636_, 0, v___x_634_);
lean_ctor_set(v_c_636_, 1, v___x_635_);
v___x_637_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_624_, v_declHint_619_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec_ref(v_env_624_);
lean_dec(v_declHint_619_);
v___x_638_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v_c_636_);
v___x_640_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = l_Lean_MessageData_note(v___x_641_);
v___x_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_643_, 0, v_msg_618_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
else
{
lean_object* v_val_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_679_; 
v_val_645_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_679_ == 0)
{
v___x_647_ = v___x_637_;
v_isShared_648_ = v_isSharedCheck_679_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_val_645_);
lean_dec(v___x_637_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_679_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v_mod_651_; uint8_t v___x_652_; 
v___x_649_ = l_Lean_Environment_header(v_env_624_);
lean_dec_ref(v_env_624_);
v___x_650_ = l_Lean_EnvironmentHeader_moduleNames(v___x_649_);
v_mod_651_ = lean_array_get(v___x_622_, v___x_650_, v_val_645_);
lean_dec(v_val_645_);
lean_dec_ref(v___x_650_);
v___x_652_ = l_Lean_isPrivateName(v_declHint_619_);
lean_dec(v_declHint_619_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_653_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v_c_636_);
v___x_655_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = l_Lean_MessageData_ofName(v_mod_651_);
v___x_658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = l_Lean_MessageData_note(v___x_660_);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v_msg_618_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 0);
lean_ctor_set(v___x_647_, 0, v___x_662_);
v___x_664_ = v___x_647_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_666_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v_c_636_);
v___x_668_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = l_Lean_MessageData_ofName(v_mod_651_);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = l_Lean_MessageData_note(v___x_673_);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v_msg_618_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 0);
lean_ctor_set(v___x_647_, 0, v___x_675_);
v___x_677_ = v___x_647_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_680_; 
lean_dec_ref(v_env_624_);
lean_dec(v_declHint_619_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v_msg_618_);
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_681_, lean_object* v_declHint_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_681_, v_declHint_682_, v___y_683_);
lean_dec(v___y_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_686_, lean_object* v_declHint_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_703_; 
v___x_693_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_686_, v_declHint_687_, v___y_691_);
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_703_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_703_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_703_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_698_ = l_Lean_unknownIdentifierMessageTag;
v___x_699_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v_a_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_699_);
v___x_701_ = v___x_696_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_704_, lean_object* v_declHint_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_704_, v_declHint_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(lean_object* v_msgData_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; lean_object* v_env_719_; lean_object* v___x_720_; lean_object* v_toCold_721_; lean_object* v_mctx_722_; lean_object* v_lctx_723_; lean_object* v_options_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_718_ = lean_st_ref_get(v___y_716_);
v_env_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc_ref(v_env_719_);
lean_dec(v___x_718_);
v___x_720_ = lean_st_ref_get(v___y_714_);
v_toCold_721_ = lean_ctor_get(v___y_715_, 0);
v_mctx_722_ = lean_ctor_get(v___x_720_, 0);
lean_inc_ref(v_mctx_722_);
lean_dec(v___x_720_);
v_lctx_723_ = lean_ctor_get(v___y_713_, 2);
v_options_724_ = lean_ctor_get(v_toCold_721_, 2);
lean_inc_ref(v_options_724_);
lean_inc_ref(v_lctx_723_);
v___x_725_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_725_, 0, v_env_719_);
lean_ctor_set(v___x_725_, 1, v_mctx_722_);
lean_ctor_set(v___x_725_, 2, v_lctx_723_);
lean_ctor_set(v___x_725_, 3, v_options_724_);
v___x_726_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v_msgData_712_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___boxed(lean_object* v_msgData_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(v_msgData_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(lean_object* v_msg_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_ref_741_; lean_object* v___x_742_; lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_751_; 
v_ref_741_ = lean_ctor_get(v___y_738_, 2);
v___x_742_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(v_msg_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_751_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
lean_inc(v_ref_741_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v_ref_741_);
lean_ctor_set(v___x_747_, 1, v_a_743_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 1);
lean_ctor_set(v___x_745_, 0, v___x_747_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg___boxed(lean_object* v_msg_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v_msg_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_759_, lean_object* v_msg_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_toCold_766_; lean_object* v_currRecDepth_767_; lean_object* v_ref_768_; uint8_t v_diag_769_; uint8_t v_suppressElabErrors_770_; lean_object* v_ref_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_toCold_766_ = lean_ctor_get(v___y_763_, 0);
v_currRecDepth_767_ = lean_ctor_get(v___y_763_, 1);
v_ref_768_ = lean_ctor_get(v___y_763_, 2);
v_diag_769_ = lean_ctor_get_uint8(v___y_763_, sizeof(void*)*3);
v_suppressElabErrors_770_ = lean_ctor_get_uint8(v___y_763_, sizeof(void*)*3 + 1);
v_ref_771_ = l_Lean_replaceRef(v_ref_759_, v_ref_768_);
lean_inc(v_currRecDepth_767_);
lean_inc_ref(v_toCold_766_);
v___x_772_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_772_, 0, v_toCold_766_);
lean_ctor_set(v___x_772_, 1, v_currRecDepth_767_);
lean_ctor_set(v___x_772_, 2, v_ref_771_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*3, v_diag_769_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*3 + 1, v_suppressElabErrors_770_);
v___x_773_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v_msg_760_, v___y_761_, v___y_762_, v___x_772_, v___y_764_);
lean_dec_ref_known(v___x_772_, 3);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_774_, lean_object* v_msg_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_774_, v_msg_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v_ref_774_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_782_, lean_object* v_msg_783_, lean_object* v_declHint_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; lean_object* v_a_791_; lean_object* v___x_792_; 
v___x_790_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_783_, v_declHint_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref(v___x_790_);
v___x_792_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_782_, v_a_791_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_793_, lean_object* v_msg_794_, lean_object* v_declHint_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_793_, v_msg_794_, v_declHint_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v_ref_793_);
return v_res_801_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__0));
v___x_804_ = l_Lean_stringToMessageData(v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__2));
v___x_807_ = l_Lean_stringToMessageData(v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_808_, lean_object* v_constName_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_815_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_816_ = 0;
lean_inc(v_constName_809_);
v___x_817_ = l_Lean_MessageData_ofConstName(v_constName_809_, v___x_816_);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_815_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_808_, v___x_820_, v_constName_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_822_, lean_object* v_constName_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_822_, v_constName_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v_ref_822_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(lean_object* v_constName_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_ref_836_; lean_object* v___x_837_; 
v_ref_836_ = lean_ctor_get(v___y_833_, 2);
v___x_837_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_836_, v_constName_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg___boxed(lean_object* v_constName_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(lean_object* v_constName_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_env_852_; uint8_t v___x_853_; lean_object* v___x_854_; 
v___x_851_ = lean_st_ref_get(v___y_849_);
v_env_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc_ref(v_env_852_);
lean_dec(v___x_851_);
v___x_853_ = 0;
lean_inc(v_constName_845_);
v___x_854_ = l_Lean_Environment_find_x3f(v_env_852_, v_constName_845_, v___x_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
return v___x_855_;
}
else
{
lean_object* v_val_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_constName_845_);
v_val_856_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_854_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_val_856_);
lean_dec(v___x_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 0);
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_val_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3___boxed(lean_object* v_constName_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(v_constName_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(lean_object* v_b_871_, lean_object* v_arg_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = l_Lean_Expr_app___override(v_b_871_, v_arg_872_);
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1___boxed(lean_object* v_b_881_, lean_object* v_arg_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_881_, v_arg_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed(lean_object* v_ctx_890_, lean_object* v_builtin_891_, lean_object* v_force_892_, lean_object* v_x_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
uint8_t v_builtin_boxed_900_; uint8_t v_force_boxed_901_; lean_object* v_res_902_; 
v_builtin_boxed_900_ = lean_unbox(v_builtin_891_);
v_force_boxed_901_ = lean_unbox(v_force_892_);
v_res_902_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(v_ctx_890_, v_builtin_boxed_900_, v_force_boxed_901_, v_x_893_, v_b_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_x_893_);
return v_res_902_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_903_; lean_object* v_dummy_904_; 
v___x_903_ = lean_box(0);
v_dummy_904_ = l_Lean_Expr_sort___override(v___x_903_);
return v_dummy_904_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(lean_object* v_upperBound_905_, lean_object* v_params_906_, lean_object* v___x_907_, lean_object* v_ctx_908_, uint8_t v_builtin_909_, uint8_t v_force_910_, lean_object* v_a_911_, lean_object* v_b_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___y_919_; uint8_t v___x_941_; 
v___x_941_ = lean_nat_dec_lt(v_a_911_, v_upperBound_905_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_dec(v_a_911_);
lean_dec_ref(v_ctx_908_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v_b_912_);
return v___x_942_;
}
else
{
lean_object* v___f_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___f_943_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0));
v___x_944_ = l_Lean_instInhabitedExpr;
v___x_945_ = lean_array_get_borrowed(v___x_944_, v_params_906_, v_a_911_);
v___x_946_ = lean_array_get_borrowed(v___x_944_, v___x_907_, v_a_911_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
lean_inc(v___x_945_);
v___x_947_ = lean_infer_type(v___x_945_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; uint8_t v___x_949_; lean_object* v___x_950_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_947_, 1);
v___x_949_ = 0;
v___x_950_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_948_, v___f_943_, v___x_949_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_908_);
v___x_953_ = l_Lean_Expr_isConstOf(v_a_951_, v___x_952_);
lean_dec(v___x_952_);
lean_dec(v_a_951_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
lean_inc(v___x_946_);
v___x_954_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_912_, v___x_946_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
v___y_919_ = v___x_954_;
goto v___jp_918_;
}
else
{
lean_object* v___x_955_; 
lean_inc(v___x_946_);
lean_inc_ref(v_ctx_908_);
v___x_955_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_908_, v_builtin_909_, v_force_910_, v___x_946_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_957_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
v___x_957_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_912_, v_a_956_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
v___y_919_ = v___x_957_;
goto v___jp_918_;
}
else
{
lean_dec_ref(v_b_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_ctx_908_);
return v___x_955_;
}
}
}
else
{
lean_dec_ref(v_b_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_ctx_908_);
return v___x_950_;
}
}
else
{
lean_dec_ref(v_b_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_ctx_908_);
return v___x_947_;
}
}
v___jp_918_:
{
if (lean_obj_tag(v___y_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_932_; 
v_a_920_ = lean_ctor_get(v___y_919_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___y_919_);
if (v_isSharedCheck_932_ == 0)
{
v___x_922_ = v___y_919_;
v_isShared_923_ = v_isSharedCheck_932_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___y_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_932_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
if (lean_obj_tag(v_a_920_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; 
lean_dec(v_a_911_);
lean_dec_ref(v_ctx_908_);
v_a_924_ = lean_ctor_get(v_a_920_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v_a_920_, 1);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v_a_924_);
v___x_926_ = v___x_922_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_del_object(v___x_922_);
v_a_928_ = lean_ctor_get(v_a_920_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v_a_920_, 1);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_add(v_a_911_, v___x_929_);
lean_dec(v_a_911_);
v_a_911_ = v___x_930_;
v_b_912_ = v_a_928_;
goto _start;
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_a_911_);
lean_dec_ref(v_ctx_908_);
v_a_933_ = lean_ctor_get(v___y_919_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___y_919_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___y_919_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___y_919_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(lean_object* v_a_958_, lean_object* v_ctx_959_, uint8_t v_builtin_960_, uint8_t v_force_961_, lean_object* v___x_962_, lean_object* v_params_963_, lean_object* v_x_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_dummy_970_; lean_object* v_nargs_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___y_977_; lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v_dummy_970_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0, &l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0);
v_nargs_971_ = l_Lean_Expr_getAppNumArgs(v_a_958_);
lean_inc(v_nargs_971_);
v___x_972_ = lean_mk_array(v_nargs_971_, v_dummy_970_);
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = lean_nat_sub(v_nargs_971_, v___x_973_);
lean_dec(v_nargs_971_);
v___x_975_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_958_, v___x_972_, v___x_974_);
v___x_980_ = lean_array_get_size(v_params_963_);
v___x_981_ = lean_array_get_size(v___x_975_);
v___x_982_ = lean_nat_dec_le(v___x_980_, v___x_981_);
if (v___x_982_ == 0)
{
v___y_977_ = v___x_981_;
goto v___jp_976_;
}
else
{
v___y_977_ = v___x_980_;
goto v___jp_976_;
}
v___jp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v___y_977_, v_params_963_, v___x_975_, v_ctx_959_, v_builtin_960_, v_force_961_, v___x_978_, v___x_962_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec_ref(v___x_975_);
lean_dec(v___y_977_);
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed(lean_object* v_a_983_, lean_object* v_ctx_984_, lean_object* v_builtin_985_, lean_object* v_force_986_, lean_object* v___x_987_, lean_object* v_params_988_, lean_object* v_x_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v_builtin_boxed_995_; uint8_t v_force_boxed_996_; lean_object* v_res_997_; 
v_builtin_boxed_995_ = lean_unbox(v_builtin_985_);
v_force_boxed_996_ = lean_unbox(v_force_986_);
v_res_997_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(v_a_983_, v_ctx_984_, v_builtin_boxed_995_, v_force_boxed_996_, v___x_987_, v_params_988_, v_x_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec_ref(v_x_989_);
lean_dec_ref(v_params_988_);
return v_res_997_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5);
v___x_1013_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
lean_ctor_set(v___x_1013_, 2, v___x_1012_);
lean_ctor_set(v___x_1013_, 3, v___x_1012_);
lean_ctor_set(v___x_1013_, 4, v___x_1012_);
lean_ctor_set(v___x_1013_, 5, v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20));
v___x_1036_ = l_Lean_stringToMessageData(v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg(lean_object* v_ctx_1037_, uint8_t v_builtin_1038_, uint8_t v_force_1039_, lean_object* v_e_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; 
v___f_1046_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0));
v___x_1047_ = lean_box(v_builtin_1038_);
v___x_1048_ = lean_box(v_force_1039_);
lean_inc_ref_n(v_ctx_1037_, 2);
v___f_1049_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1049_, 0, v_ctx_1037_);
lean_closure_set(v___f_1049_, 1, v___x_1047_);
lean_closure_set(v___f_1049_, 2, v___x_1048_);
v___f_1050_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_1050_, 0, v_ctx_1037_);
v___x_1051_ = l_Lean_Meta_whnfCore(v_e_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v_p_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
switch(lean_obj_tag(v_a_1052_))
{
case 6:
{
uint8_t v___x_1068_; uint8_t v___x_1069_; lean_object* v___x_1070_; 
lean_dec_ref_known(v___x_1051_, 1);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_ctx_1037_);
v___x_1068_ = 0;
v___x_1069_ = 1;
v___x_1070_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_a_1052_, v___f_1049_, v___x_1068_, v___x_1068_, v___x_1069_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
return v___x_1070_;
}
case 8:
{
uint8_t v___x_1071_; uint8_t v___x_1072_; lean_object* v___x_1073_; 
lean_dec_ref_known(v___x_1051_, 1);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_ctx_1037_);
v___x_1071_ = 0;
v___x_1072_ = 1;
v___x_1073_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_a_1052_, v___f_1049_, v___x_1071_, v___x_1071_, v___x_1072_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
return v___x_1073_;
}
case 1:
{
lean_dec_ref_known(v_a_1052_, 1);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v___f_1049_);
lean_dec_ref(v_ctx_1037_);
return v___x_1051_;
}
default: 
{
lean_object* v___x_1074_; 
lean_dec_ref_known(v___x_1051_, 1);
lean_dec_ref(v___f_1049_);
v___x_1074_ = l_Lean_Expr_getAppFn(v_a_1052_);
if (lean_obj_tag(v___x_1074_) == 4)
{
lean_object* v_declName_1075_; lean_object* v___x_1076_; lean_object* v_env_1077_; lean_object* v_varName_1078_; lean_object* v_categoryAttr_1079_; lean_object* v_combinatorAttr_1080_; lean_object* v___x_1081_; 
v_declName_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_declName_1075_);
lean_dec_ref_known(v___x_1074_, 2);
v___x_1076_ = lean_st_ref_get(v_a_1044_);
v_env_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc_ref_n(v_env_1077_, 2);
lean_dec(v___x_1076_);
v_varName_1078_ = lean_ctor_get(v_ctx_1037_, 0);
v_categoryAttr_1079_ = lean_ctor_get(v_ctx_1037_, 1);
v_combinatorAttr_1080_ = lean_ctor_get(v_ctx_1037_, 2);
v___x_1081_ = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(v_combinatorAttr_1080_, v_env_1077_, v_declName_1075_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_inc(v_varName_1078_);
lean_inc_n(v_declName_1075_, 2);
v___x_1082_ = l_Lean_Name_append(v_declName_1075_, v_varName_1078_);
v___x_1083_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(v_declName_1075_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v___x_1085_ = l_Lean_ConstantInfo_type(v_a_1084_);
v___x_1086_ = 0;
lean_inc_ref(v___x_1085_);
v___x_1087_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v___x_1085_, v___f_1046_, v___x_1086_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; uint8_t v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; uint8_t v___y_1211_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1261_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19));
v___x_1262_ = l_Lean_Expr_isConstOf(v_a_1088_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = ((lean_object*)(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2));
v___x_1264_ = l_Lean_Expr_isConstOf(v_a_1088_, v___x_1263_);
lean_dec(v_a_1088_);
v___y_1211_ = v___x_1264_;
goto v___jp_1210_;
}
else
{
lean_dec(v_a_1088_);
v___y_1211_ = v___x_1262_;
goto v___jp_1210_;
}
v___jp_1089_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; lean_object* v___x_1111_; 
v___x_1096_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2));
lean_inc(v___y_1095_);
v___x_1097_ = l_Lean_mkIdent(v___y_1095_);
v___x_1098_ = l_Lean_mkIdent(v___y_1091_);
v___x_1099_ = lean_unsigned_to_nat(1u);
v___x_1100_ = lean_mk_empty_array_with_capacity(v___x_1099_);
v___x_1101_ = lean_array_push(v___x_1100_, v___x_1098_);
v___x_1102_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__4));
v___x_1103_ = lean_box(2);
v___x_1104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v___x_1102_);
lean_ctor_set(v___x_1104_, 2, v___x_1101_);
v___x_1105_ = lean_unsigned_to_nat(2u);
v___x_1106_ = lean_mk_empty_array_with_capacity(v___x_1105_);
v___x_1107_ = lean_array_push(v___x_1106_, v___x_1097_);
v___x_1108_ = lean_array_push(v___x_1107_, v___x_1104_);
v___x_1109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1103_);
lean_ctor_set(v___x_1109_, 1, v___x_1096_);
lean_ctor_set(v___x_1109_, 2, v___x_1108_);
v___x_1110_ = 0;
lean_inc(v___x_1082_);
v___x_1111_ = l_Lean_Attribute_add(v___x_1082_, v___y_1095_, v___x_1109_, v___x_1110_, v___y_1094_, v___y_1092_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_dec_ref_known(v___x_1111_, 1);
v_p_1054_ = v___x_1082_;
v___y_1055_ = v___y_1090_;
v___y_1056_ = v___y_1093_;
v___y_1057_ = v___y_1094_;
v___y_1058_ = v___y_1092_;
goto v___jp_1053_;
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v___x_1082_);
lean_dec(v_a_1052_);
lean_dec_ref(v_ctx_1037_);
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
v___jp_1120_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_inc_ref_n(v_ctx_1037_, 2);
v___x_1127_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_1037_, v___y_1122_);
lean_dec_ref(v___y_1122_);
v___x_1128_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1037_, v_builtin_1038_, v_force_1039_, v___x_1127_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
lean_inc_ref(v___x_1085_);
v___x_1130_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v___x_1085_, v___f_1050_, v___x_1086_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1209_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1209_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1209_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1135_ = lean_box(0);
lean_inc_n(v___x_1082_, 2);
v___x_1136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1082_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
lean_ctor_set(v___x_1136_, 2, v_a_1131_);
v___x_1137_ = lean_box(0);
v___x_1138_ = 1;
v___x_1139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1082_);
lean_ctor_set(v___x_1139_, 1, v___x_1135_);
v___x_1140_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1140_, 0, v___x_1136_);
lean_ctor_set(v___x_1140_, 1, v_a_1129_);
lean_ctor_set(v___x_1140_, 2, v___x_1137_);
lean_ctor_set(v___x_1140_, 3, v___x_1139_);
lean_ctor_set_uint8(v___x_1140_, sizeof(void*)*4, v___x_1138_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 1);
lean_ctor_set(v___x_1133_, 0, v___x_1140_);
v___x_1142_ = v___x_1133_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v_env_1144_; uint8_t v___x_1145_; lean_object* v___x_1146_; 
v___x_1143_ = lean_st_ref_get(v___y_1126_);
v_env_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc_ref(v_env_1144_);
lean_dec(v___x_1143_);
lean_inc(v_declName_1075_);
v___x_1145_ = l_Lean_isMarkedMeta(v_env_1144_, v_declName_1075_);
v___x_1146_ = l_Lean_addAndCompile(v___x_1142_, v___y_1121_, v___x_1145_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1147_; lean_object* v_env_1148_; lean_object* v_nextMacroScope_1149_; lean_object* v_ngen_1150_; lean_object* v_auxDeclNGen_1151_; lean_object* v_traceState_1152_; lean_object* v_messages_1153_; lean_object* v_infoState_1154_; lean_object* v_snapshotTasks_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref_known(v___x_1146_, 1);
v___x_1147_ = lean_st_ref_take(v___y_1126_);
v_env_1148_ = lean_ctor_get(v___x_1147_, 0);
v_nextMacroScope_1149_ = lean_ctor_get(v___x_1147_, 1);
v_ngen_1150_ = lean_ctor_get(v___x_1147_, 2);
v_auxDeclNGen_1151_ = lean_ctor_get(v___x_1147_, 3);
v_traceState_1152_ = lean_ctor_get(v___x_1147_, 4);
v_messages_1153_ = lean_ctor_get(v___x_1147_, 6);
v_infoState_1154_ = lean_ctor_get(v___x_1147_, 7);
v_snapshotTasks_1155_ = lean_ctor_get(v___x_1147_, 8);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v___x_1147_, 5);
lean_dec(v_unused_1199_);
v___x_1157_ = v___x_1147_;
v_isShared_1158_ = v_isSharedCheck_1198_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_snapshotTasks_1155_);
lean_inc(v_infoState_1154_);
lean_inc(v_messages_1153_);
lean_inc(v_traceState_1152_);
lean_inc(v_auxDeclNGen_1151_);
lean_inc(v_ngen_1150_);
lean_inc(v_nextMacroScope_1149_);
lean_inc(v_env_1148_);
lean_dec(v___x_1147_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1198_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_inc(v___x_1082_);
lean_inc_ref(v_combinatorAttr_1080_);
v___x_1159_ = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(v_combinatorAttr_1080_, v_env_1148_, v_declName_1075_, v___x_1082_);
v___x_1160_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 5, v___x_1160_);
lean_ctor_set(v___x_1157_, 0, v___x_1159_);
v___x_1162_ = v___x_1157_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_nextMacroScope_1149_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_ngen_1150_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_auxDeclNGen_1151_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_traceState_1152_);
lean_ctor_set(v_reuseFailAlloc_1197_, 5, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1197_, 6, v_messages_1153_);
lean_ctor_set(v_reuseFailAlloc_1197_, 7, v_infoState_1154_);
lean_ctor_set(v_reuseFailAlloc_1197_, 8, v_snapshotTasks_1155_);
v___x_1162_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_mctx_1165_; lean_object* v_zetaDeltaFVarIds_1166_; lean_object* v_postponed_1167_; lean_object* v_diag_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1195_; 
v___x_1163_ = lean_st_ref_put(v___y_1126_, v___x_1162_);
v___x_1164_ = lean_st_ref_take(v___y_1124_);
v_mctx_1165_ = lean_ctor_get(v___x_1164_, 0);
v_zetaDeltaFVarIds_1166_ = lean_ctor_get(v___x_1164_, 2);
v_postponed_1167_ = lean_ctor_get(v___x_1164_, 3);
v_diag_1168_ = lean_ctor_get(v___x_1164_, 4);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v___x_1164_, 1);
lean_dec(v_unused_1196_);
v___x_1170_ = v___x_1164_;
v_isShared_1171_ = v_isSharedCheck_1195_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_diag_1168_);
lean_inc(v_postponed_1167_);
lean_inc(v_zetaDeltaFVarIds_1166_);
lean_inc(v_mctx_1165_);
lean_dec(v___x_1164_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1195_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1172_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v___x_1172_);
v___x_1174_ = v___x_1170_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_mctx_1165_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_zetaDeltaFVarIds_1166_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v_postponed_1167_);
lean_ctor_set(v_reuseFailAlloc_1194_, 4, v_diag_1168_);
v___x_1174_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_st_ref_put(v___y_1124_, v___x_1174_);
v___x_1176_ = l_Lean_Expr_isConst(v___x_1085_);
lean_dec_ref(v___x_1085_);
if (v___x_1176_ == 0)
{
lean_dec(v_a_1084_);
v_p_1054_ = v___x_1082_;
v___y_1055_ = v___y_1123_;
v___y_1056_ = v___y_1124_;
v___y_1057_ = v___y_1125_;
v___y_1058_ = v___y_1126_;
goto v___jp_1053_;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = l_Lean_ConstantInfo_value_x21(v_a_1084_, v___x_1086_);
lean_dec(v_a_1084_);
v___x_1178_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v___x_1177_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
if (lean_obj_tag(v_a_1179_) == 1)
{
if (v_builtin_1038_ == 0)
{
lean_object* v_defn_1180_; lean_object* v_val_1181_; lean_object* v_name_1182_; 
v_defn_1180_ = lean_ctor_get(v_categoryAttr_1079_, 0);
v_val_1181_ = lean_ctor_get(v_a_1179_, 0);
lean_inc(v_val_1181_);
lean_dec_ref_known(v_a_1179_, 1);
v_name_1182_ = lean_ctor_get(v_defn_1180_, 1);
lean_inc(v_name_1182_);
v___y_1090_ = v___y_1123_;
v___y_1091_ = v_val_1181_;
v___y_1092_ = v___y_1126_;
v___y_1093_ = v___y_1124_;
v___y_1094_ = v___y_1125_;
v___y_1095_ = v_name_1182_;
goto v___jp_1089_;
}
else
{
lean_object* v_defn_1183_; lean_object* v_val_1184_; lean_object* v_builtinName_1185_; 
v_defn_1183_ = lean_ctor_get(v_categoryAttr_1079_, 0);
v_val_1184_ = lean_ctor_get(v_a_1179_, 0);
lean_inc(v_val_1184_);
lean_dec_ref_known(v_a_1179_, 1);
v_builtinName_1185_ = lean_ctor_get(v_defn_1183_, 0);
lean_inc(v_builtinName_1185_);
v___y_1090_ = v___y_1123_;
v___y_1091_ = v_val_1184_;
v___y_1092_ = v___y_1126_;
v___y_1093_ = v___y_1124_;
v___y_1094_ = v___y_1125_;
v___y_1095_ = v_builtinName_1185_;
goto v___jp_1089_;
}
}
else
{
lean_dec(v_a_1179_);
v_p_1054_ = v___x_1082_;
v___y_1055_ = v___y_1123_;
v___y_1056_ = v___y_1124_;
v___y_1057_ = v___y_1125_;
v___y_1058_ = v___y_1126_;
goto v___jp_1053_;
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v___x_1082_);
lean_dec(v_a_1052_);
lean_dec_ref(v_ctx_1037_);
v_a_1186_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1178_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1178_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
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
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v___x_1085_);
lean_dec(v_a_1084_);
lean_dec(v___x_1082_);
lean_dec(v_declName_1075_);
lean_dec(v_a_1052_);
lean_dec_ref(v_ctx_1037_);
v_a_1200_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1146_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1146_);
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
}
}
else
{
lean_dec(v_a_1129_);
lean_dec_ref(v___x_1085_);
lean_dec(v_a_1084_);
lean_dec(v___x_1082_);
lean_dec(v_declName_1075_);
lean_dec(v_a_1052_);
lean_dec_ref(v_ctx_1037_);
return v___x_1130_;
}
}
else
{
lean_dec_ref(v___x_1085_);
lean_dec(v_a_1084_);
lean_dec(v___x_1082_);
lean_dec(v_declName_1075_);
lean_dec(v_a_1052_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_ctx_1037_);
return v___x_1128_;
}
}
v___jp_1210_:
{
if (v___y_1211_ == 0)
{
lean_object* v___x_1212_; 
lean_dec_ref(v___x_1085_);
lean_dec(v_a_1084_);
lean_dec(v___x_1082_);
lean_dec_ref(v_env_1077_);
lean_dec(v_declName_1075_);
lean_dec_ref(v___f_1050_);
lean_inc(v_a_1052_);
v___x_1212_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_1052_, v___x_1086_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
if (lean_obj_tag(v_a_1213_) == 1)
{
lean_object* v_val_1214_; 
lean_dec(v_a_1052_);
v_val_1214_ = lean_ctor_get(v_a_1213_, 0);
lean_inc(v_val_1214_);
lean_dec_ref_known(v_a_1213_, 1);
v_e_1040_ = v_val_1214_;
goto _start;
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_inc(v_varName_1078_);
lean_dec(v_a_1213_);
lean_dec_ref(v_ctx_1037_);
v___x_1216_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9);
v___x_1217_ = l_Lean_MessageData_ofName(v_varName_1078_);
v___x_1218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11);
v___x_1220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1218_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = l_Lean_MessageData_ofExpr(v_a_1052_);
v___x_1222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1224_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
return v___x_1225_;
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec(v_a_1052_);
lean_dec_ref(v_ctx_1037_);
v_a_1226_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1212_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1212_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v___x_1234_; 
lean_inc(v_a_1084_);
v___x_1234_ = l_Lean_ConstantInfo_value_x3f(v_a_1084_, v___x_1086_);
if (lean_obj_tag(v___x_1234_) == 1)
{
lean_object* v_val_1235_; lean_object* v___x_1236_; 
v_val_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_val_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1077_, v_declName_1075_);
lean_dec_ref(v_env_1077_);
if (lean_obj_tag(v___x_1236_) == 0)
{
v___y_1121_ = v___y_1211_;
v___y_1122_ = v_val_1235_;
v___y_1123_ = v_a_1041_;
v___y_1124_ = v_a_1042_;
v___y_1125_ = v_a_1043_;
v___y_1126_ = v_a_1044_;
goto v___jp_1120_;
}
else
{
lean_dec_ref_known(v___x_1236_, 1);
if (v_force_1039_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1237_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13);
lean_inc(v_declName_1075_);
v___x_1238_ = l_Lean_MessageData_ofName(v_declName_1075_);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1241_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_dec_ref_known(v___x_1242_, 1);
v___y_1121_ = v___y_1211_;
v___y_1122_ = v_val_1235_;
v___y_1123_ = v_a_1041_;
v___y_1124_ = v_a_1042_;
v___y_1125_ = v_a_1043_;
v___y_1126_ = v_a_1044_;
goto v___jp_1120_;
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec(v_val_1235_);
lean_dec_ref(v___x_1085_);
lean_dec(v_a_1084_);
lean_dec(v___x_1082_);
lean_dec(v_declName_1075_);
lean_dec(v_a_1052_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_ctx_1037_);
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
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
else
{
v___y_1121_ = v___y_1211_;
v___y_1122_ = v_val_1235_;
v___y_1123_ = v_a_1041_;
v___y_1124_ = v_a_1042_;
v___y_1125_ = v_a_1043_;
v___y_1126_ = v_a_1044_;
goto v___jp_1120_;
}
}
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_inc(v_varName_1078_);
lean_dec(v___x_1234_);
lean_dec_ref(v___x_1085_);
lean_dec(v_a_1084_);
lean_dec(v___x_1082_);
lean_dec_ref(v_env_1077_);
lean_dec(v_declName_1075_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_ctx_1037_);
v___x_1251_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9);
v___x_1252_ = l_Lean_MessageData_ofName(v_varName_1078_);
v___x_1253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17);
v___x_1255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1253_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = l_Lean_MessageData_ofExpr(v_a_1052_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1259_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
return v___x_1260_;
}
}
}
}
else
{
lean_dec_ref(v___x_1085_);
lean_dec(v_a_1084_);
lean_dec(v___x_1082_);
lean_dec_ref(v_env_1077_);
lean_dec(v_declName_1075_);
lean_dec(v_a_1052_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_ctx_1037_);
return v___x_1087_;
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v___x_1082_);
lean_dec_ref(v_env_1077_);
lean_dec(v_declName_1075_);
lean_dec(v_a_1052_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_ctx_1037_);
v_a_1265_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1083_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1083_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
else
{
lean_object* v_val_1273_; 
lean_dec_ref(v_env_1077_);
lean_dec(v_declName_1075_);
lean_dec_ref(v___f_1050_);
v_val_1273_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v___x_1081_, 1);
v_p_1054_ = v_val_1273_;
v___y_1055_ = v_a_1041_;
v___y_1056_ = v_a_1042_;
v___y_1057_ = v_a_1043_;
v___y_1058_ = v_a_1044_;
goto v___jp_1053_;
}
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec_ref(v___x_1074_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_ctx_1037_);
v___x_1274_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21);
v___x_1275_ = l_Lean_MessageData_ofExpr(v_a_1052_);
v___x_1276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1278_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
return v___x_1279_;
}
}
}
v___jp_1053_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = l_Lean_mkConst(v_p_1054_, v___x_1059_);
v___x_1061_ = lean_box(v_builtin_1038_);
v___x_1062_ = lean_box(v_force_1039_);
lean_inc_ref(v___x_1060_);
v___f_1063_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed), 12, 5);
lean_closure_set(v___f_1063_, 0, v_a_1052_);
lean_closure_set(v___f_1063_, 1, v_ctx_1037_);
lean_closure_set(v___f_1063_, 2, v___x_1061_);
lean_closure_set(v___f_1063_, 3, v___x_1062_);
lean_closure_set(v___f_1063_, 4, v___x_1060_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
v___x_1064_ = lean_infer_type(v___x_1060_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; uint8_t v___x_1066_; lean_object* v___x_1067_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1066_ = 0;
v___x_1067_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_1065_, v___f_1063_, v___x_1066_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
return v___x_1067_;
}
else
{
lean_dec_ref(v___f_1063_);
return v___x_1064_;
}
}
}
else
{
lean_dec_ref(v___f_1050_);
lean_dec_ref(v___f_1049_);
lean_dec_ref(v_ctx_1037_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(lean_object* v_ctx_1280_, uint8_t v_builtin_1281_, uint8_t v_force_1282_, lean_object* v_x_1283_, lean_object* v_b_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1280_, v_builtin_1281_, v_force_1282_, v_b_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___boxed(lean_object* v_upperBound_1291_, lean_object* v_params_1292_, lean_object* v___x_1293_, lean_object* v_ctx_1294_, lean_object* v_builtin_1295_, lean_object* v_force_1296_, lean_object* v_a_1297_, lean_object* v_b_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
uint8_t v_builtin_boxed_1304_; uint8_t v_force_boxed_1305_; lean_object* v_res_1306_; 
v_builtin_boxed_1304_ = lean_unbox(v_builtin_1295_);
v_force_boxed_1305_ = lean_unbox(v_force_1296_);
v_res_1306_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v_upperBound_1291_, v_params_1292_, v___x_1293_, v_ctx_1294_, v_builtin_boxed_1304_, v_force_boxed_1305_, v_a_1297_, v_b_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec_ref(v___x_1293_);
lean_dec_ref(v_params_1292_);
lean_dec(v_upperBound_1291_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___boxed(lean_object* v_ctx_1307_, lean_object* v_builtin_1308_, lean_object* v_force_1309_, lean_object* v_e_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
uint8_t v_builtin_boxed_1316_; uint8_t v_force_boxed_1317_; lean_object* v_res_1318_; 
v_builtin_boxed_1316_ = lean_unbox(v_builtin_1308_);
v_force_boxed_1317_ = lean_unbox(v_force_1309_);
v_res_1318_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1307_, v_builtin_boxed_1316_, v_force_boxed_1317_, v_e_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr(lean_object* v_00_u03b1_1319_, lean_object* v_ctx_1320_, uint8_t v_builtin_1321_, uint8_t v_force_1322_, lean_object* v_e_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1320_, v_builtin_1321_, v_force_1322_, v_e_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___boxed(lean_object* v_00_u03b1_1330_, lean_object* v_ctx_1331_, lean_object* v_builtin_1332_, lean_object* v_force_1333_, lean_object* v_e_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
uint8_t v_builtin_boxed_1340_; uint8_t v_force_boxed_1341_; lean_object* v_res_1342_; 
v_builtin_boxed_1340_ = lean_unbox(v_builtin_1332_);
v_force_boxed_1341_ = lean_unbox(v_force_1333_);
v_res_1342_ = l_Lean_ParserCompiler_compileParserExpr(v_00_u03b1_1330_, v_ctx_1331_, v_builtin_boxed_1340_, v_force_boxed_1341_, v_e_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(lean_object* v_00_u03b1_1343_, lean_object* v_ctx_1344_, lean_object* v_as_1345_, size_t v_i_1346_, size_t v_stop_1347_, lean_object* v_b_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_1344_, v_as_1345_, v_i_1346_, v_stop_1347_, v_b_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___boxed(lean_object* v_00_u03b1_1355_, lean_object* v_ctx_1356_, lean_object* v_as_1357_, lean_object* v_i_1358_, lean_object* v_stop_1359_, lean_object* v_b_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
size_t v_i_boxed_1366_; size_t v_stop_boxed_1367_; lean_object* v_res_1368_; 
v_i_boxed_1366_ = lean_unbox_usize(v_i_1358_);
lean_dec(v_i_1358_);
v_stop_boxed_1367_ = lean_unbox_usize(v_stop_1359_);
lean_dec(v_stop_1359_);
v_res_1368_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(v_00_u03b1_1355_, v_ctx_1356_, v_as_1357_, v_i_boxed_1366_, v_stop_boxed_1367_, v_b_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec_ref(v_as_1357_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(lean_object* v_upperBound_1369_, lean_object* v_params_1370_, lean_object* v___x_1371_, lean_object* v_00_u03b1_1372_, lean_object* v_ctx_1373_, uint8_t v_builtin_1374_, uint8_t v_force_1375_, lean_object* v_inst_1376_, lean_object* v_R_1377_, lean_object* v_a_1378_, lean_object* v_b_1379_, lean_object* v_c_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v_upperBound_1369_, v_params_1370_, v___x_1371_, v_ctx_1373_, v_builtin_1374_, v_force_1375_, v_a_1378_, v_b_1379_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1387_ = _args[0];
lean_object* v_params_1388_ = _args[1];
lean_object* v___x_1389_ = _args[2];
lean_object* v_00_u03b1_1390_ = _args[3];
lean_object* v_ctx_1391_ = _args[4];
lean_object* v_builtin_1392_ = _args[5];
lean_object* v_force_1393_ = _args[6];
lean_object* v_inst_1394_ = _args[7];
lean_object* v_R_1395_ = _args[8];
lean_object* v_a_1396_ = _args[9];
lean_object* v_b_1397_ = _args[10];
lean_object* v_c_1398_ = _args[11];
lean_object* v___y_1399_ = _args[12];
lean_object* v___y_1400_ = _args[13];
lean_object* v___y_1401_ = _args[14];
lean_object* v___y_1402_ = _args[15];
lean_object* v___y_1403_ = _args[16];
_start:
{
uint8_t v_builtin_boxed_1404_; uint8_t v_force_boxed_1405_; lean_object* v_res_1406_; 
v_builtin_boxed_1404_ = lean_unbox(v_builtin_1392_);
v_force_boxed_1405_ = lean_unbox(v_force_1393_);
v_res_1406_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(v_upperBound_1387_, v_params_1388_, v___x_1389_, v_00_u03b1_1390_, v_ctx_1391_, v_builtin_boxed_1404_, v_force_boxed_1405_, v_inst_1394_, v_R_1395_, v_a_1396_, v_b_1397_, v_c_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v___x_1389_);
lean_dec_ref(v_params_1388_);
lean_dec(v_upperBound_1387_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4(lean_object* v_00_u03b1_1407_, lean_object* v_msg_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v_msg_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_msg_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4(v_00_u03b1_1415_, v_msg_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(lean_object* v_00_u03b1_1423_, lean_object* v_constName_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1431_, lean_object* v_constName_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(v_00_u03b1_1431_, v_constName_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_1439_, lean_object* v_ref_1440_, lean_object* v_constName_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_1440_, v_constName_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1448_, lean_object* v_ref_1449_, lean_object* v_constName_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(v_00_u03b1_1448_, v_ref_1449_, v_constName_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v_ref_1449_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_1457_, lean_object* v_ref_1458_, lean_object* v_msg_1459_, lean_object* v_declHint_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_1458_, v_msg_1459_, v_declHint_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1467_, lean_object* v_ref_1468_, lean_object* v_msg_1469_, lean_object* v_declHint_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7(v_00_u03b1_1467_, v_ref_1468_, v_msg_1469_, v_declHint_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v_ref_1468_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_1477_, lean_object* v_declHint_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1477_, v_declHint_1478_, v___y_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1485_, lean_object* v_declHint_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_1485_, v_declHint_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1493_, lean_object* v_ref_1494_, lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1494_, v_msg_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1502_, lean_object* v_ref_1503_, lean_object* v_msg_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_1502_, v_ref_1503_, v_msg_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v_ref_1503_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(lean_object* v_ctx_1511_, uint8_t v_builtin_1512_, lean_object* v_x_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_p_1520_; lean_object* v_psep_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; 
switch(lean_obj_tag(v_x_1513_))
{
case 1:
{
lean_object* v_p_1528_; 
v_p_1528_ = lean_ctor_get(v_x_1513_, 1);
lean_inc_ref(v_p_1528_);
lean_dec_ref_known(v_x_1513_, 2);
v_x_1513_ = v_p_1528_;
goto _start;
}
case 2:
{
lean_object* v_p_u2081_1530_; lean_object* v_p_u2082_1531_; lean_object* v___x_1532_; 
v_p_u2081_1530_ = lean_ctor_get(v_x_1513_, 1);
lean_inc_ref(v_p_u2081_1530_);
v_p_u2082_1531_ = lean_ctor_get(v_x_1513_, 2);
lean_inc_ref(v_p_u2082_1531_);
lean_dec_ref_known(v_x_1513_, 3);
lean_inc_ref(v_ctx_1511_);
v___x_1532_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1511_, v_builtin_1512_, v_p_u2081_1530_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_dec_ref_known(v___x_1532_, 1);
v_x_1513_ = v_p_u2082_1531_;
goto _start;
}
else
{
lean_dec_ref(v_p_u2082_1531_);
lean_dec_ref(v_ctx_1511_);
return v___x_1532_;
}
}
case 3:
{
lean_object* v_p_1534_; 
v_p_1534_ = lean_ctor_get(v_x_1513_, 2);
lean_inc_ref(v_p_1534_);
lean_dec_ref_known(v_x_1513_, 3);
v_x_1513_ = v_p_1534_;
goto _start;
}
case 4:
{
lean_object* v_p_1536_; 
v_p_1536_ = lean_ctor_get(v_x_1513_, 3);
lean_inc_ref(v_p_1536_);
lean_dec_ref_known(v_x_1513_, 4);
v_x_1513_ = v_p_1536_;
goto _start;
}
case 8:
{
lean_object* v_declName_1538_; uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_declName_1538_ = lean_ctor_get(v_x_1513_, 0);
lean_inc(v_declName_1538_);
lean_dec_ref_known(v_x_1513_, 1);
v___x_1539_ = 0;
v___x_1540_ = lean_box(0);
v___x_1541_ = l_Lean_mkConst(v_declName_1538_, v___x_1540_);
v___x_1542_ = lean_box(0);
v___x_1543_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1511_, v_builtin_1512_, v___x_1539_, v___x_1541_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v___x_1543_, 0);
lean_dec(v_unused_1551_);
v___x_1545_ = v___x_1543_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_dec(v___x_1543_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1542_);
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1542_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_a_1552_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1543_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1543_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
case 9:
{
lean_object* v_p_1560_; 
v_p_1560_ = lean_ctor_get(v_x_1513_, 2);
lean_inc_ref(v_p_1560_);
lean_dec_ref_known(v_x_1513_, 3);
v_x_1513_ = v_p_1560_;
goto _start;
}
case 10:
{
lean_object* v_p_1562_; lean_object* v_psep_1563_; 
v_p_1562_ = lean_ctor_get(v_x_1513_, 0);
lean_inc_ref(v_p_1562_);
v_psep_1563_ = lean_ctor_get(v_x_1513_, 2);
lean_inc_ref(v_psep_1563_);
lean_dec_ref_known(v_x_1513_, 3);
v_p_1520_ = v_p_1562_;
v_psep_1521_ = v_psep_1563_;
v___y_1522_ = v_a_1514_;
v___y_1523_ = v_a_1515_;
v___y_1524_ = v_a_1516_;
v___y_1525_ = v_a_1517_;
goto v___jp_1519_;
}
case 11:
{
lean_object* v_p_1564_; lean_object* v_psep_1565_; 
v_p_1564_ = lean_ctor_get(v_x_1513_, 0);
lean_inc_ref(v_p_1564_);
v_psep_1565_ = lean_ctor_get(v_x_1513_, 2);
lean_inc_ref(v_psep_1565_);
lean_dec_ref_known(v_x_1513_, 3);
v_p_1520_ = v_p_1564_;
v_psep_1521_ = v_psep_1565_;
v___y_1522_ = v_a_1514_;
v___y_1523_ = v_a_1515_;
v___y_1524_ = v_a_1516_;
v___y_1525_ = v_a_1517_;
goto v___jp_1519_;
}
default: 
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_dec_ref(v_x_1513_);
lean_dec_ref(v_ctx_1511_);
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
return v___x_1567_;
}
}
v___jp_1519_:
{
lean_object* v___x_1526_; 
lean_inc_ref(v_ctx_1511_);
v___x_1526_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1511_, v_builtin_1512_, v_p_1520_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_dec_ref_known(v___x_1526_, 1);
v_x_1513_ = v_psep_1521_;
v_a_1514_ = v___y_1522_;
v_a_1515_ = v___y_1523_;
v_a_1516_ = v___y_1524_;
v_a_1517_ = v___y_1525_;
goto _start;
}
else
{
lean_dec_ref(v_psep_1521_);
lean_dec_ref(v_ctx_1511_);
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg___boxed(lean_object* v_ctx_1568_, lean_object* v_builtin_1569_, lean_object* v_x_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
uint8_t v_builtin_boxed_1576_; lean_object* v_res_1577_; 
v_builtin_boxed_1576_ = lean_unbox(v_builtin_1569_);
v_res_1577_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1568_, v_builtin_boxed_1576_, v_x_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers(lean_object* v_00_u03b1_1578_, lean_object* v_ctx_1579_, uint8_t v_builtin_1580_, lean_object* v_x_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1579_, v_builtin_1580_, v_x_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___boxed(lean_object* v_00_u03b1_1588_, lean_object* v_ctx_1589_, lean_object* v_builtin_1590_, lean_object* v_x_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_){
_start:
{
uint8_t v_builtin_boxed_1597_; lean_object* v_res_1598_; 
v_builtin_boxed_1597_ = lean_unbox(v_builtin_1590_);
v_res_1598_ = l_Lean_ParserCompiler_compileEmbeddedParsers(v_00_u03b1_1588_, v_ctx_1589_, v_builtin_boxed_1597_, v_x_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
return v_res_1598_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = lean_box(0);
v___x_1600_ = l_Lean_Elab_abortCommandExceptionId;
v___x_1601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v___x_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg(){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0);
v___x_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___boxed(lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(lean_object* v_msgData_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; lean_object* v_toCold_1612_; lean_object* v_env_1613_; lean_object* v_options_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1611_ = lean_st_ref_get(v___y_1609_);
v_toCold_1612_ = lean_ctor_get(v___y_1608_, 0);
v_env_1613_ = lean_ctor_get(v___x_1611_, 0);
lean_inc_ref(v_env_1613_);
lean_dec(v___x_1611_);
v_options_1614_ = lean_ctor_get(v_toCold_1612_, 2);
v___x_1615_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1616_ = lean_unsigned_to_nat(32u);
v___x_1617_ = lean_mk_empty_array_with_capacity(v___x_1616_);
lean_dec_ref(v___x_1617_);
v___x_1618_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
lean_inc_ref(v_options_1614_);
v___x_1619_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1619_, 0, v_env_1613_);
lean_ctor_set(v___x_1619_, 1, v___x_1615_);
lean_ctor_set(v___x_1619_, 2, v___x_1618_);
lean_ctor_set(v___x_1619_, 3, v_options_1614_);
v___x_1620_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
lean_ctor_set(v___x_1620_, 1, v_msgData_1607_);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9___boxed(lean_object* v_msgData_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(v_msgData_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(lean_object* v_msg_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_ref_1631_; lean_object* v___x_1632_; lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1641_; 
v_ref_1631_ = lean_ctor_get(v___y_1628_, 2);
v___x_1632_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(v_msg_1627_, v___y_1628_, v___y_1629_);
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1641_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1641_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
lean_inc(v_ref_1631_);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_ref_1631_);
lean_ctor_set(v___x_1637_, 1, v_a_1633_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 1);
lean_ctor_set(v___x_1635_, 0, v___x_1637_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msg_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(lean_object* v_x_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
if (lean_obj_tag(v_x_1647_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_a_1651_ = lean_ctor_get(v_x_1647_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v_x_1647_, 1);
v___x_1652_ = l_Lean_stringToMessageData(v_a_1651_);
v___x_1653_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v___x_1652_, v___y_1648_, v___y_1649_);
return v___x_1653_;
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
v_a_1654_ = lean_ctor_get(v_x_1647_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_x_1647_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v_x_1647_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v_x_1647_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set_tag(v___x_1656_, 0);
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg___boxed(lean_object* v_x_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v_x_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(lean_object* v_typeName_1667_, lean_object* v_constName_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; lean_object* v_env_1673_; uint8_t v___x_1674_; 
v___x_1672_ = lean_st_ref_get(v___y_1670_);
v_env_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc_ref(v_env_1673_);
lean_dec(v___x_1672_);
lean_inc(v_constName_1668_);
v___x_1674_ = lean_has_compile_error(v_env_1673_, v_constName_1668_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; lean_object* v_toCold_1676_; lean_object* v_env_1677_; lean_object* v_options_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1675_ = lean_st_ref_get(v___y_1670_);
v_toCold_1676_ = lean_ctor_get(v___y_1669_, 0);
v_env_1677_ = lean_ctor_get(v___x_1675_, 0);
lean_inc_ref(v_env_1677_);
lean_dec(v___x_1675_);
v_options_1678_ = lean_ctor_get(v_toCold_1676_, 2);
v___x_1679_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1677_, v_options_1678_, v_typeName_1667_, v_constName_1668_);
v___x_1680_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v___x_1679_, v___y_1669_, v___y_1670_);
return v___x_1680_;
}
else
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v___x_1682_; lean_object* v_toCold_1683_; lean_object* v_env_1684_; lean_object* v_options_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec_ref_known(v___x_1681_, 1);
v___x_1682_ = lean_st_ref_get(v___y_1670_);
v_toCold_1683_ = lean_ctor_get(v___y_1669_, 0);
v_env_1684_ = lean_ctor_get(v___x_1682_, 0);
lean_inc_ref(v_env_1684_);
lean_dec(v___x_1682_);
v_options_1685_ = lean_ctor_get(v_toCold_1683_, 2);
v___x_1686_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1684_, v_options_1685_, v_typeName_1667_, v_constName_1668_);
v___x_1687_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v___x_1686_, v___y_1669_, v___y_1670_);
return v___x_1687_;
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec(v_constName_1668_);
lean_dec(v_typeName_1667_);
v_a_1688_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1681_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1681_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg___boxed(lean_object* v_typeName_1696_, lean_object* v_constName_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v_typeName_1696_, v_constName_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(lean_object* v_ref_1702_, lean_object* v_msg_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_toCold_1707_; lean_object* v_currRecDepth_1708_; lean_object* v_ref_1709_; uint8_t v_diag_1710_; uint8_t v_suppressElabErrors_1711_; lean_object* v_ref_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_toCold_1707_ = lean_ctor_get(v___y_1704_, 0);
v_currRecDepth_1708_ = lean_ctor_get(v___y_1704_, 1);
v_ref_1709_ = lean_ctor_get(v___y_1704_, 2);
v_diag_1710_ = lean_ctor_get_uint8(v___y_1704_, sizeof(void*)*3);
v_suppressElabErrors_1711_ = lean_ctor_get_uint8(v___y_1704_, sizeof(void*)*3 + 1);
v_ref_1712_ = l_Lean_replaceRef(v_ref_1702_, v_ref_1709_);
lean_inc(v_currRecDepth_1708_);
lean_inc_ref(v_toCold_1707_);
v___x_1713_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1713_, 0, v_toCold_1707_);
lean_ctor_set(v___x_1713_, 1, v_currRecDepth_1708_);
lean_ctor_set(v___x_1713_, 2, v_ref_1712_);
lean_ctor_set_uint8(v___x_1713_, sizeof(void*)*3, v_diag_1710_);
lean_ctor_set_uint8(v___x_1713_, sizeof(void*)*3 + 1, v_suppressElabErrors_1711_);
v___x_1714_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_1703_, v___x_1713_, v___y_1705_);
lean_dec_ref_known(v___x_1713_, 3);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg___boxed(lean_object* v_ref_1715_, lean_object* v_msg_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_1715_, v_msg_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v_ref_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(lean_object* v_msg_1721_, lean_object* v_declHint_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v_env_1727_; uint8_t v___x_1728_; 
v___x_1725_ = lean_box(0);
v___x_1726_ = lean_st_ref_get(v___y_1723_);
v_env_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc_ref(v_env_1727_);
lean_dec(v___x_1726_);
v___x_1728_ = l_Lean_Name_isAnonymous(v_declHint_1722_);
if (v___x_1728_ == 0)
{
uint8_t v_isExporting_1729_; 
v_isExporting_1729_ = lean_ctor_get_uint8(v_env_1727_, sizeof(void*)*8);
if (v_isExporting_1729_ == 0)
{
lean_object* v___x_1730_; 
lean_dec_ref(v_env_1727_);
lean_dec(v_declHint_1722_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_msg_1721_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
lean_inc_ref(v_env_1727_);
v___x_1731_ = l_Lean_Environment_setExporting(v_env_1727_, v___x_1728_);
lean_inc(v_declHint_1722_);
lean_inc_ref(v___x_1731_);
v___x_1732_ = l_Lean_Environment_contains(v___x_1731_, v_declHint_1722_, v_isExporting_1729_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; 
lean_dec_ref(v___x_1731_);
lean_dec_ref(v_env_1727_);
lean_dec(v_declHint_1722_);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_msg_1721_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v_c_1741_; lean_object* v___x_1742_; 
v___x_1734_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1735_ = lean_unsigned_to_nat(32u);
v___x_1736_ = lean_mk_empty_array_with_capacity(v___x_1735_);
lean_dec_ref(v___x_1736_);
v___x_1737_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1738_ = l_Lean_Options_empty;
v___x_1739_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1731_);
lean_ctor_set(v___x_1739_, 1, v___x_1734_);
lean_ctor_set(v___x_1739_, 2, v___x_1737_);
lean_ctor_set(v___x_1739_, 3, v___x_1738_);
lean_inc(v_declHint_1722_);
v___x_1740_ = l_Lean_MessageData_ofConstName(v_declHint_1722_, v___x_1728_);
v_c_1741_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1741_, 0, v___x_1739_);
lean_ctor_set(v_c_1741_, 1, v___x_1740_);
v___x_1742_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1727_, v_declHint_1722_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
lean_dec_ref(v_env_1727_);
lean_dec(v_declHint_1722_);
v___x_1743_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v_c_1741_);
v___x_1745_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = l_Lean_MessageData_note(v___x_1746_);
v___x_1748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_msg_1721_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
else
{
lean_object* v_val_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1784_; 
v_val_1750_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1752_ = v___x_1742_;
v_isShared_1753_ = v_isSharedCheck_1784_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_val_1750_);
lean_dec(v___x_1742_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1784_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v_mod_1756_; uint8_t v___x_1757_; 
v___x_1754_ = l_Lean_Environment_header(v_env_1727_);
lean_dec_ref(v_env_1727_);
v___x_1755_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1754_);
v_mod_1756_ = lean_array_get(v___x_1725_, v___x_1755_, v_val_1750_);
lean_dec(v_val_1750_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = l_Lean_isPrivateName(v_declHint_1722_);
lean_dec(v_declHint_1722_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1758_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v_c_1741_);
v___x_1760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = l_Lean_MessageData_ofName(v_mod_1756_);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_MessageData_note(v___x_1765_);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_msg_1721_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set_tag(v___x_1752_, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1767_);
v___x_1769_ = v___x_1752_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1771_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v_c_1741_);
v___x_1773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_MessageData_ofName(v_mod_1756_);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = l_Lean_MessageData_note(v___x_1778_);
v___x_1780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1780_, 0, v_msg_1721_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set_tag(v___x_1752_, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1780_);
v___x_1782_ = v___x_1752_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1785_; 
lean_dec_ref(v_env_1727_);
lean_dec(v_declHint_1722_);
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_msg_1721_);
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg___boxed(lean_object* v_msg_1786_, lean_object* v_declHint_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_1786_, v_declHint_1787_, v___y_1788_);
lean_dec(v___y_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(lean_object* v_msg_1791_, lean_object* v_declHint_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1806_; 
v___x_1796_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_1791_, v_declHint_1792_, v___y_1794_);
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1806_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1806_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1801_ = l_Lean_unknownIdentifierMessageTag;
v___x_1802_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
lean_ctor_set(v___x_1802_, 1, v_a_1797_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1802_);
v___x_1804_ = v___x_1799_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8___boxed(lean_object* v_msg_1807_, lean_object* v_declHint_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_1807_, v_declHint_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_ref_1813_, lean_object* v_msg_1814_, lean_object* v_declHint_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; lean_object* v_a_1820_; lean_object* v___x_1821_; 
v___x_1819_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_1814_, v_declHint_1815_, v___y_1816_, v___y_1817_);
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1819_);
v___x_1821_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_1813_, v_a_1820_, v___y_1816_, v___y_1817_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_ref_1822_, lean_object* v_msg_1823_, lean_object* v_declHint_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1822_, v_msg_1823_, v_declHint_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v_ref_1822_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1829_, lean_object* v_constName_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1834_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_1835_ = 0;
lean_inc(v_constName_1830_);
v___x_1836_ = l_Lean_MessageData_ofConstName(v_constName_1830_, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1834_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1829_, v___x_1839_, v_constName_1830_, v___y_1831_, v___y_1832_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1841_, lean_object* v_constName_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_1841_, v_constName_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v_ref_1841_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(lean_object* v_constName_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_ref_1851_; lean_object* v___x_1852_; 
v_ref_1851_ = lean_ctor_get(v___y_1848_, 2);
v___x_1852_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_1851_, v_constName_1847_, v___y_1848_, v___y_1849_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(lean_object* v_constName_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; lean_object* v_env_1863_; uint8_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1862_ = lean_st_ref_get(v___y_1860_);
v_env_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc_ref(v_env_1863_);
lean_dec(v___x_1862_);
v___x_1864_ = 0;
lean_inc(v_constName_1858_);
v___x_1865_ = l_Lean_Environment_find_x3f(v_env_1863_, v_constName_1858_, v___x_1864_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_1858_, v___y_1859_, v___y_1860_);
return v___x_1866_;
}
else
{
lean_object* v_val_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_constName_1858_);
v_val_1867_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1865_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_val_1867_);
lean_dec(v___x_1865_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 0);
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_val_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0___boxed(lean_object* v_constName_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(v_constName_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1879_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1882_ = lean_box(1);
v___x_1883_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1884_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v___x_1883_);
lean_ctor_set(v___x_1885_, 2, v___x_1882_);
return v___x_1885_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
lean_ctor_set(v___x_1890_, 2, v___x_1889_);
lean_ctor_set(v___x_1890_, 3, v___x_1889_);
lean_ctor_set(v___x_1890_, 4, v___x_1888_);
lean_ctor_set(v___x_1890_, 5, v___x_1888_);
lean_ctor_set(v___x_1890_, 6, v___x_1888_);
lean_ctor_set(v___x_1890_, 7, v___x_1888_);
lean_ctor_set(v___x_1890_, 8, v___x_1888_);
lean_ctor_set(v___x_1890_, 9, v___x_1888_);
lean_ctor_set(v___x_1890_, 10, v___x_1888_);
return v___x_1890_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1892_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
lean_ctor_set(v___x_1892_, 2, v___x_1891_);
lean_ctor_set(v___x_1892_, 3, v___x_1891_);
lean_ctor_set(v___x_1892_, 4, v___x_1891_);
lean_ctor_set(v___x_1892_, 5, v___x_1891_);
return v___x_1892_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
lean_ctor_set(v___x_1894_, 2, v___x_1893_);
lean_ctor_set(v___x_1894_, 3, v___x_1893_);
lean_ctor_set(v___x_1894_, 4, v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(lean_object* v___x_1903_, lean_object* v_ctx_1904_, uint8_t v_builtin_1905_, lean_object* v_constName_1906_, lean_object* v_catName_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
uint8_t v___y_1912_; uint8_t v___y_1913_; lean_object* v___y_1914_; lean_object* v___x_1952_; 
lean_inc(v_constName_1906_);
v___x_1952_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(v_constName_1906_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; uint8_t v___y_1956_; lean_object* v___y_1957_; uint8_t v___y_1958_; uint8_t v___y_1959_; lean_object* v___x_1962_; uint8_t v___y_1964_; uint8_t v___x_2017_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1954_ = l_Lean_ConstantInfo_type(v_a_1953_);
lean_dec(v_a_1953_);
v___x_1962_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9));
v___x_2017_ = l_Lean_Expr_isConstOf(v___x_1954_, v___x_1962_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7));
v___x_2019_ = l_Lean_Expr_isConstOf(v___x_1954_, v___x_2018_);
lean_dec_ref(v___x_1954_);
v___y_1964_ = v___x_2019_;
goto v___jp_1963_;
}
else
{
lean_dec_ref(v___x_1954_);
v___y_1964_ = v___x_2017_;
goto v___jp_1963_;
}
v___jp_1955_:
{
if (v___y_1959_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec_ref(v___y_1957_);
v___x_1960_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7));
v___x_1961_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v___x_1960_, v_constName_1906_, v___y_1908_, v___y_1909_);
v___y_1912_ = v___y_1956_;
v___y_1913_ = v___y_1958_;
v___y_1914_ = v___x_1961_;
goto v___jp_1911_;
}
else
{
lean_dec(v_constName_1906_);
v___y_1912_ = v___y_1956_;
v___y_1913_ = v___y_1958_;
v___y_1914_ = v___y_1957_;
goto v___jp_1911_;
}
}
v___jp_1963_:
{
uint8_t v___x_1965_; 
v___x_1965_ = 1;
if (v___y_1964_ == 0)
{
uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; uint8_t v___x_1970_; uint8_t v___x_1971_; lean_object* v___x_1972_; uint64_t v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1966_ = l_Lean_Name_isAnonymous(v_catName_1907_);
v___x_1967_ = lean_box(0);
v___x_1968_ = l_Lean_mkConst(v_constName_1906_, v___x_1967_);
v___x_1969_ = 1;
v___x_1970_ = 0;
v___x_1971_ = 2;
v___x_1972_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1972_, 0, v___y_1964_);
lean_ctor_set_uint8(v___x_1972_, 1, v___y_1964_);
lean_ctor_set_uint8(v___x_1972_, 2, v___y_1964_);
lean_ctor_set_uint8(v___x_1972_, 3, v___y_1964_);
lean_ctor_set_uint8(v___x_1972_, 4, v___y_1964_);
lean_ctor_set_uint8(v___x_1972_, 5, v___x_1965_);
lean_ctor_set_uint8(v___x_1972_, 6, v___x_1965_);
lean_ctor_set_uint8(v___x_1972_, 7, v___y_1964_);
lean_ctor_set_uint8(v___x_1972_, 8, v___x_1965_);
lean_ctor_set_uint8(v___x_1972_, 9, v___x_1969_);
lean_ctor_set_uint8(v___x_1972_, 10, v___x_1970_);
lean_ctor_set_uint8(v___x_1972_, 11, v___x_1965_);
lean_ctor_set_uint8(v___x_1972_, 12, v___x_1965_);
lean_ctor_set_uint8(v___x_1972_, 13, v___x_1965_);
lean_ctor_set_uint8(v___x_1972_, 14, v___x_1971_);
lean_ctor_set_uint8(v___x_1972_, 15, v___x_1965_);
lean_ctor_set_uint8(v___x_1972_, 16, v___x_1965_);
lean_ctor_set_uint8(v___x_1972_, 17, v___x_1965_);
lean_ctor_set_uint8(v___x_1972_, 18, v___x_1965_);
lean_ctor_set_uint8(v___x_1972_, 19, v___y_1964_);
v___x_1973_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1972_);
v___x_1974_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set_uint64(v___x_1974_, sizeof(void*)*1, v___x_1973_);
v___x_1975_ = lean_unsigned_to_nat(0u);
v___x_1976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1977_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1978_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2));
v___x_1979_ = lean_box(0);
lean_inc(v___x_1903_);
v___x_1980_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1980_, 0, v___x_1974_);
lean_ctor_set(v___x_1980_, 1, v___x_1903_);
lean_ctor_set(v___x_1980_, 2, v___x_1977_);
lean_ctor_set(v___x_1980_, 3, v___x_1978_);
lean_ctor_set(v___x_1980_, 4, v___x_1979_);
lean_ctor_set(v___x_1980_, 5, v___x_1975_);
lean_ctor_set(v___x_1980_, 6, v___x_1979_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*7, v___y_1964_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*7 + 1, v___y_1964_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*7 + 2, v___y_1964_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*7 + 3, v___x_1965_);
v___x_1981_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3);
v___x_1982_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4);
v___x_1983_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5);
v___x_1984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1981_);
lean_ctor_set(v___x_1984_, 1, v___x_1982_);
lean_ctor_set(v___x_1984_, 2, v___x_1903_);
lean_ctor_set(v___x_1984_, 3, v___x_1976_);
lean_ctor_set(v___x_1984_, 4, v___x_1983_);
v___x_1985_ = lean_box(0);
v___x_1986_ = lean_st_mk_ref(v___x_1984_);
v___x_1987_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1904_, v_builtin_1905_, v___x_1966_, v___x_1968_, v___x_1980_, v___x_1986_, v___y_1908_, v___y_1909_);
lean_dec_ref_known(v___x_1980_, 7);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1995_; 
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v___x_1987_, 0);
lean_dec(v_unused_1996_);
v___x_1989_ = v___x_1987_;
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
else
{
lean_dec(v___x_1987_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1991_ = lean_st_ref_get(v___x_1986_);
lean_dec(v___x_1986_);
lean_dec(v___x_1991_);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_1985_);
v___x_1993_ = v___x_1989_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1985_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
lean_dec(v___x_1986_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v___x_1987_, 0);
lean_dec(v_unused_2004_);
v___x_1998_ = v___x_1987_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_dec(v___x_1987_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1985_);
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1985_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
v_a_2005_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1987_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1987_);
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
else
{
lean_object* v___x_2013_; 
lean_inc(v_constName_1906_);
v___x_2013_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v___x_1962_, v_constName_1906_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_dec(v_constName_1906_);
v___y_1912_ = v___x_1965_;
v___y_1913_ = v___y_1964_;
v___y_1914_ = v___x_2013_;
goto v___jp_1911_;
}
else
{
lean_object* v_a_2014_; uint8_t v___x_2015_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
v___x_2015_ = l_Lean_Exception_isInterrupt(v_a_2014_);
if (v___x_2015_ == 0)
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_Exception_isRuntime(v_a_2014_);
v___y_1956_ = v___x_1965_;
v___y_1957_ = v___x_2013_;
v___y_1958_ = v___y_1964_;
v___y_1959_ = v___x_2016_;
goto v___jp_1955_;
}
else
{
lean_dec(v_a_2014_);
v___y_1956_ = v___x_1965_;
v___y_1957_ = v___x_2013_;
v___y_1958_ = v___y_1964_;
v___y_1959_ = v___x_2015_;
goto v___jp_1955_;
}
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_constName_1906_);
lean_dec_ref(v_ctx_1904_);
lean_dec(v___x_1903_);
v_a_2020_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1952_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1952_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
v___jp_1911_:
{
if (lean_obj_tag(v___y_1914_) == 0)
{
lean_object* v_a_1915_; uint8_t v___x_1916_; uint8_t v___x_1917_; uint8_t v___x_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; uint64_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v_a_1915_ = lean_ctor_get(v___y_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___y_1914_, 1);
v___x_1916_ = 0;
v___x_1917_ = 1;
v___x_1918_ = 0;
v___x_1919_ = 2;
v___x_1920_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1920_, 0, v___x_1916_);
lean_ctor_set_uint8(v___x_1920_, 1, v___x_1916_);
lean_ctor_set_uint8(v___x_1920_, 2, v___x_1916_);
lean_ctor_set_uint8(v___x_1920_, 3, v___x_1916_);
lean_ctor_set_uint8(v___x_1920_, 4, v___x_1916_);
lean_ctor_set_uint8(v___x_1920_, 5, v___y_1913_);
lean_ctor_set_uint8(v___x_1920_, 6, v___y_1913_);
lean_ctor_set_uint8(v___x_1920_, 7, v___x_1916_);
lean_ctor_set_uint8(v___x_1920_, 8, v___y_1913_);
lean_ctor_set_uint8(v___x_1920_, 9, v___x_1917_);
lean_ctor_set_uint8(v___x_1920_, 10, v___x_1918_);
lean_ctor_set_uint8(v___x_1920_, 11, v___y_1913_);
lean_ctor_set_uint8(v___x_1920_, 12, v___y_1913_);
lean_ctor_set_uint8(v___x_1920_, 13, v___y_1913_);
lean_ctor_set_uint8(v___x_1920_, 14, v___x_1919_);
lean_ctor_set_uint8(v___x_1920_, 15, v___y_1913_);
lean_ctor_set_uint8(v___x_1920_, 16, v___y_1913_);
lean_ctor_set_uint8(v___x_1920_, 17, v___y_1913_);
lean_ctor_set_uint8(v___x_1920_, 18, v___y_1913_);
lean_ctor_set_uint8(v___x_1920_, 19, v___x_1916_);
v___x_1921_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1920_);
v___x_1922_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set_uint64(v___x_1922_, sizeof(void*)*1, v___x_1921_);
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1925_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1926_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2));
v___x_1927_ = lean_box(0);
lean_inc(v___x_1903_);
v___x_1928_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1928_, 0, v___x_1922_);
lean_ctor_set(v___x_1928_, 1, v___x_1903_);
lean_ctor_set(v___x_1928_, 2, v___x_1925_);
lean_ctor_set(v___x_1928_, 3, v___x_1926_);
lean_ctor_set(v___x_1928_, 4, v___x_1927_);
lean_ctor_set(v___x_1928_, 5, v___x_1923_);
lean_ctor_set(v___x_1928_, 6, v___x_1927_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*7, v___x_1916_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*7 + 1, v___x_1916_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*7 + 2, v___x_1916_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*7 + 3, v___y_1912_);
v___x_1929_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3);
v___x_1930_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4);
v___x_1931_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5);
v___x_1932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1929_);
lean_ctor_set(v___x_1932_, 1, v___x_1930_);
lean_ctor_set(v___x_1932_, 2, v___x_1903_);
lean_ctor_set(v___x_1932_, 3, v___x_1924_);
lean_ctor_set(v___x_1932_, 4, v___x_1931_);
v___x_1933_ = lean_st_mk_ref(v___x_1932_);
v___x_1934_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1904_, v_builtin_1905_, v_a_1915_, v___x_1928_, v___x_1933_, v___y_1908_, v___y_1909_);
lean_dec_ref_known(v___x_1928_, 7);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1943_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1943_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1943_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1939_ = lean_st_ref_get(v___x_1933_);
lean_dec(v___x_1933_);
lean_dec(v___x_1939_);
if (v_isShared_1938_ == 0)
{
v___x_1941_ = v___x_1937_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1935_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
else
{
lean_dec(v___x_1933_);
return v___x_1934_;
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v_ctx_1904_);
lean_dec(v___x_1903_);
v_a_1944_ = lean_ctor_get(v___y_1914_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___y_1914_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___y_1914_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___y_1914_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed(lean_object* v___x_2028_, lean_object* v_ctx_2029_, lean_object* v_builtin_2030_, lean_object* v_constName_2031_, lean_object* v_catName_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
uint8_t v_builtin_boxed_2036_; lean_object* v_res_2037_; 
v_builtin_boxed_2036_ = lean_unbox(v_builtin_2030_);
v_res_2037_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(v___x_2028_, v_ctx_2029_, v_builtin_boxed_2036_, v_constName_2031_, v_catName_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v_catName_2032_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(lean_object* v___y_2038_, uint8_t v_isExporting_2039_, lean_object* v___x_2040_, lean_object* v_a_x3f_2041_){
_start:
{
lean_object* v___x_2043_; lean_object* v_env_2044_; lean_object* v_nextMacroScope_2045_; lean_object* v_ngen_2046_; lean_object* v_auxDeclNGen_2047_; lean_object* v_traceState_2048_; lean_object* v_messages_2049_; lean_object* v_infoState_2050_; lean_object* v_snapshotTasks_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2062_; 
v___x_2043_ = lean_st_ref_take(v___y_2038_);
v_env_2044_ = lean_ctor_get(v___x_2043_, 0);
v_nextMacroScope_2045_ = lean_ctor_get(v___x_2043_, 1);
v_ngen_2046_ = lean_ctor_get(v___x_2043_, 2);
v_auxDeclNGen_2047_ = lean_ctor_get(v___x_2043_, 3);
v_traceState_2048_ = lean_ctor_get(v___x_2043_, 4);
v_messages_2049_ = lean_ctor_get(v___x_2043_, 6);
v_infoState_2050_ = lean_ctor_get(v___x_2043_, 7);
v_snapshotTasks_2051_ = lean_ctor_get(v___x_2043_, 8);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; 
v_unused_2063_ = lean_ctor_get(v___x_2043_, 5);
lean_dec(v_unused_2063_);
v___x_2053_ = v___x_2043_;
v_isShared_2054_ = v_isSharedCheck_2062_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_snapshotTasks_2051_);
lean_inc(v_infoState_2050_);
lean_inc(v_messages_2049_);
lean_inc(v_traceState_2048_);
lean_inc(v_auxDeclNGen_2047_);
lean_inc(v_ngen_2046_);
lean_inc(v_nextMacroScope_2045_);
lean_inc(v_env_2044_);
lean_dec(v___x_2043_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2062_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2055_ = lean_box(0);
v___x_2056_ = l_Lean_Environment_setExporting(v_env_2044_, v_isExporting_2039_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 5, v___x_2040_);
lean_ctor_set(v___x_2053_, 0, v___x_2056_);
v___x_2058_ = v___x_2053_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_nextMacroScope_2045_);
lean_ctor_set(v_reuseFailAlloc_2061_, 2, v_ngen_2046_);
lean_ctor_set(v_reuseFailAlloc_2061_, 3, v_auxDeclNGen_2047_);
lean_ctor_set(v_reuseFailAlloc_2061_, 4, v_traceState_2048_);
lean_ctor_set(v_reuseFailAlloc_2061_, 5, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2061_, 6, v_messages_2049_);
lean_ctor_set(v_reuseFailAlloc_2061_, 7, v_infoState_2050_);
lean_ctor_set(v_reuseFailAlloc_2061_, 8, v_snapshotTasks_2051_);
v___x_2058_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_st_ref_put(v___y_2038_, v___x_2058_);
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2055_);
return v___x_2060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v___y_2064_, lean_object* v_isExporting_2065_, lean_object* v___x_2066_, lean_object* v_a_x3f_2067_, lean_object* v___y_2068_){
_start:
{
uint8_t v_isExporting_boxed_2069_; lean_object* v_res_2070_; 
v_isExporting_boxed_2069_ = lean_unbox(v_isExporting_2065_);
v_res_2070_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2064_, v_isExporting_boxed_2069_, v___x_2066_, v_a_x3f_2067_);
lean_dec(v_a_x3f_2067_);
lean_dec(v___y_2064_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(lean_object* v_x_2071_, uint8_t v_isExporting_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___x_2076_; lean_object* v_env_2077_; lean_object* v___x_2078_; uint8_t v_isModule_2079_; 
v___x_2076_ = lean_st_ref_get(v___y_2074_);
v_env_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc_ref(v_env_2077_);
lean_dec(v___x_2076_);
v___x_2078_ = l_Lean_Environment_header(v_env_2077_);
v_isModule_2079_ = lean_ctor_get_uint8(v___x_2078_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2078_);
if (v_isModule_2079_ == 0)
{
lean_object* v___x_2080_; 
lean_dec_ref(v_env_2077_);
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
v___x_2080_ = lean_apply_3(v_x_2071_, v___y_2073_, v___y_2074_, lean_box(0));
return v___x_2080_;
}
else
{
uint8_t v_isExporting_2081_; 
v_isExporting_2081_ = lean_ctor_get_uint8(v_env_2077_, sizeof(void*)*8);
lean_dec_ref(v_env_2077_);
if (v_isExporting_2072_ == 0)
{
if (v_isExporting_2081_ == 0)
{
lean_object* v___x_2132_; 
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
v___x_2132_ = lean_apply_3(v_x_2071_, v___y_2073_, v___y_2074_, lean_box(0));
return v___x_2132_;
}
else
{
goto v___jp_2082_;
}
}
else
{
if (v_isExporting_2081_ == 0)
{
goto v___jp_2082_;
}
else
{
lean_object* v___x_2133_; 
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
v___x_2133_ = lean_apply_3(v_x_2071_, v___y_2073_, v___y_2074_, lean_box(0));
return v___x_2133_;
}
}
v___jp_2082_:
{
lean_object* v___x_2083_; lean_object* v_env_2084_; lean_object* v_nextMacroScope_2085_; lean_object* v_ngen_2086_; lean_object* v_auxDeclNGen_2087_; lean_object* v_traceState_2088_; lean_object* v_messages_2089_; lean_object* v_infoState_2090_; lean_object* v_snapshotTasks_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2130_; 
v___x_2083_ = lean_st_ref_take(v___y_2074_);
v_env_2084_ = lean_ctor_get(v___x_2083_, 0);
v_nextMacroScope_2085_ = lean_ctor_get(v___x_2083_, 1);
v_ngen_2086_ = lean_ctor_get(v___x_2083_, 2);
v_auxDeclNGen_2087_ = lean_ctor_get(v___x_2083_, 3);
v_traceState_2088_ = lean_ctor_get(v___x_2083_, 4);
v_messages_2089_ = lean_ctor_get(v___x_2083_, 6);
v_infoState_2090_ = lean_ctor_get(v___x_2083_, 7);
v_snapshotTasks_2091_ = lean_ctor_get(v___x_2083_, 8);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v___x_2083_, 5);
lean_dec(v_unused_2131_);
v___x_2093_ = v___x_2083_;
v_isShared_2094_ = v_isSharedCheck_2130_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_snapshotTasks_2091_);
lean_inc(v_infoState_2090_);
lean_inc(v_messages_2089_);
lean_inc(v_traceState_2088_);
lean_inc(v_auxDeclNGen_2087_);
lean_inc(v_ngen_2086_);
lean_inc(v_nextMacroScope_2085_);
lean_inc(v_env_2084_);
lean_dec(v___x_2083_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2130_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2095_ = l_Lean_Environment_setExporting(v_env_2084_, v_isExporting_2072_);
v___x_2096_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 5, v___x_2096_);
lean_ctor_set(v___x_2093_, 0, v___x_2095_);
v___x_2098_ = v___x_2093_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_nextMacroScope_2085_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_ngen_2086_);
lean_ctor_set(v_reuseFailAlloc_2129_, 3, v_auxDeclNGen_2087_);
lean_ctor_set(v_reuseFailAlloc_2129_, 4, v_traceState_2088_);
lean_ctor_set(v_reuseFailAlloc_2129_, 5, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2129_, 6, v_messages_2089_);
lean_ctor_set(v_reuseFailAlloc_2129_, 7, v_infoState_2090_);
lean_ctor_set(v_reuseFailAlloc_2129_, 8, v_snapshotTasks_2091_);
v___x_2098_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; lean_object* v_r_2100_; 
v___x_2099_ = lean_st_ref_put(v___y_2074_, v___x_2098_);
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
v_r_2100_ = lean_apply_3(v_x_2071_, v___y_2073_, v___y_2074_, lean_box(0));
if (lean_obj_tag(v_r_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2117_; 
v_a_2101_ = lean_ctor_get(v_r_2100_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_r_2100_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2103_ = v_r_2100_;
v_isShared_2104_ = v_isSharedCheck_2117_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v_r_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2117_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
lean_inc(v_a_2101_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set_tag(v___x_2103_, 1);
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
v___x_2107_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2074_, v_isExporting_2081_, v___x_2096_, v___x_2106_);
lean_dec_ref(v___x_2106_);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; 
v_unused_2115_ = lean_ctor_get(v___x_2107_, 0);
lean_dec(v_unused_2115_);
v___x_2109_ = v___x_2107_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_dec(v___x_2107_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v_a_2101_);
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2101_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
v_a_2118_ = lean_ctor_get(v_r_2100_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v_r_2100_, 1);
v___x_2119_ = lean_box(0);
v___x_2120_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2074_, v_isExporting_2081_, v___x_2096_, v___x_2119_);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; 
v_unused_2128_ = lean_ctor_get(v___x_2120_, 0);
lean_dec(v_unused_2128_);
v___x_2122_ = v___x_2120_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_dec(v___x_2120_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
lean_ctor_set_tag(v___x_2122_, 1);
lean_ctor_set(v___x_2122_, 0, v_a_2118_);
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2118_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___boxed(lean_object* v_x_2134_, lean_object* v_isExporting_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
uint8_t v_isExporting_boxed_2139_; lean_object* v_res_2140_; 
v_isExporting_boxed_2139_ = lean_unbox(v_isExporting_2135_);
v_res_2140_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2134_, v_isExporting_boxed_2139_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(lean_object* v_x_2141_, uint8_t v_when_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
if (v_when_2142_ == 0)
{
lean_object* v___x_2146_; 
lean_inc(v___y_2144_);
lean_inc_ref(v___y_2143_);
v___x_2146_ = lean_apply_3(v_x_2141_, v___y_2143_, v___y_2144_, lean_box(0));
return v___x_2146_;
}
else
{
uint8_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = 0;
v___x_2148_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2141_, v___x_2147_, v___y_2143_, v___y_2144_);
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg___boxed(lean_object* v_x_2149_, lean_object* v_when_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
uint8_t v_when_boxed_2154_; lean_object* v_res_2155_; 
v_when_boxed_2154_ = lean_unbox(v_when_2150_);
v_res_2155_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v_x_2149_, v_when_boxed_2154_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(lean_object* v___x_2156_, lean_object* v_ctx_2157_, lean_object* v_catName_2158_, lean_object* v_constName_2159_, uint8_t v_builtin_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; lean_object* v___f_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2164_ = lean_box(v_builtin_2160_);
v___f_2165_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed), 8, 5);
lean_closure_set(v___f_2165_, 0, v___x_2156_);
lean_closure_set(v___f_2165_, 1, v_ctx_2157_);
lean_closure_set(v___f_2165_, 2, v___x_2164_);
lean_closure_set(v___f_2165_, 3, v_constName_2159_);
lean_closure_set(v___f_2165_, 4, v_catName_2158_);
v___x_2166_ = 1;
v___x_2167_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v___f_2165_, v___x_2166_, v___y_2161_, v___y_2162_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed(lean_object* v___x_2168_, lean_object* v_ctx_2169_, lean_object* v_catName_2170_, lean_object* v_constName_2171_, lean_object* v_builtin_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
uint8_t v_builtin_boxed_2176_; lean_object* v_res_2177_; 
v_builtin_boxed_2176_ = lean_unbox(v_builtin_2172_);
v_res_2177_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(v___x_2168_, v_ctx_2169_, v_catName_2170_, v_constName_2171_, v_builtin_boxed_2176_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg(lean_object* v_ctx_2178_){
_start:
{
lean_object* v___x_2180_; lean_object* v___f_2181_; lean_object* v___x_2182_; 
v___x_2180_ = lean_box(1);
v___f_2181_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed), 8, 2);
lean_closure_set(v___f_2181_, 0, v___x_2180_);
lean_closure_set(v___f_2181_, 1, v_ctx_2178_);
v___x_2182_ = l_Lean_Parser_registerParserAttributeHook(v___f_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___boxed(lean_object* v_ctx_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v_ctx_2183_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object* v_00_u03b1_2186_, lean_object* v_ctx_2187_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v_ctx_2187_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___boxed(lean_object* v_00_u03b1_2190_, lean_object* v_ctx_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_ParserCompiler_registerParserCompiler(v_00_u03b1_2190_, v_ctx_2191_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(lean_object* v_00_u03b1_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(v_00_u03b1_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(lean_object* v_00_u03b1_2204_, lean_object* v_typeName_2205_, lean_object* v_constName_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v_typeName_2205_, v_constName_2206_, v___y_2207_, v___y_2208_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___boxed(lean_object* v_00_u03b1_2211_, lean_object* v_typeName_2212_, lean_object* v_constName_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(v_00_u03b1_2211_, v_typeName_2212_, v_constName_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(lean_object* v_00_u03b1_2218_, lean_object* v_x_2219_, uint8_t v_isExporting_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2219_, v_isExporting_2220_, v___y_2221_, v___y_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2225_, lean_object* v_x_2226_, lean_object* v_isExporting_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
uint8_t v_isExporting_boxed_2231_; lean_object* v_res_2232_; 
v_isExporting_boxed_2231_ = lean_unbox(v_isExporting_2227_);
v_res_2232_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(v_00_u03b1_2225_, v_x_2226_, v_isExporting_boxed_2231_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(lean_object* v_00_u03b1_2233_, lean_object* v_x_2234_, uint8_t v_when_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v_x_2234_, v_when_2235_, v___y_2236_, v___y_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___boxed(lean_object* v_00_u03b1_2240_, lean_object* v_x_2241_, lean_object* v_when_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
uint8_t v_when_boxed_2246_; lean_object* v_res_2247_; 
v_when_boxed_2246_ = lean_unbox(v_when_2242_);
v_res_2247_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(v_00_u03b1_2240_, v_x_2241_, v_when_boxed_2246_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(lean_object* v_00_u03b1_2248_, lean_object* v_constName_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_2249_, v___y_2250_, v___y_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2254_, lean_object* v_constName_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(v_00_u03b1_2254_, v_constName_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(lean_object* v_00_u03b1_2260_, lean_object* v_x_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v_x_2261_, v___y_2262_, v___y_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2266_, lean_object* v_x_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(v_00_u03b1_2266_, v_x_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2272_, lean_object* v_ref_2273_, lean_object* v_constName_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_2273_, v_constName_2274_, v___y_2275_, v___y_2276_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2279_, lean_object* v_ref_2280_, lean_object* v_constName_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(v_00_u03b1_2279_, v_ref_2280_, v_constName_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v_ref_2280_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2286_, lean_object* v_msg_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_2287_, v___y_2288_, v___y_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2292_, lean_object* v_msg_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(v_00_u03b1_2292_, v_msg_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b1_2298_, lean_object* v_ref_2299_, lean_object* v_msg_2300_, lean_object* v_declHint_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_2299_, v_msg_2300_, v_declHint_2301_, v___y_2302_, v___y_2303_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b1_2306_, lean_object* v_ref_2307_, lean_object* v_msg_2308_, lean_object* v_declHint_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_2306_, v_ref_2307_, v_msg_2308_, v_declHint_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v_ref_2307_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(lean_object* v_msg_2314_, lean_object* v_declHint_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_2314_, v_declHint_2315_, v___y_2317_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___boxed(lean_object* v_msg_2320_, lean_object* v_declHint_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(v_msg_2320_, v_declHint_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_2326_, lean_object* v_ref_2327_, lean_object* v_msg_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_2327_, v_msg_2328_, v___y_2329_, v___y_2330_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2333_, lean_object* v_ref_2334_, lean_object* v_msg_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(v_00_u03b1_2333_, v_ref_2334_, v_msg_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v_ref_2334_);
return v_res_2339_;
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
