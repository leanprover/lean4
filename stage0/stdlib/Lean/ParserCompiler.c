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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*, uint8_t);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "don't know how to generate "};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " for non-parser combinator `"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "refusing to generate code for imported parser declaration `"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14;
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "`; use `@[run_parser_attribute_hooks]` on its definition instead."};
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
static const lean_string_object l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "call of unknown parser at `"};
static const lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21 = (const lean_object*)&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21_value;
static lean_once_cell_t l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2;
static const lean_array_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4;
static lean_once_cell_t l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5;
static lean_once_cell_t l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6;
static lean_once_cell_t l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7;
static const lean_string_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "TrailingParserDescr"};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(73, 30, 7, 95, 84, 115, 124, 250)}};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value;
static const lean_string_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ParserDescr"};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__10 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(92, 191, 134, 190, 206, 60, 55, 123)}};
static const lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11 = (const lean_object*)&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_141_; lean_object* v___x_156_; uint8_t v_transparency_157_; uint8_t v___x_158_; uint8_t v___x_159_; 
v___x_156_ = l_Lean_Meta_Context_config(v_a_135_);
v_transparency_157_ = lean_ctor_get_uint8(v___x_156_, 9);
lean_dec_ref(v___x_156_);
v___x_158_ = 1;
v___x_159_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_157_, v___x_158_);
if (v___x_159_ == 0)
{
v___y_141_ = v_transparency_157_;
goto v___jp_140_;
}
else
{
v___y_141_ = v___x_158_;
goto v___jp_140_;
}
v___jp_140_:
{
lean_object* v_keyedConfig_142_; uint8_t v_trackZetaDelta_143_; lean_object* v_zetaDeltaSet_144_; lean_object* v_lctx_145_; lean_object* v_localInstances_146_; lean_object* v_defEqCtx_x3f_147_; lean_object* v_synthPendingDepth_148_; lean_object* v_customCanUnfoldPredicate_x3f_149_; uint8_t v_univApprox_150_; uint8_t v_inTypeClassResolution_151_; uint8_t v_cacheInferType_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_keyedConfig_142_ = lean_ctor_get(v_a_135_, 0);
v_trackZetaDelta_143_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*7);
v_zetaDeltaSet_144_ = lean_ctor_get(v_a_135_, 1);
v_lctx_145_ = lean_ctor_get(v_a_135_, 2);
v_localInstances_146_ = lean_ctor_get(v_a_135_, 3);
v_defEqCtx_x3f_147_ = lean_ctor_get(v_a_135_, 4);
v_synthPendingDepth_148_ = lean_ctor_get(v_a_135_, 5);
v_customCanUnfoldPredicate_x3f_149_ = lean_ctor_get(v_a_135_, 6);
v_univApprox_150_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_151_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*7 + 2);
v_cacheInferType_152_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_142_);
v___x_153_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_141_, v_keyedConfig_142_);
lean_inc(v_customCanUnfoldPredicate_x3f_149_);
lean_inc(v_synthPendingDepth_148_);
lean_inc(v_defEqCtx_x3f_147_);
lean_inc_ref(v_localInstances_146_);
lean_inc_ref(v_lctx_145_);
lean_inc(v_zetaDeltaSet_144_);
v___x_154_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v_zetaDeltaSet_144_);
lean_ctor_set(v___x_154_, 2, v_lctx_145_);
lean_ctor_set(v___x_154_, 3, v_localInstances_146_);
lean_ctor_set(v___x_154_, 4, v_defEqCtx_x3f_147_);
lean_ctor_set(v___x_154_, 5, v_synthPendingDepth_148_);
lean_ctor_set(v___x_154_, 6, v_customCanUnfoldPredicate_x3f_149_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*7, v_trackZetaDelta_143_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*7 + 1, v_univApprox_150_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*7 + 2, v_inTypeClassResolution_151_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*7 + 3, v_cacheInferType_152_);
v___x_155_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_134_, v___x_154_, v_a_136_, v_a_137_, v_a_138_);
lean_dec_ref_known(v___x_154_, 7);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1___boxed(lean_object* v_e_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1(v_e_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(lean_object* v_type_167_, lean_object* v_k_168_, uint8_t v_cleanupAnnotations_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___f_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___f_175_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_175_, 0, v_k_168_);
v___x_176_ = 0;
v___x_177_ = lean_box(0);
v___x_178_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_176_, v___x_177_, v_type_167_, v___f_175_, v_cleanupAnnotations_169_, v___x_176_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_a_187_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_178_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_178_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg___boxed(lean_object* v_type_195_, lean_object* v_k_196_, lean_object* v_cleanupAnnotations_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_203_; lean_object* v_res_204_; 
v_cleanupAnnotations_boxed_203_ = lean_unbox(v_cleanupAnnotations_197_);
v_res_204_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_type_195_, v_k_196_, v_cleanupAnnotations_boxed_203_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3(lean_object* v_00_u03b1_205_, lean_object* v_type_206_, lean_object* v_k_207_, uint8_t v_cleanupAnnotations_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_type_206_, v_k_207_, v_cleanupAnnotations_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___boxed(lean_object* v_00_u03b1_215_, lean_object* v_type_216_, lean_object* v_k_217_, lean_object* v_cleanupAnnotations_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_224_; lean_object* v_res_225_; 
v_cleanupAnnotations_boxed_224_ = lean_unbox(v_cleanupAnnotations_218_);
v_res_225_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3(v_00_u03b1_215_, v_type_216_, v_k_217_, v_cleanupAnnotations_boxed_224_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(lean_object* v___x_226_, lean_object* v_as_227_, size_t v_i_228_, size_t v_stop_229_, lean_object* v_b_230_){
_start:
{
lean_object* v___y_232_; uint8_t v___x_236_; 
v___x_236_ = lean_usize_dec_eq(v_i_228_, v_stop_229_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v_fst_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_237_ = lean_array_uget_borrowed(v_as_227_, v_i_228_);
v_fst_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc_ref(v___x_226_);
v___x_239_ = l_Lean_LocalContext_getFVar_x21(v___x_226_, v_fst_238_);
v___x_240_ = l_Lean_LocalDecl_type(v___x_239_);
lean_dec_ref(v___x_239_);
v___x_241_ = ((lean_object*)(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2));
v___x_242_ = l_Lean_Expr_isConstOf(v___x_240_, v___x_241_);
lean_dec_ref(v___x_240_);
if (v___x_242_ == 0)
{
v___y_232_ = v_b_230_;
goto v___jp_231_;
}
else
{
lean_object* v___x_243_; 
lean_inc(v___x_237_);
v___x_243_ = lean_array_push(v_b_230_, v___x_237_);
v___y_232_ = v___x_243_;
goto v___jp_231_;
}
}
else
{
lean_dec_ref(v___x_226_);
return v_b_230_;
}
v___jp_231_:
{
size_t v___x_233_; size_t v___x_234_; 
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_add(v_i_228_, v___x_233_);
v_i_228_ = v___x_234_;
v_b_230_ = v___y_232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2___boxed(lean_object* v___x_244_, lean_object* v_as_245_, lean_object* v_i_246_, lean_object* v_stop_247_, lean_object* v_b_248_){
_start:
{
size_t v_i_boxed_249_; size_t v_stop_boxed_250_; lean_object* v_res_251_; 
v_i_boxed_249_ = lean_unbox_usize(v_i_246_);
lean_dec(v_i_246_);
v_stop_boxed_250_ = lean_unbox_usize(v_stop_247_);
lean_dec(v_stop_247_);
v_res_251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v___x_244_, v_as_245_, v_i_boxed_249_, v_stop_boxed_250_, v_b_248_);
lean_dec_ref(v_as_245_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed(lean_object* v_x_252_, lean_object* v_e_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(v_x_252_, v_e_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec_ref(v_x_252_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(lean_object* v_a_262_, lean_object* v_params_263_, lean_object* v_x_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; lean_object* v___y_272_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_285_ = l_Array_zipIdx___redArg(v_params_263_, v___x_270_);
v___x_286_ = lean_array_get_size(v___x_285_);
v___x_287_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0));
v___x_288_ = lean_nat_dec_lt(v___x_270_, v___x_286_);
if (v___x_288_ == 0)
{
lean_dec_ref(v___x_285_);
v___y_272_ = v___x_287_;
goto v___jp_271_;
}
else
{
lean_object* v_lctx_289_; uint8_t v___x_290_; 
v_lctx_289_ = lean_ctor_get(v___y_265_, 2);
v___x_290_ = lean_nat_dec_le(v___x_286_, v___x_286_);
if (v___x_290_ == 0)
{
if (v___x_288_ == 0)
{
lean_dec_ref(v___x_285_);
v___y_272_ = v___x_287_;
goto v___jp_271_;
}
else
{
size_t v___x_291_; size_t v___x_292_; lean_object* v___x_293_; 
v___x_291_ = ((size_t)0ULL);
v___x_292_ = lean_usize_of_nat(v___x_286_);
lean_inc_ref(v_lctx_289_);
v___x_293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v_lctx_289_, v___x_285_, v___x_291_, v___x_292_, v___x_287_);
lean_dec_ref(v___x_285_);
v___y_272_ = v___x_293_;
goto v___jp_271_;
}
}
else
{
size_t v___x_294_; size_t v___x_295_; lean_object* v___x_296_; 
v___x_294_ = ((size_t)0ULL);
v___x_295_ = lean_usize_of_nat(v___x_286_);
lean_inc_ref(v_lctx_289_);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v_lctx_289_, v___x_285_, v___x_294_, v___x_295_, v___x_287_);
lean_dec_ref(v___x_285_);
v___y_272_ = v___x_296_;
goto v___jp_271_;
}
}
v___jp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_273_ = lean_array_get_size(v___y_272_);
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_nat_dec_eq(v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec_ref(v___y_272_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v_snd_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_278_ = lean_array_fget(v___y_272_, v___x_270_);
lean_dec_ref(v___y_272_);
v_snd_279_ = lean_ctor_get(v___x_278_, 1);
lean_inc(v_snd_279_);
lean_dec(v___x_278_);
v___x_280_ = l_Lean_Expr_getAppNumArgs(v_a_262_);
v___x_281_ = lean_nat_sub(v___x_280_, v_snd_279_);
lean_dec(v_snd_279_);
lean_dec(v___x_280_);
v___x_282_ = lean_nat_sub(v___x_281_, v___x_274_);
lean_dec(v___x_281_);
v___x_283_ = l_Lean_Expr_getRevArg_x21(v_a_262_, v___x_282_);
v___x_284_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v___x_283_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed(lean_object* v_a_297_, lean_object* v_params_298_, lean_object* v_x_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(v_a_297_, v_params_298_, v_x_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec_ref(v_x_299_);
lean_dec_ref(v_a_297_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f(lean_object* v_e_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___y_333_; uint8_t v___y_334_; lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_whnfCore(v_e_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___f_364_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v___f_364_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed), 7, 0);
switch(lean_obj_tag(v_a_338_))
{
case 6:
{
goto v___jp_365_;
}
case 8:
{
goto v___jp_365_;
}
default: 
{
lean_object* v___f_368_; uint8_t v___y_370_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
lean_dec_ref(v___f_364_);
lean_inc(v_a_338_);
v___f_368_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed), 8, 1);
lean_closure_set(v___f_368_, 0, v_a_338_);
v___x_394_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5));
v___x_395_ = lean_unsigned_to_nat(3u);
v___x_396_ = l_Lean_Expr_isAppOfArity(v_a_338_, v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_397_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7));
v___x_398_ = lean_unsigned_to_nat(4u);
v___x_399_ = l_Lean_Expr_isAppOfArity(v_a_338_, v___x_397_, v___x_398_);
v___y_370_ = v___x_399_;
goto v___jp_369_;
}
else
{
v___y_370_ = v___x_396_;
goto v___jp_369_;
}
v___jp_369_:
{
if (v___y_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_371_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1));
v___x_372_ = lean_unsigned_to_nat(2u);
v___x_373_ = l_Lean_Expr_isAppOfArity(v_a_338_, v___x_371_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3));
v___x_375_ = l_Lean_Expr_isAppOfArity(v_a_338_, v___x_374_, v___x_372_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = l_Lean_Expr_getAppFn(v_a_338_);
lean_dec(v_a_338_);
lean_inc(v_a_330_);
lean_inc_ref(v_a_329_);
lean_inc(v_a_328_);
lean_inc_ref(v_a_327_);
v___x_377_ = lean_infer_type(v___x_376_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_379_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
lean_dec_ref_known(v___x_377_, 1);
v___x_379_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_378_, v___f_368_, v___x_375_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
return v___x_379_;
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref(v___f_368_);
v_a_380_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_377_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_377_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec_ref(v___f_368_);
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = l_Lean_Expr_getAppNumArgs(v_a_338_);
v___x_390_ = lean_nat_sub(v___x_389_, v___x_388_);
lean_dec(v___x_389_);
v___x_391_ = lean_nat_sub(v___x_390_, v___x_388_);
lean_dec(v___x_390_);
v___x_392_ = l_Lean_Expr_getRevArg_x21(v_a_338_, v___x_391_);
lean_dec(v_a_338_);
v_e_326_ = v___x_392_;
goto _start;
}
}
else
{
lean_dec_ref(v___f_368_);
goto v___jp_339_;
}
}
else
{
lean_dec_ref(v___f_368_);
goto v___jp_339_;
}
}
}
}
v___jp_339_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_340_ = l_Lean_Expr_getAppNumArgs(v_a_338_);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_sub(v___x_340_, v___x_341_);
lean_dec(v___x_340_);
v___x_343_ = l_Lean_Expr_getRevArg_x21(v_a_338_, v___x_342_);
lean_dec(v_a_338_);
v___x_344_ = l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1(v___x_343_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_353_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_353_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_353_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_353_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v_a_345_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_349_);
v___x_351_ = v___x_347_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_363_; 
v_a_354_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_363_ == 0)
{
v___x_356_ = v___x_344_;
v_isShared_357_ = v_isSharedCheck_363_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_344_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_363_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
lean_inc(v_a_354_);
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_362_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
uint8_t v___x_360_; 
v___x_360_ = l_Lean_Exception_isInterrupt(v_a_354_);
if (v___x_360_ == 0)
{
uint8_t v___x_361_; 
v___x_361_ = l_Lean_Exception_isRuntime(v_a_354_);
v___y_333_ = v___x_359_;
v___y_334_ = v___x_361_;
goto v___jp_332_;
}
else
{
lean_dec(v_a_354_);
v___y_333_ = v___x_359_;
v___y_334_ = v___x_360_;
goto v___jp_332_;
}
}
}
}
}
v___jp_365_:
{
uint8_t v___x_366_; lean_object* v___x_367_; 
v___x_366_ = 0;
v___x_367_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_a_338_, v___f_364_, v___x_366_, v___x_366_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
return v___x_367_;
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
v_a_400_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_337_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_337_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
v___jp_332_:
{
if (v___y_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec_ref(v___y_333_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
else
{
return v___y_333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(lean_object* v_x_408_, lean_object* v_e_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v_e_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___boxed(lean_object* v_e_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v_e_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(lean_object* v_ctx_426_, lean_object* v_as_427_, size_t v_i_428_, size_t v_stop_429_, lean_object* v_b_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = lean_usize_dec_eq(v_i_428_, v_stop_429_);
if (v___x_436_ == 0)
{
size_t v___x_437_; size_t v___x_438_; lean_object* v_a_440_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_437_ = ((size_t)1ULL);
v___x_438_ = lean_usize_sub(v_i_428_, v___x_437_);
v___x_445_ = lean_array_uget_borrowed(v_as_427_, v___x_438_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___x_445_);
v___x_446_ = lean_infer_type(v___x_445_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_448_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_446_, 1);
lean_inc_ref(v_ctx_426_);
v___x_448_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_426_, v_a_447_);
lean_dec(v_a_447_);
v_a_440_ = v___x_448_;
goto v___jp_439_;
}
else
{
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_449_; 
v_a_449_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_446_, 1);
v_a_440_ = v_a_449_;
goto v___jp_439_;
}
else
{
lean_dec_ref(v_b_430_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_450_; 
v_a_450_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_446_, 1);
v_i_428_ = v___x_438_;
v_b_430_ = v_a_450_;
goto _start;
}
else
{
lean_dec_ref(v_ctx_426_);
return v___x_446_;
}
}
}
v___jp_439_:
{
lean_object* v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__1));
v___x_442_ = 0;
v___x_443_ = l_Lean_mkForall(v___x_441_, v___x_442_, v_a_440_, v_b_430_);
v_i_428_ = v___x_438_;
v_b_430_ = v___x_443_;
goto _start;
}
}
else
{
lean_object* v___x_452_; 
lean_dec_ref(v_ctx_426_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v_b_430_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___boxed(lean_object* v_ctx_453_, lean_object* v_as_454_, lean_object* v_i_455_, lean_object* v_stop_456_, lean_object* v_b_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
size_t v_i_boxed_463_; size_t v_stop_boxed_464_; lean_object* v_res_465_; 
v_i_boxed_463_ = lean_unbox_usize(v_i_455_);
lean_dec(v_i_455_);
v_stop_boxed_464_ = lean_unbox_usize(v_stop_456_);
lean_dec(v_stop_456_);
v_res_465_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_453_, v_as_454_, v_i_boxed_463_, v_stop_boxed_464_, v_b_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v_as_454_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3(lean_object* v_ctx_466_, lean_object* v_params_467_, lean_object* v_x_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_474_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_466_);
v___x_475_ = lean_box(0);
v___x_476_ = l_Lean_mkConst(v___x_474_, v___x_475_);
v___x_477_ = lean_array_get_size(v_params_467_);
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_nat_dec_lt(v___x_478_, v___x_477_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
lean_dec_ref(v_ctx_466_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_476_);
return v___x_480_;
}
else
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_usize_of_nat(v___x_477_);
v___x_482_ = ((size_t)0ULL);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_466_, v_params_467_, v___x_481_, v___x_482_, v___x_476_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3___boxed(lean_object* v_ctx_484_, lean_object* v_params_485_, lean_object* v_x_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3(v_ctx_484_, v_params_485_, v_x_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec_ref(v_x_486_);
lean_dec_ref(v_params_485_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0(lean_object* v_k_493_, uint8_t v_usedLetOnly_494_, lean_object* v_xs_495_, lean_object* v_b_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v___x_502_; 
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc_ref(v_xs_495_);
v___x_502_ = lean_apply_7(v_k_493_, v_xs_495_, v_b_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, lean_box(0));
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; uint8_t v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
v___x_504_ = 0;
v___x_505_ = 1;
v___x_506_ = l_Lean_Meta_mkLambdaFVars(v_xs_495_, v_a_503_, v___x_504_, v_usedLetOnly_494_, v___x_504_, v___x_504_, v___x_505_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec_ref(v_xs_495_);
return v___x_506_;
}
else
{
lean_dec_ref(v_xs_495_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0___boxed(lean_object* v_k_507_, lean_object* v_usedLetOnly_508_, lean_object* v_xs_509_, lean_object* v_b_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v_usedLetOnly_boxed_516_; lean_object* v_res_517_; 
v_usedLetOnly_boxed_516_ = lean_unbox(v_usedLetOnly_508_);
v_res_517_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0(v_k_507_, v_usedLetOnly_boxed_516_, v_xs_509_, v_b_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(lean_object* v_e_518_, lean_object* v_k_519_, uint8_t v_cleanupAnnotations_520_, uint8_t v_preserveNondepLet_521_, uint8_t v_usedLetOnly_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; lean_object* v___f_529_; lean_object* v___x_530_; 
v___x_528_ = lean_box(v_usedLetOnly_522_);
v___f_529_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0___boxed), 9, 2);
lean_closure_set(v___f_529_, 0, v_k_519_);
lean_closure_set(v___f_529_, 1, v___x_528_);
v___x_530_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_e_518_, v___f_529_, v_cleanupAnnotations_520_, v_preserveNondepLet_521_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___boxed(lean_object* v_e_531_, lean_object* v_k_532_, lean_object* v_cleanupAnnotations_533_, lean_object* v_preserveNondepLet_534_, lean_object* v_usedLetOnly_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_541_; uint8_t v_preserveNondepLet_boxed_542_; uint8_t v_usedLetOnly_boxed_543_; lean_object* v_res_544_; 
v_cleanupAnnotations_boxed_541_ = lean_unbox(v_cleanupAnnotations_533_);
v_preserveNondepLet_boxed_542_ = lean_unbox(v_preserveNondepLet_534_);
v_usedLetOnly_boxed_543_ = lean_unbox(v_usedLetOnly_535_);
v_res_544_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_e_531_, v_k_532_, v_cleanupAnnotations_boxed_541_, v_preserveNondepLet_boxed_542_, v_usedLetOnly_boxed_543_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_544_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_545_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
lean_ctor_set(v___x_550_, 3, v___x_549_);
lean_ctor_set(v___x_550_, 4, v___x_548_);
lean_ctor_set(v___x_550_, 5, v___x_548_);
lean_ctor_set(v___x_550_, 6, v___x_548_);
lean_ctor_set(v___x_550_, 7, v___x_548_);
lean_ctor_set(v___x_550_, 8, v___x_548_);
lean_ctor_set(v___x_550_, 9, v___x_548_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_unsigned_to_nat(32u);
v___x_552_ = lean_mk_empty_array_with_capacity(v___x_551_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_554_ = ((size_t)5ULL);
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_unsigned_to_nat(32u);
v___x_557_ = lean_mk_empty_array_with_capacity(v___x_556_);
v___x_558_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_559_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
lean_ctor_set(v___x_559_, 2, v___x_555_);
lean_ctor_set(v___x_559_, 3, v___x_555_);
lean_ctor_set_usize(v___x_559_, 4, v___x_554_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_560_ = lean_box(1);
v___x_561_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_562_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v___x_561_);
lean_ctor_set(v___x_563_, 2, v___x_560_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_566_ = l_Lean_stringToMessageData(v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_569_ = l_Lean_stringToMessageData(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_578_ = l_Lean_stringToMessageData(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_581_ = l_Lean_stringToMessageData(v___x_580_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_584_ = l_Lean_stringToMessageData(v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_585_, lean_object* v_declHint_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; lean_object* v_env_590_; uint8_t v___x_591_; 
v___x_589_ = lean_st_ref_get(v___y_587_);
v_env_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc_ref(v_env_590_);
lean_dec(v___x_589_);
v___x_591_ = l_Lean_Name_isAnonymous(v_declHint_586_);
if (v___x_591_ == 0)
{
uint8_t v_isExporting_592_; 
v_isExporting_592_ = lean_ctor_get_uint8(v_env_590_, sizeof(void*)*8);
if (v_isExporting_592_ == 0)
{
lean_object* v___x_593_; 
lean_dec_ref(v_env_590_);
lean_dec(v_declHint_586_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v_msg_585_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; uint8_t v___x_595_; 
lean_inc_ref(v_env_590_);
v___x_594_ = l_Lean_Environment_setExporting(v_env_590_, v___x_591_);
lean_inc(v_declHint_586_);
lean_inc_ref(v___x_594_);
v___x_595_ = l_Lean_Environment_contains(v___x_594_, v_declHint_586_, v_isExporting_592_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec_ref(v___x_594_);
lean_dec_ref(v_env_590_);
lean_dec(v_declHint_586_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_msg_585_);
return v___x_596_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_c_602_; lean_object* v___x_603_; 
v___x_597_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_598_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_599_ = l_Lean_Options_empty;
v___x_600_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_600_, 0, v___x_594_);
lean_ctor_set(v___x_600_, 1, v___x_597_);
lean_ctor_set(v___x_600_, 2, v___x_598_);
lean_ctor_set(v___x_600_, 3, v___x_599_);
lean_inc(v_declHint_586_);
v___x_601_ = l_Lean_MessageData_ofConstName(v_declHint_586_, v___x_591_);
v_c_602_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_602_, 0, v___x_600_);
lean_ctor_set(v_c_602_, 1, v___x_601_);
v___x_603_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_590_, v_declHint_586_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec_ref(v_env_590_);
lean_dec(v_declHint_586_);
v___x_604_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v_c_602_);
v___x_606_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_Lean_MessageData_note(v___x_607_);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v_msg_585_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
else
{
lean_object* v_val_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_646_; 
v_val_611_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_646_ == 0)
{
v___x_613_ = v___x_603_;
v_isShared_614_ = v_isSharedCheck_646_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_val_611_);
lean_dec(v___x_603_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_646_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_mod_618_; uint8_t v___x_619_; 
v___x_615_ = lean_box(0);
v___x_616_ = l_Lean_Environment_header(v_env_590_);
lean_dec_ref(v_env_590_);
v___x_617_ = l_Lean_EnvironmentHeader_moduleNames(v___x_616_);
v_mod_618_ = lean_array_get(v___x_615_, v___x_617_, v_val_611_);
lean_dec(v_val_611_);
lean_dec_ref(v___x_617_);
v___x_619_ = l_Lean_isPrivateName(v_declHint_586_);
lean_dec(v_declHint_586_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_620_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v_c_602_);
v___x_622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Lean_MessageData_ofName(v_mod_618_);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = l_Lean_MessageData_note(v___x_627_);
v___x_629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_629_, 0, v_msg_585_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 0);
lean_ctor_set(v___x_613_, 0, v___x_629_);
v___x_631_ = v___x_613_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_633_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v_c_602_);
v___x_635_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = l_Lean_MessageData_ofName(v_mod_618_);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = l_Lean_MessageData_note(v___x_640_);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v_msg_585_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 0);
lean_ctor_set(v___x_613_, 0, v___x_642_);
v___x_644_ = v___x_613_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_647_; 
lean_dec_ref(v_env_590_);
lean_dec(v_declHint_586_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v_msg_585_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_648_, lean_object* v_declHint_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_648_, v_declHint_649_, v___y_650_);
lean_dec(v___y_650_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_653_, lean_object* v_declHint_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_670_; 
v___x_660_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_653_, v_declHint_654_, v___y_658_);
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_670_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_665_ = l_Lean_unknownIdentifierMessageTag;
v___x_666_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v_a_661_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_666_);
v___x_668_ = v___x_663_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_671_, lean_object* v_declHint_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_671_, v_declHint_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(lean_object* v_msgData_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; lean_object* v_env_686_; lean_object* v___x_687_; lean_object* v_mctx_688_; lean_object* v_lctx_689_; lean_object* v_options_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_685_ = lean_st_ref_get(v___y_683_);
v_env_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc_ref(v_env_686_);
lean_dec(v___x_685_);
v___x_687_ = lean_st_ref_get(v___y_681_);
v_mctx_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc_ref(v_mctx_688_);
lean_dec(v___x_687_);
v_lctx_689_ = lean_ctor_get(v___y_680_, 2);
v_options_690_ = lean_ctor_get(v___y_682_, 2);
lean_inc_ref(v_options_690_);
lean_inc_ref(v_lctx_689_);
v___x_691_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_691_, 0, v_env_686_);
lean_ctor_set(v___x_691_, 1, v_mctx_688_);
lean_ctor_set(v___x_691_, 2, v_lctx_689_);
lean_ctor_set(v___x_691_, 3, v_options_690_);
v___x_692_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v_msgData_679_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___boxed(lean_object* v_msgData_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(v_msgData_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(lean_object* v_msg_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_ref_707_; lean_object* v___x_708_; lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_717_; 
v_ref_707_ = lean_ctor_get(v___y_704_, 5);
v___x_708_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(v_msg_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_717_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_717_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
lean_inc(v_ref_707_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_ref_707_);
lean_ctor_set(v___x_713_, 1, v_a_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 1);
lean_ctor_set(v___x_711_, 0, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg___boxed(lean_object* v_msg_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v_msg_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_725_, lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_fileName_732_; lean_object* v_fileMap_733_; lean_object* v_options_734_; lean_object* v_currRecDepth_735_; lean_object* v_maxRecDepth_736_; lean_object* v_ref_737_; lean_object* v_currNamespace_738_; lean_object* v_openDecls_739_; lean_object* v_initHeartbeats_740_; lean_object* v_maxHeartbeats_741_; lean_object* v_quotContext_742_; lean_object* v_currMacroScope_743_; uint8_t v_diag_744_; lean_object* v_cancelTk_x3f_745_; uint8_t v_suppressElabErrors_746_; lean_object* v_inheritedTraceOptions_747_; lean_object* v_ref_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_fileName_732_ = lean_ctor_get(v___y_729_, 0);
v_fileMap_733_ = lean_ctor_get(v___y_729_, 1);
v_options_734_ = lean_ctor_get(v___y_729_, 2);
v_currRecDepth_735_ = lean_ctor_get(v___y_729_, 3);
v_maxRecDepth_736_ = lean_ctor_get(v___y_729_, 4);
v_ref_737_ = lean_ctor_get(v___y_729_, 5);
v_currNamespace_738_ = lean_ctor_get(v___y_729_, 6);
v_openDecls_739_ = lean_ctor_get(v___y_729_, 7);
v_initHeartbeats_740_ = lean_ctor_get(v___y_729_, 8);
v_maxHeartbeats_741_ = lean_ctor_get(v___y_729_, 9);
v_quotContext_742_ = lean_ctor_get(v___y_729_, 10);
v_currMacroScope_743_ = lean_ctor_get(v___y_729_, 11);
v_diag_744_ = lean_ctor_get_uint8(v___y_729_, sizeof(void*)*14);
v_cancelTk_x3f_745_ = lean_ctor_get(v___y_729_, 12);
v_suppressElabErrors_746_ = lean_ctor_get_uint8(v___y_729_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_747_ = lean_ctor_get(v___y_729_, 13);
v_ref_748_ = l_Lean_replaceRef(v_ref_725_, v_ref_737_);
lean_inc_ref(v_inheritedTraceOptions_747_);
lean_inc(v_cancelTk_x3f_745_);
lean_inc(v_currMacroScope_743_);
lean_inc(v_quotContext_742_);
lean_inc(v_maxHeartbeats_741_);
lean_inc(v_initHeartbeats_740_);
lean_inc(v_openDecls_739_);
lean_inc(v_currNamespace_738_);
lean_inc(v_maxRecDepth_736_);
lean_inc(v_currRecDepth_735_);
lean_inc_ref(v_options_734_);
lean_inc_ref(v_fileMap_733_);
lean_inc_ref(v_fileName_732_);
v___x_749_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_749_, 0, v_fileName_732_);
lean_ctor_set(v___x_749_, 1, v_fileMap_733_);
lean_ctor_set(v___x_749_, 2, v_options_734_);
lean_ctor_set(v___x_749_, 3, v_currRecDepth_735_);
lean_ctor_set(v___x_749_, 4, v_maxRecDepth_736_);
lean_ctor_set(v___x_749_, 5, v_ref_748_);
lean_ctor_set(v___x_749_, 6, v_currNamespace_738_);
lean_ctor_set(v___x_749_, 7, v_openDecls_739_);
lean_ctor_set(v___x_749_, 8, v_initHeartbeats_740_);
lean_ctor_set(v___x_749_, 9, v_maxHeartbeats_741_);
lean_ctor_set(v___x_749_, 10, v_quotContext_742_);
lean_ctor_set(v___x_749_, 11, v_currMacroScope_743_);
lean_ctor_set(v___x_749_, 12, v_cancelTk_x3f_745_);
lean_ctor_set(v___x_749_, 13, v_inheritedTraceOptions_747_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*14, v_diag_744_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*14 + 1, v_suppressElabErrors_746_);
v___x_750_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v_msg_726_, v___y_727_, v___y_728_, v___x_749_, v___y_730_);
lean_dec_ref_known(v___x_749_, 14);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_751_, lean_object* v_msg_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_751_, v_msg_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v_ref_751_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_759_, lean_object* v_msg_760_, lean_object* v_declHint_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; lean_object* v_a_768_; lean_object* v___x_769_; 
v___x_767_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_760_, v_declHint_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref(v___x_767_);
v___x_769_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_759_, v_a_768_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_770_, lean_object* v_msg_771_, lean_object* v_declHint_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_770_, v_msg_771_, v_declHint_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v_ref_770_);
return v_res_778_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__0));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__2));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_785_, lean_object* v_constName_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; uint8_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_792_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_793_ = 0;
lean_inc(v_constName_786_);
v___x_794_ = l_Lean_MessageData_ofConstName(v_constName_786_, v___x_793_);
v___x_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_792_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_785_, v___x_797_, v_constName_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_799_, lean_object* v_constName_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_799_, v_constName_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v_ref_799_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(lean_object* v_constName_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_ref_813_; lean_object* v___x_814_; 
v_ref_813_ = lean_ctor_get(v___y_810_, 5);
v___x_814_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_813_, v_constName_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg___boxed(lean_object* v_constName_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(lean_object* v_constName_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; lean_object* v_env_829_; uint8_t v___x_830_; lean_object* v___x_831_; 
v___x_828_ = lean_st_ref_get(v___y_826_);
v_env_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc_ref(v_env_829_);
lean_dec(v___x_828_);
v___x_830_ = 0;
lean_inc(v_constName_822_);
v___x_831_ = l_Lean_Environment_find_x3f(v_env_829_, v_constName_822_, v___x_830_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
return v___x_832_;
}
else
{
lean_object* v_val_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_constName_822_);
v_val_833_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_831_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_val_833_);
lean_dec(v___x_831_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 0);
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_val_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3___boxed(lean_object* v_constName_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(v_constName_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(lean_object* v_b_848_, lean_object* v_arg_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = l_Lean_Expr_app___override(v_b_848_, v_arg_849_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1___boxed(lean_object* v_b_858_, lean_object* v_arg_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_858_, v_arg_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(lean_object* v_x_866_, lean_object* v_b_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v_b_867_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed(lean_object* v_x_874_, lean_object* v_b_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(v_x_874_, v_b_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v_x_874_);
return v_res_881_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_882_; lean_object* v_dummy_883_; 
v___x_882_ = lean_box(0);
v_dummy_883_ = l_Lean_Expr_sort___override(v___x_882_);
return v_dummy_883_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(lean_object* v_upperBound_885_, lean_object* v_params_886_, lean_object* v___x_887_, lean_object* v_ctx_888_, uint8_t v_builtin_889_, uint8_t v_force_890_, lean_object* v_a_891_, lean_object* v_b_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___y_899_; uint8_t v___x_921_; 
v___x_921_ = lean_nat_dec_lt(v_a_891_, v_upperBound_885_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
lean_dec(v_a_891_);
lean_dec_ref(v_ctx_888_);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v_b_892_);
return v___x_922_;
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = l_Lean_instInhabitedExpr;
v___x_924_ = lean_array_get_borrowed(v___x_923_, v_params_886_, v_a_891_);
lean_inc(v___y_896_);
lean_inc_ref(v___y_895_);
lean_inc(v___y_894_);
lean_inc_ref(v___y_893_);
lean_inc(v___x_924_);
v___x_925_ = lean_infer_type(v___x_924_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___f_927_; uint8_t v___x_928_; lean_object* v___x_929_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___f_927_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0));
v___x_928_ = 0;
v___x_929_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_926_, v___f_927_, v___x_928_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_929_, 1);
v___x_931_ = lean_array_get_borrowed(v___x_923_, v___x_887_, v_a_891_);
v___x_932_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_888_);
v___x_933_ = l_Lean_Expr_isConstOf(v_a_930_, v___x_932_);
lean_dec(v___x_932_);
lean_dec(v_a_930_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; 
lean_inc(v___x_931_);
v___x_934_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_892_, v___x_931_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
v___y_899_ = v___x_934_;
goto v___jp_898_;
}
else
{
lean_object* v___x_935_; 
lean_inc(v___x_931_);
lean_inc_ref(v_ctx_888_);
v___x_935_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_888_, v_builtin_889_, v_force_890_, v___x_931_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_937_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_892_, v_a_936_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
v___y_899_ = v___x_937_;
goto v___jp_898_;
}
else
{
lean_dec_ref(v_b_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_ctx_888_);
return v___x_935_;
}
}
}
else
{
lean_dec_ref(v_b_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_ctx_888_);
return v___x_929_;
}
}
else
{
lean_dec_ref(v_b_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_ctx_888_);
return v___x_925_;
}
}
v___jp_898_:
{
if (lean_obj_tag(v___y_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_912_; 
v_a_900_ = lean_ctor_get(v___y_899_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___y_899_);
if (v_isSharedCheck_912_ == 0)
{
v___x_902_ = v___y_899_;
v_isShared_903_ = v_isSharedCheck_912_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___y_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_912_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
if (lean_obj_tag(v_a_900_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; 
lean_dec(v_a_891_);
lean_dec_ref(v_ctx_888_);
v_a_904_ = lean_ctor_get(v_a_900_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v_a_900_, 1);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v_a_904_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_del_object(v___x_902_);
v_a_908_ = lean_ctor_get(v_a_900_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v_a_900_, 1);
v___x_909_ = lean_unsigned_to_nat(1u);
v___x_910_ = lean_nat_add(v_a_891_, v___x_909_);
lean_dec(v_a_891_);
v_a_891_ = v___x_910_;
v_b_892_ = v_a_908_;
goto _start;
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_a_891_);
lean_dec_ref(v_ctx_888_);
v_a_913_ = lean_ctor_get(v___y_899_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___y_899_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___y_899_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___y_899_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(lean_object* v_a_938_, lean_object* v_ctx_939_, uint8_t v_builtin_940_, uint8_t v_force_941_, lean_object* v___x_942_, lean_object* v_params_943_, lean_object* v_x_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_dummy_950_; lean_object* v_nargs_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___y_957_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_dummy_950_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0, &l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0);
v_nargs_951_ = l_Lean_Expr_getAppNumArgs(v_a_938_);
lean_inc(v_nargs_951_);
v___x_952_ = lean_mk_array(v_nargs_951_, v_dummy_950_);
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_sub(v_nargs_951_, v___x_953_);
lean_dec(v_nargs_951_);
v___x_955_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_938_, v___x_952_, v___x_954_);
v___x_960_ = lean_array_get_size(v_params_943_);
v___x_961_ = lean_array_get_size(v___x_955_);
v___x_962_ = lean_nat_dec_le(v___x_960_, v___x_961_);
if (v___x_962_ == 0)
{
v___y_957_ = v___x_961_;
goto v___jp_956_;
}
else
{
v___y_957_ = v___x_960_;
goto v___jp_956_;
}
v___jp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v___y_957_, v_params_943_, v___x_955_, v_ctx_939_, v_builtin_940_, v_force_941_, v___x_958_, v___x_942_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec_ref(v___x_955_);
lean_dec(v___y_957_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed(lean_object* v_a_963_, lean_object* v_ctx_964_, lean_object* v_builtin_965_, lean_object* v_force_966_, lean_object* v___x_967_, lean_object* v_params_968_, lean_object* v_x_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
uint8_t v_builtin_boxed_975_; uint8_t v_force_boxed_976_; lean_object* v_res_977_; 
v_builtin_boxed_975_ = lean_unbox(v_builtin_965_);
v_force_boxed_976_ = lean_unbox(v_force_966_);
v_res_977_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(v_a_963_, v_ctx_964_, v_builtin_boxed_975_, v_force_boxed_976_, v___x_967_, v_params_968_, v_x_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec_ref(v_x_969_);
lean_dec_ref(v_params_968_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed(lean_object* v_ctx_978_, lean_object* v_builtin_979_, lean_object* v_force_980_, lean_object* v_x_981_, lean_object* v_b_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v_builtin_boxed_988_; uint8_t v_force_boxed_989_; lean_object* v_res_990_; 
v_builtin_boxed_988_ = lean_unbox(v_builtin_979_);
v_force_boxed_989_ = lean_unbox(v_force_980_);
v_res_990_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(v_ctx_978_, v_builtin_boxed_988_, v_force_boxed_989_, v_x_981_, v_b_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec_ref(v_x_981_);
return v_res_990_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6);
v___x_1007_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
lean_ctor_set(v___x_1007_, 2, v___x_1006_);
lean_ctor_set(v___x_1007_, 3, v___x_1006_);
lean_ctor_set(v___x_1007_, 4, v___x_1006_);
lean_ctor_set(v___x_1007_, 5, v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg(lean_object* v_ctx_1031_, uint8_t v_builtin_1032_, uint8_t v_force_1033_, lean_object* v_e_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Meta_whnfCore(v_e_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v_p_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
switch(lean_obj_tag(v_a_1041_))
{
case 6:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; uint8_t v___x_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; 
lean_dec_ref_known(v___x_1040_, 1);
v___x_1057_ = lean_box(v_builtin_1032_);
v___x_1058_ = lean_box(v_force_1033_);
v___f_1059_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1059_, 0, v_ctx_1031_);
lean_closure_set(v___f_1059_, 1, v___x_1057_);
lean_closure_set(v___f_1059_, 2, v___x_1058_);
v___x_1060_ = 0;
v___x_1061_ = 1;
v___x_1062_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_a_1041_, v___f_1059_, v___x_1060_, v___x_1060_, v___x_1061_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
return v___x_1062_;
}
case 8:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___f_1065_; uint8_t v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; 
lean_dec_ref_known(v___x_1040_, 1);
v___x_1063_ = lean_box(v_builtin_1032_);
v___x_1064_ = lean_box(v_force_1033_);
v___f_1065_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1065_, 0, v_ctx_1031_);
lean_closure_set(v___f_1065_, 1, v___x_1063_);
lean_closure_set(v___f_1065_, 2, v___x_1064_);
v___x_1066_ = 0;
v___x_1067_ = 1;
v___x_1068_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_a_1041_, v___f_1065_, v___x_1066_, v___x_1066_, v___x_1067_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
return v___x_1068_;
}
case 1:
{
lean_dec_ref_known(v_a_1041_, 1);
lean_dec_ref(v_ctx_1031_);
return v___x_1040_;
}
default: 
{
lean_object* v___x_1069_; 
lean_dec_ref_known(v___x_1040_, 1);
v___x_1069_ = l_Lean_Expr_getAppFn(v_a_1041_);
if (lean_obj_tag(v___x_1069_) == 4)
{
lean_object* v_declName_1070_; lean_object* v___x_1071_; lean_object* v_env_1072_; lean_object* v_varName_1073_; lean_object* v_categoryAttr_1074_; lean_object* v_combinatorAttr_1075_; lean_object* v___x_1076_; 
v_declName_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_declName_1070_);
lean_dec_ref_known(v___x_1069_, 2);
v___x_1071_ = lean_st_ref_get(v_a_1038_);
v_env_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc_ref_n(v_env_1072_, 2);
lean_dec(v___x_1071_);
v_varName_1073_ = lean_ctor_get(v_ctx_1031_, 0);
v_categoryAttr_1074_ = lean_ctor_get(v_ctx_1031_, 1);
v_combinatorAttr_1075_ = lean_ctor_get(v_ctx_1031_, 2);
v___x_1076_ = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(v_combinatorAttr_1075_, v_env_1072_, v_declName_1070_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_inc(v_varName_1073_);
lean_inc_n(v_declName_1070_, 2);
v___x_1077_ = l_Lean_Name_append(v_declName_1070_, v_varName_1073_);
v___x_1078_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(v_declName_1070_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v___f_1080_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0));
v___x_1081_ = l_Lean_ConstantInfo_type(v_a_1079_);
v___x_1082_ = 0;
lean_inc_ref(v___x_1081_);
v___x_1083_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v___x_1081_, v___f_1080_, v___x_1082_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___f_1085_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; uint8_t v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; uint8_t v___y_1208_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
lean_inc_ref(v_ctx_1031_);
v___f_1085_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_1085_, 0, v_ctx_1031_);
v___x_1258_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20));
v___x_1259_ = l_Lean_Expr_isConstOf(v_a_1084_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = ((lean_object*)(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2));
v___x_1261_ = l_Lean_Expr_isConstOf(v_a_1084_, v___x_1260_);
lean_dec(v_a_1084_);
v___y_1208_ = v___x_1261_;
goto v___jp_1207_;
}
else
{
lean_dec(v_a_1084_);
v___y_1208_ = v___x_1259_;
goto v___jp_1207_;
}
v___jp_1086_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; lean_object* v___x_1108_; 
v___x_1093_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2));
lean_inc(v___y_1092_);
v___x_1094_ = l_Lean_mkIdent(v___y_1092_);
v___x_1095_ = l_Lean_mkIdent(v___y_1088_);
v___x_1096_ = lean_unsigned_to_nat(1u);
v___x_1097_ = lean_mk_empty_array_with_capacity(v___x_1096_);
v___x_1098_ = lean_array_push(v___x_1097_, v___x_1095_);
v___x_1099_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__4));
v___x_1100_ = lean_box(2);
v___x_1101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v___x_1099_);
lean_ctor_set(v___x_1101_, 2, v___x_1098_);
v___x_1102_ = lean_unsigned_to_nat(2u);
v___x_1103_ = lean_mk_empty_array_with_capacity(v___x_1102_);
v___x_1104_ = lean_array_push(v___x_1103_, v___x_1094_);
v___x_1105_ = lean_array_push(v___x_1104_, v___x_1101_);
v___x_1106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1100_);
lean_ctor_set(v___x_1106_, 1, v___x_1093_);
lean_ctor_set(v___x_1106_, 2, v___x_1105_);
v___x_1107_ = 0;
lean_inc(v___x_1077_);
v___x_1108_ = l_Lean_Attribute_add(v___x_1077_, v___y_1092_, v___x_1106_, v___x_1107_, v___y_1089_, v___y_1091_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_dec_ref_known(v___x_1108_, 1);
v_p_1043_ = v___x_1077_;
v___y_1044_ = v___y_1090_;
v___y_1045_ = v___y_1087_;
v___y_1046_ = v___y_1089_;
v___y_1047_ = v___y_1091_;
goto v___jp_1042_;
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v___x_1077_);
lean_dec(v_a_1041_);
lean_dec_ref(v_ctx_1031_);
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
v___jp_1117_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_inc_ref_n(v_ctx_1031_, 2);
v___x_1124_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_1031_, v___y_1119_);
lean_dec_ref(v___y_1119_);
v___x_1125_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1031_, v_builtin_1032_, v_force_1033_, v___x_1124_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1127_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
lean_inc_ref(v___x_1081_);
v___x_1127_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v___x_1081_, v___f_1085_, v___x_1082_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1206_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1206_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1206_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v_env_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1132_ = lean_st_ref_get(v___y_1123_);
v_env_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc_ref(v_env_1133_);
lean_dec(v___x_1132_);
v___x_1134_ = lean_box(0);
lean_inc_n(v___x_1077_, 2);
v___x_1135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1077_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
lean_ctor_set(v___x_1135_, 2, v_a_1128_);
v___x_1136_ = lean_box(0);
v___x_1137_ = 1;
v___x_1138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1077_);
lean_ctor_set(v___x_1138_, 1, v___x_1134_);
v___x_1139_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1139_, 0, v___x_1135_);
lean_ctor_set(v___x_1139_, 1, v_a_1126_);
lean_ctor_set(v___x_1139_, 2, v___x_1136_);
lean_ctor_set(v___x_1139_, 3, v___x_1138_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*4, v___x_1137_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 1);
lean_ctor_set(v___x_1130_, 0, v___x_1139_);
v___x_1141_ = v___x_1130_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
uint8_t v___x_1142_; lean_object* v___x_1143_; 
lean_inc(v_declName_1070_);
v___x_1142_ = l_Lean_isMarkedMeta(v_env_1133_, v_declName_1070_);
v___x_1143_ = l_Lean_addAndCompile(v___x_1141_, v___y_1118_, v___x_1142_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v___x_1144_; lean_object* v_env_1145_; lean_object* v_nextMacroScope_1146_; lean_object* v_ngen_1147_; lean_object* v_auxDeclNGen_1148_; lean_object* v_traceState_1149_; lean_object* v_messages_1150_; lean_object* v_infoState_1151_; lean_object* v_snapshotTasks_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref_known(v___x_1143_, 1);
v___x_1144_ = lean_st_ref_take(v___y_1123_);
v_env_1145_ = lean_ctor_get(v___x_1144_, 0);
v_nextMacroScope_1146_ = lean_ctor_get(v___x_1144_, 1);
v_ngen_1147_ = lean_ctor_get(v___x_1144_, 2);
v_auxDeclNGen_1148_ = lean_ctor_get(v___x_1144_, 3);
v_traceState_1149_ = lean_ctor_get(v___x_1144_, 4);
v_messages_1150_ = lean_ctor_get(v___x_1144_, 6);
v_infoState_1151_ = lean_ctor_get(v___x_1144_, 7);
v_snapshotTasks_1152_ = lean_ctor_get(v___x_1144_, 8);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v___x_1144_, 5);
lean_dec(v_unused_1196_);
v___x_1154_ = v___x_1144_;
v_isShared_1155_ = v_isSharedCheck_1195_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snapshotTasks_1152_);
lean_inc(v_infoState_1151_);
lean_inc(v_messages_1150_);
lean_inc(v_traceState_1149_);
lean_inc(v_auxDeclNGen_1148_);
lean_inc(v_ngen_1147_);
lean_inc(v_nextMacroScope_1146_);
lean_inc(v_env_1145_);
lean_dec(v___x_1144_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1195_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_inc(v___x_1077_);
lean_inc_ref(v_combinatorAttr_1075_);
v___x_1156_ = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(v_combinatorAttr_1075_, v_env_1145_, v_declName_1070_, v___x_1077_);
v___x_1157_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 5, v___x_1157_);
lean_ctor_set(v___x_1154_, 0, v___x_1156_);
v___x_1159_ = v___x_1154_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_nextMacroScope_1146_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_ngen_1147_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v_auxDeclNGen_1148_);
lean_ctor_set(v_reuseFailAlloc_1194_, 4, v_traceState_1149_);
lean_ctor_set(v_reuseFailAlloc_1194_, 5, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1194_, 6, v_messages_1150_);
lean_ctor_set(v_reuseFailAlloc_1194_, 7, v_infoState_1151_);
lean_ctor_set(v_reuseFailAlloc_1194_, 8, v_snapshotTasks_1152_);
v___x_1159_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v_mctx_1162_; lean_object* v_zetaDeltaFVarIds_1163_; lean_object* v_postponed_1164_; lean_object* v_diag_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1192_; 
v___x_1160_ = lean_st_ref_set(v___y_1123_, v___x_1159_);
v___x_1161_ = lean_st_ref_take(v___y_1121_);
v_mctx_1162_ = lean_ctor_get(v___x_1161_, 0);
v_zetaDeltaFVarIds_1163_ = lean_ctor_get(v___x_1161_, 2);
v_postponed_1164_ = lean_ctor_get(v___x_1161_, 3);
v_diag_1165_ = lean_ctor_get(v___x_1161_, 4);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v___x_1161_, 1);
lean_dec(v_unused_1193_);
v___x_1167_ = v___x_1161_;
v_isShared_1168_ = v_isSharedCheck_1192_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_diag_1165_);
lean_inc(v_postponed_1164_);
lean_inc(v_zetaDeltaFVarIds_1163_);
lean_inc(v_mctx_1162_);
lean_dec(v___x_1161_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1192_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1169_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1169_);
v___x_1171_ = v___x_1167_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_mctx_1162_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_zetaDeltaFVarIds_1163_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v_postponed_1164_);
lean_ctor_set(v_reuseFailAlloc_1191_, 4, v_diag_1165_);
v___x_1171_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = lean_st_ref_set(v___y_1121_, v___x_1171_);
v___x_1173_ = l_Lean_Expr_isConst(v___x_1081_);
lean_dec_ref(v___x_1081_);
if (v___x_1173_ == 0)
{
lean_dec(v_a_1079_);
v_p_1043_ = v___x_1077_;
v___y_1044_ = v___y_1120_;
v___y_1045_ = v___y_1121_;
v___y_1046_ = v___y_1122_;
v___y_1047_ = v___y_1123_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = l_Lean_ConstantInfo_value_x21(v_a_1079_, v___x_1082_);
lean_dec(v_a_1079_);
v___x_1175_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v___x_1174_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
if (lean_obj_tag(v_a_1176_) == 1)
{
if (v_builtin_1032_ == 0)
{
lean_object* v_defn_1177_; lean_object* v_val_1178_; lean_object* v_name_1179_; 
v_defn_1177_ = lean_ctor_get(v_categoryAttr_1074_, 0);
v_val_1178_ = lean_ctor_get(v_a_1176_, 0);
lean_inc(v_val_1178_);
lean_dec_ref_known(v_a_1176_, 1);
v_name_1179_ = lean_ctor_get(v_defn_1177_, 1);
lean_inc(v_name_1179_);
v___y_1087_ = v___y_1121_;
v___y_1088_ = v_val_1178_;
v___y_1089_ = v___y_1122_;
v___y_1090_ = v___y_1120_;
v___y_1091_ = v___y_1123_;
v___y_1092_ = v_name_1179_;
goto v___jp_1086_;
}
else
{
lean_object* v_defn_1180_; lean_object* v_val_1181_; lean_object* v_builtinName_1182_; 
v_defn_1180_ = lean_ctor_get(v_categoryAttr_1074_, 0);
v_val_1181_ = lean_ctor_get(v_a_1176_, 0);
lean_inc(v_val_1181_);
lean_dec_ref_known(v_a_1176_, 1);
v_builtinName_1182_ = lean_ctor_get(v_defn_1180_, 0);
lean_inc(v_builtinName_1182_);
v___y_1087_ = v___y_1121_;
v___y_1088_ = v_val_1181_;
v___y_1089_ = v___y_1122_;
v___y_1090_ = v___y_1120_;
v___y_1091_ = v___y_1123_;
v___y_1092_ = v_builtinName_1182_;
goto v___jp_1086_;
}
}
else
{
lean_dec(v_a_1176_);
v_p_1043_ = v___x_1077_;
v___y_1044_ = v___y_1120_;
v___y_1045_ = v___y_1121_;
v___y_1046_ = v___y_1122_;
v___y_1047_ = v___y_1123_;
goto v___jp_1042_;
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec(v___x_1077_);
lean_dec(v_a_1041_);
lean_dec_ref(v_ctx_1031_);
v_a_1183_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1175_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1175_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
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
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec_ref(v___x_1081_);
lean_dec(v_a_1079_);
lean_dec(v___x_1077_);
lean_dec(v_declName_1070_);
lean_dec(v_a_1041_);
lean_dec_ref(v_ctx_1031_);
v_a_1197_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1143_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1143_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1126_);
lean_dec_ref(v___x_1081_);
lean_dec(v_a_1079_);
lean_dec(v___x_1077_);
lean_dec(v_declName_1070_);
lean_dec(v_a_1041_);
lean_dec_ref(v_ctx_1031_);
return v___x_1127_;
}
}
else
{
lean_dec_ref(v___f_1085_);
lean_dec_ref(v___x_1081_);
lean_dec(v_a_1079_);
lean_dec(v___x_1077_);
lean_dec(v_declName_1070_);
lean_dec(v_a_1041_);
lean_dec_ref(v_ctx_1031_);
return v___x_1125_;
}
}
v___jp_1207_:
{
if (v___y_1208_ == 0)
{
lean_object* v___x_1209_; 
lean_dec_ref(v___f_1085_);
lean_dec_ref(v___x_1081_);
lean_dec(v_a_1079_);
lean_dec(v___x_1077_);
lean_dec_ref(v_env_1072_);
lean_dec(v_declName_1070_);
lean_inc(v_a_1041_);
v___x_1209_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_1041_, v___x_1082_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
if (lean_obj_tag(v_a_1210_) == 1)
{
lean_object* v_val_1211_; 
lean_dec(v_a_1041_);
v_val_1211_ = lean_ctor_get(v_a_1210_, 0);
lean_inc(v_val_1211_);
lean_dec_ref_known(v_a_1210_, 1);
v_e_1034_ = v_val_1211_;
goto _start;
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_inc(v_varName_1073_);
lean_dec(v_a_1210_);
lean_dec_ref(v_ctx_1031_);
v___x_1213_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10);
v___x_1214_ = l_Lean_MessageData_ofName(v_varName_1073_);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12);
v___x_1217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = l_Lean_MessageData_ofExpr(v_a_1041_);
v___x_1219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1221_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
return v___x_1222_;
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_a_1041_);
lean_dec_ref(v_ctx_1031_);
v_a_1223_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1209_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1209_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
lean_object* v___x_1231_; 
lean_inc(v_a_1079_);
v___x_1231_ = l_Lean_ConstantInfo_value_x3f(v_a_1079_, v___x_1082_);
if (lean_obj_tag(v___x_1231_) == 1)
{
lean_object* v_val_1232_; lean_object* v___x_1233_; 
v_val_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_val_1232_);
lean_dec_ref_known(v___x_1231_, 1);
v___x_1233_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1072_, v_declName_1070_);
lean_dec_ref(v_env_1072_);
if (lean_obj_tag(v___x_1233_) == 0)
{
v___y_1118_ = v___y_1208_;
v___y_1119_ = v_val_1232_;
v___y_1120_ = v_a_1035_;
v___y_1121_ = v_a_1036_;
v___y_1122_ = v_a_1037_;
v___y_1123_ = v_a_1038_;
goto v___jp_1117_;
}
else
{
lean_dec_ref_known(v___x_1233_, 1);
if (v_force_1033_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1234_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14);
lean_inc(v_declName_1070_);
v___x_1235_ = l_Lean_MessageData_ofName(v_declName_1070_);
v___x_1236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16);
v___x_1238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1238_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_dec_ref_known(v___x_1239_, 1);
v___y_1118_ = v___y_1208_;
v___y_1119_ = v_val_1232_;
v___y_1120_ = v_a_1035_;
v___y_1121_ = v_a_1036_;
v___y_1122_ = v_a_1037_;
v___y_1123_ = v_a_1038_;
goto v___jp_1117_;
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_val_1232_);
lean_dec_ref(v___f_1085_);
lean_dec_ref(v___x_1081_);
lean_dec(v_a_1079_);
lean_dec(v___x_1077_);
lean_dec(v_declName_1070_);
lean_dec(v_a_1041_);
lean_dec_ref(v_ctx_1031_);
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
v___y_1118_ = v___y_1208_;
v___y_1119_ = v_val_1232_;
v___y_1120_ = v_a_1035_;
v___y_1121_ = v_a_1036_;
v___y_1122_ = v_a_1037_;
v___y_1123_ = v_a_1038_;
goto v___jp_1117_;
}
}
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_inc(v_varName_1073_);
lean_dec(v___x_1231_);
lean_dec_ref(v___f_1085_);
lean_dec_ref(v___x_1081_);
lean_dec(v_a_1079_);
lean_dec(v___x_1077_);
lean_dec_ref(v_env_1072_);
lean_dec(v_declName_1070_);
lean_dec_ref(v_ctx_1031_);
v___x_1248_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10);
v___x_1249_ = l_Lean_MessageData_ofName(v_varName_1073_);
v___x_1250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18);
v___x_1252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = l_Lean_MessageData_ofExpr(v_a_1041_);
v___x_1254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1256_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
return v___x_1257_;
}
}
}
}
else
{
lean_dec_ref(v___x_1081_);
lean_dec(v_a_1079_);
lean_dec(v___x_1077_);
lean_dec_ref(v_env_1072_);
lean_dec(v_declName_1070_);
lean_dec(v_a_1041_);
lean_dec_ref(v_ctx_1031_);
return v___x_1083_;
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v___x_1077_);
lean_dec_ref(v_env_1072_);
lean_dec(v_declName_1070_);
lean_dec(v_a_1041_);
lean_dec_ref(v_ctx_1031_);
v_a_1262_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1078_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1078_);
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
lean_object* v_val_1270_; 
lean_dec_ref(v_env_1072_);
lean_dec(v_declName_1070_);
v_val_1270_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v___x_1076_, 1);
v_p_1043_ = v_val_1270_;
v___y_1044_ = v_a_1035_;
v___y_1045_ = v_a_1036_;
v___y_1046_ = v_a_1037_;
v___y_1047_ = v_a_1038_;
goto v___jp_1042_;
}
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec_ref(v___x_1069_);
lean_dec_ref(v_ctx_1031_);
v___x_1271_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22);
v___x_1272_ = l_Lean_MessageData_ofExpr(v_a_1041_);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1275_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
return v___x_1276_;
}
}
}
v___jp_1042_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = lean_box(0);
v___x_1049_ = l_Lean_mkConst(v_p_1043_, v___x_1048_);
lean_inc(v___y_1047_);
lean_inc_ref(v___y_1046_);
lean_inc(v___y_1045_);
lean_inc_ref(v___y_1044_);
lean_inc_ref(v___x_1049_);
v___x_1050_ = lean_infer_type(v___x_1049_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___f_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = lean_box(v_builtin_1032_);
v___x_1053_ = lean_box(v_force_1033_);
v___f_1054_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed), 12, 5);
lean_closure_set(v___f_1054_, 0, v_a_1041_);
lean_closure_set(v___f_1054_, 1, v_ctx_1031_);
lean_closure_set(v___f_1054_, 2, v___x_1052_);
lean_closure_set(v___f_1054_, 3, v___x_1053_);
lean_closure_set(v___f_1054_, 4, v___x_1049_);
v___x_1055_ = 0;
v___x_1056_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_1051_, v___f_1054_, v___x_1055_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
return v___x_1056_;
}
else
{
lean_dec_ref(v___x_1049_);
lean_dec(v_a_1041_);
lean_dec_ref(v_ctx_1031_);
return v___x_1050_;
}
}
}
else
{
lean_dec_ref(v_ctx_1031_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(lean_object* v_ctx_1277_, uint8_t v_builtin_1278_, uint8_t v_force_1279_, lean_object* v_x_1280_, lean_object* v_b_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1277_, v_builtin_1278_, v_force_1279_, v_b_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___boxed(lean_object* v_upperBound_1288_, lean_object* v_params_1289_, lean_object* v___x_1290_, lean_object* v_ctx_1291_, lean_object* v_builtin_1292_, lean_object* v_force_1293_, lean_object* v_a_1294_, lean_object* v_b_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
uint8_t v_builtin_boxed_1301_; uint8_t v_force_boxed_1302_; lean_object* v_res_1303_; 
v_builtin_boxed_1301_ = lean_unbox(v_builtin_1292_);
v_force_boxed_1302_ = lean_unbox(v_force_1293_);
v_res_1303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v_upperBound_1288_, v_params_1289_, v___x_1290_, v_ctx_1291_, v_builtin_boxed_1301_, v_force_boxed_1302_, v_a_1294_, v_b_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_params_1289_);
lean_dec(v_upperBound_1288_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___boxed(lean_object* v_ctx_1304_, lean_object* v_builtin_1305_, lean_object* v_force_1306_, lean_object* v_e_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
uint8_t v_builtin_boxed_1313_; uint8_t v_force_boxed_1314_; lean_object* v_res_1315_; 
v_builtin_boxed_1313_ = lean_unbox(v_builtin_1305_);
v_force_boxed_1314_ = lean_unbox(v_force_1306_);
v_res_1315_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1304_, v_builtin_boxed_1313_, v_force_boxed_1314_, v_e_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr(lean_object* v_00_u03b1_1316_, lean_object* v_ctx_1317_, uint8_t v_builtin_1318_, uint8_t v_force_1319_, lean_object* v_e_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1317_, v_builtin_1318_, v_force_1319_, v_e_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_ctx_1328_, lean_object* v_builtin_1329_, lean_object* v_force_1330_, lean_object* v_e_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
uint8_t v_builtin_boxed_1337_; uint8_t v_force_boxed_1338_; lean_object* v_res_1339_; 
v_builtin_boxed_1337_ = lean_unbox(v_builtin_1329_);
v_force_boxed_1338_ = lean_unbox(v_force_1330_);
v_res_1339_ = l_Lean_ParserCompiler_compileParserExpr(v_00_u03b1_1327_, v_ctx_1328_, v_builtin_boxed_1337_, v_force_boxed_1338_, v_e_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(lean_object* v_00_u03b1_1340_, lean_object* v_ctx_1341_, lean_object* v_as_1342_, size_t v_i_1343_, size_t v_stop_1344_, lean_object* v_b_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_1341_, v_as_1342_, v_i_1343_, v_stop_1344_, v_b_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___boxed(lean_object* v_00_u03b1_1352_, lean_object* v_ctx_1353_, lean_object* v_as_1354_, lean_object* v_i_1355_, lean_object* v_stop_1356_, lean_object* v_b_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
size_t v_i_boxed_1363_; size_t v_stop_boxed_1364_; lean_object* v_res_1365_; 
v_i_boxed_1363_ = lean_unbox_usize(v_i_1355_);
lean_dec(v_i_1355_);
v_stop_boxed_1364_ = lean_unbox_usize(v_stop_1356_);
lean_dec(v_stop_1356_);
v_res_1365_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(v_00_u03b1_1352_, v_ctx_1353_, v_as_1354_, v_i_boxed_1363_, v_stop_boxed_1364_, v_b_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec_ref(v_as_1354_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(lean_object* v_upperBound_1366_, lean_object* v_params_1367_, lean_object* v___x_1368_, lean_object* v_00_u03b1_1369_, lean_object* v_ctx_1370_, uint8_t v_builtin_1371_, uint8_t v_force_1372_, lean_object* v_inst_1373_, lean_object* v_R_1374_, lean_object* v_a_1375_, lean_object* v_b_1376_, lean_object* v_c_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v_upperBound_1366_, v_params_1367_, v___x_1368_, v_ctx_1370_, v_builtin_1371_, v_force_1372_, v_a_1375_, v_b_1376_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1384_ = _args[0];
lean_object* v_params_1385_ = _args[1];
lean_object* v___x_1386_ = _args[2];
lean_object* v_00_u03b1_1387_ = _args[3];
lean_object* v_ctx_1388_ = _args[4];
lean_object* v_builtin_1389_ = _args[5];
lean_object* v_force_1390_ = _args[6];
lean_object* v_inst_1391_ = _args[7];
lean_object* v_R_1392_ = _args[8];
lean_object* v_a_1393_ = _args[9];
lean_object* v_b_1394_ = _args[10];
lean_object* v_c_1395_ = _args[11];
lean_object* v___y_1396_ = _args[12];
lean_object* v___y_1397_ = _args[13];
lean_object* v___y_1398_ = _args[14];
lean_object* v___y_1399_ = _args[15];
lean_object* v___y_1400_ = _args[16];
_start:
{
uint8_t v_builtin_boxed_1401_; uint8_t v_force_boxed_1402_; lean_object* v_res_1403_; 
v_builtin_boxed_1401_ = lean_unbox(v_builtin_1389_);
v_force_boxed_1402_ = lean_unbox(v_force_1390_);
v_res_1403_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(v_upperBound_1384_, v_params_1385_, v___x_1386_, v_00_u03b1_1387_, v_ctx_1388_, v_builtin_boxed_1401_, v_force_boxed_1402_, v_inst_1391_, v_R_1392_, v_a_1393_, v_b_1394_, v_c_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec_ref(v___x_1386_);
lean_dec_ref(v_params_1385_);
lean_dec(v_upperBound_1384_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4(lean_object* v_00_u03b1_1404_, lean_object* v_msg_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v_msg_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___boxed(lean_object* v_00_u03b1_1412_, lean_object* v_msg_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4(v_00_u03b1_1412_, v_msg_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(lean_object* v_00_u03b1_1420_, lean_object* v_constName_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1428_, lean_object* v_constName_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(v_00_u03b1_1428_, v_constName_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_1436_, lean_object* v_ref_1437_, lean_object* v_constName_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_1437_, v_constName_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1445_, lean_object* v_ref_1446_, lean_object* v_constName_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(v_00_u03b1_1445_, v_ref_1446_, v_constName_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v_ref_1446_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_1454_, lean_object* v_ref_1455_, lean_object* v_msg_1456_, lean_object* v_declHint_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_1455_, v_msg_1456_, v_declHint_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1464_, lean_object* v_ref_1465_, lean_object* v_msg_1466_, lean_object* v_declHint_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7(v_00_u03b1_1464_, v_ref_1465_, v_msg_1466_, v_declHint_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v_ref_1465_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_1474_, lean_object* v_declHint_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1474_, v_declHint_1475_, v___y_1479_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1482_, lean_object* v_declHint_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_1482_, v_declHint_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1490_, lean_object* v_ref_1491_, lean_object* v_msg_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1491_, v_msg_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1499_, lean_object* v_ref_1500_, lean_object* v_msg_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_1499_, v_ref_1500_, v_msg_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v_ref_1500_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(lean_object* v_ctx_1508_, uint8_t v_builtin_1509_, lean_object* v_x_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_p_1517_; lean_object* v_psep_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; 
switch(lean_obj_tag(v_x_1510_))
{
case 1:
{
lean_object* v_p_1525_; 
v_p_1525_ = lean_ctor_get(v_x_1510_, 1);
lean_inc_ref(v_p_1525_);
lean_dec_ref_known(v_x_1510_, 2);
v_x_1510_ = v_p_1525_;
goto _start;
}
case 2:
{
lean_object* v_p_u2081_1527_; lean_object* v_p_u2082_1528_; lean_object* v___x_1529_; 
v_p_u2081_1527_ = lean_ctor_get(v_x_1510_, 1);
lean_inc_ref(v_p_u2081_1527_);
v_p_u2082_1528_ = lean_ctor_get(v_x_1510_, 2);
lean_inc_ref(v_p_u2082_1528_);
lean_dec_ref_known(v_x_1510_, 3);
lean_inc_ref(v_ctx_1508_);
v___x_1529_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1508_, v_builtin_1509_, v_p_u2081_1527_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_dec_ref_known(v___x_1529_, 1);
v_x_1510_ = v_p_u2082_1528_;
goto _start;
}
else
{
lean_dec_ref(v_p_u2082_1528_);
lean_dec_ref(v_ctx_1508_);
return v___x_1529_;
}
}
case 3:
{
lean_object* v_p_1531_; 
v_p_1531_ = lean_ctor_get(v_x_1510_, 2);
lean_inc_ref(v_p_1531_);
lean_dec_ref_known(v_x_1510_, 3);
v_x_1510_ = v_p_1531_;
goto _start;
}
case 4:
{
lean_object* v_p_1533_; 
v_p_1533_ = lean_ctor_get(v_x_1510_, 3);
lean_inc_ref(v_p_1533_);
lean_dec_ref_known(v_x_1510_, 4);
v_x_1510_ = v_p_1533_;
goto _start;
}
case 8:
{
lean_object* v_declName_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_declName_1535_ = lean_ctor_get(v_x_1510_, 0);
lean_inc(v_declName_1535_);
lean_dec_ref_known(v_x_1510_, 1);
v___x_1536_ = 0;
v___x_1537_ = lean_box(0);
v___x_1538_ = l_Lean_mkConst(v_declName_1535_, v___x_1537_);
v___x_1539_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1508_, v_builtin_1509_, v___x_1536_, v___x_1538_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1547_; 
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v___x_1539_, 0);
lean_dec(v_unused_1548_);
v___x_1541_ = v___x_1539_;
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
else
{
lean_dec(v___x_1539_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1543_ = lean_box(0);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1543_);
v___x_1545_ = v___x_1541_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_a_1549_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1539_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1539_);
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
case 9:
{
lean_object* v_p_1557_; 
v_p_1557_ = lean_ctor_get(v_x_1510_, 2);
lean_inc_ref(v_p_1557_);
lean_dec_ref_known(v_x_1510_, 3);
v_x_1510_ = v_p_1557_;
goto _start;
}
case 10:
{
lean_object* v_p_1559_; lean_object* v_psep_1560_; 
v_p_1559_ = lean_ctor_get(v_x_1510_, 0);
lean_inc_ref(v_p_1559_);
v_psep_1560_ = lean_ctor_get(v_x_1510_, 2);
lean_inc_ref(v_psep_1560_);
lean_dec_ref_known(v_x_1510_, 3);
v_p_1517_ = v_p_1559_;
v_psep_1518_ = v_psep_1560_;
v___y_1519_ = v_a_1511_;
v___y_1520_ = v_a_1512_;
v___y_1521_ = v_a_1513_;
v___y_1522_ = v_a_1514_;
goto v___jp_1516_;
}
case 11:
{
lean_object* v_p_1561_; lean_object* v_psep_1562_; 
v_p_1561_ = lean_ctor_get(v_x_1510_, 0);
lean_inc_ref(v_p_1561_);
v_psep_1562_ = lean_ctor_get(v_x_1510_, 2);
lean_inc_ref(v_psep_1562_);
lean_dec_ref_known(v_x_1510_, 3);
v_p_1517_ = v_p_1561_;
v_psep_1518_ = v_psep_1562_;
v___y_1519_ = v_a_1511_;
v___y_1520_ = v_a_1512_;
v___y_1521_ = v_a_1513_;
v___y_1522_ = v_a_1514_;
goto v___jp_1516_;
}
default: 
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v_x_1510_);
lean_dec_ref(v_ctx_1508_);
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
}
v___jp_1516_:
{
lean_object* v___x_1523_; 
lean_inc_ref(v_ctx_1508_);
v___x_1523_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1508_, v_builtin_1509_, v_p_1517_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_dec_ref_known(v___x_1523_, 1);
v_x_1510_ = v_psep_1518_;
v_a_1511_ = v___y_1519_;
v_a_1512_ = v___y_1520_;
v_a_1513_ = v___y_1521_;
v_a_1514_ = v___y_1522_;
goto _start;
}
else
{
lean_dec_ref(v_psep_1518_);
lean_dec_ref(v_ctx_1508_);
return v___x_1523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg___boxed(lean_object* v_ctx_1565_, lean_object* v_builtin_1566_, lean_object* v_x_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
uint8_t v_builtin_boxed_1573_; lean_object* v_res_1574_; 
v_builtin_boxed_1573_ = lean_unbox(v_builtin_1566_);
v_res_1574_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1565_, v_builtin_boxed_1573_, v_x_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers(lean_object* v_00_u03b1_1575_, lean_object* v_ctx_1576_, uint8_t v_builtin_1577_, lean_object* v_x_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1576_, v_builtin_1577_, v_x_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___boxed(lean_object* v_00_u03b1_1585_, lean_object* v_ctx_1586_, lean_object* v_builtin_1587_, lean_object* v_x_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
uint8_t v_builtin_boxed_1594_; lean_object* v_res_1595_; 
v_builtin_boxed_1594_ = lean_unbox(v_builtin_1587_);
v_res_1595_ = l_Lean_ParserCompiler_compileEmbeddedParsers(v_00_u03b1_1585_, v_ctx_1586_, v_builtin_boxed_1594_, v_x_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
return v_res_1595_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = lean_box(0);
v___x_1597_ = l_Lean_Elab_abortCommandExceptionId;
v___x_1598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v___x_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg(){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0);
v___x_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___boxed(lean_object* v___y_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(lean_object* v_msgData_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v_env_1609_; lean_object* v_options_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1608_ = lean_st_ref_get(v___y_1606_);
v_env_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc_ref(v_env_1609_);
lean_dec(v___x_1608_);
v_options_1610_ = lean_ctor_get(v___y_1605_, 2);
v___x_1611_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1612_ = lean_unsigned_to_nat(32u);
v___x_1613_ = lean_mk_empty_array_with_capacity(v___x_1612_);
lean_dec_ref(v___x_1613_);
v___x_1614_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
lean_inc_ref(v_options_1610_);
v___x_1615_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1615_, 0, v_env_1609_);
lean_ctor_set(v___x_1615_, 1, v___x_1611_);
lean_ctor_set(v___x_1615_, 2, v___x_1614_);
lean_ctor_set(v___x_1615_, 3, v_options_1610_);
v___x_1616_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
lean_ctor_set(v___x_1616_, 1, v_msgData_1604_);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9___boxed(lean_object* v_msgData_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(v_msgData_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(lean_object* v_msg_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_ref_1627_; lean_object* v___x_1628_; lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1637_; 
v_ref_1627_ = lean_ctor_get(v___y_1624_, 5);
v___x_1628_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(v_msg_1623_, v___y_1624_, v___y_1625_);
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1637_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
lean_inc(v_ref_1627_);
v___x_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1633_, 0, v_ref_1627_);
lean_ctor_set(v___x_1633_, 1, v_a_1629_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set_tag(v___x_1631_, 1);
lean_ctor_set(v___x_1631_, 0, v___x_1633_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msg_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(lean_object* v_x_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
if (lean_obj_tag(v_x_1643_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v_a_1647_ = lean_ctor_get(v_x_1643_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v_x_1643_, 1);
v___x_1648_ = l_Lean_stringToMessageData(v_a_1647_);
v___x_1649_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v___x_1648_, v___y_1644_, v___y_1645_);
return v___x_1649_;
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v_a_1650_ = lean_ctor_get(v_x_1643_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_x_1643_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v_x_1643_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v_x_1643_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 0);
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg___boxed(lean_object* v_x_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v_x_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(lean_object* v_typeName_1663_, lean_object* v_constName_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; lean_object* v_env_1669_; uint8_t v___x_1670_; 
v___x_1668_ = lean_st_ref_get(v___y_1666_);
v_env_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc_ref(v_env_1669_);
lean_dec(v___x_1668_);
lean_inc(v_constName_1664_);
v___x_1670_ = lean_has_compile_error(v_env_1669_, v_constName_1664_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v_env_1672_; lean_object* v_options_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1671_ = lean_st_ref_get(v___y_1666_);
v_env_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc_ref(v_env_1672_);
lean_dec(v___x_1671_);
v_options_1673_ = lean_ctor_get(v___y_1665_, 2);
v___x_1674_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1672_, v_options_1673_, v_typeName_1663_, v_constName_1664_);
v___x_1675_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v___x_1674_, v___y_1665_, v___y_1666_);
return v___x_1675_;
}
else
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v___x_1677_; lean_object* v_env_1678_; lean_object* v_options_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec_ref_known(v___x_1676_, 1);
v___x_1677_ = lean_st_ref_get(v___y_1666_);
v_env_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc_ref(v_env_1678_);
lean_dec(v___x_1677_);
v_options_1679_ = lean_ctor_get(v___y_1665_, 2);
v___x_1680_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1678_, v_options_1679_, v_typeName_1663_, v_constName_1664_);
v___x_1681_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v___x_1680_, v___y_1665_, v___y_1666_);
return v___x_1681_;
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v_constName_1664_);
lean_dec(v_typeName_1663_);
v_a_1682_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1676_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1676_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg___boxed(lean_object* v_typeName_1690_, lean_object* v_constName_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v_typeName_1690_, v_constName_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(lean_object* v_ref_1696_, lean_object* v_msg_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_fileName_1701_; lean_object* v_fileMap_1702_; lean_object* v_options_1703_; lean_object* v_currRecDepth_1704_; lean_object* v_maxRecDepth_1705_; lean_object* v_ref_1706_; lean_object* v_currNamespace_1707_; lean_object* v_openDecls_1708_; lean_object* v_initHeartbeats_1709_; lean_object* v_maxHeartbeats_1710_; lean_object* v_quotContext_1711_; lean_object* v_currMacroScope_1712_; uint8_t v_diag_1713_; lean_object* v_cancelTk_x3f_1714_; uint8_t v_suppressElabErrors_1715_; lean_object* v_inheritedTraceOptions_1716_; lean_object* v_ref_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_fileName_1701_ = lean_ctor_get(v___y_1698_, 0);
v_fileMap_1702_ = lean_ctor_get(v___y_1698_, 1);
v_options_1703_ = lean_ctor_get(v___y_1698_, 2);
v_currRecDepth_1704_ = lean_ctor_get(v___y_1698_, 3);
v_maxRecDepth_1705_ = lean_ctor_get(v___y_1698_, 4);
v_ref_1706_ = lean_ctor_get(v___y_1698_, 5);
v_currNamespace_1707_ = lean_ctor_get(v___y_1698_, 6);
v_openDecls_1708_ = lean_ctor_get(v___y_1698_, 7);
v_initHeartbeats_1709_ = lean_ctor_get(v___y_1698_, 8);
v_maxHeartbeats_1710_ = lean_ctor_get(v___y_1698_, 9);
v_quotContext_1711_ = lean_ctor_get(v___y_1698_, 10);
v_currMacroScope_1712_ = lean_ctor_get(v___y_1698_, 11);
v_diag_1713_ = lean_ctor_get_uint8(v___y_1698_, sizeof(void*)*14);
v_cancelTk_x3f_1714_ = lean_ctor_get(v___y_1698_, 12);
v_suppressElabErrors_1715_ = lean_ctor_get_uint8(v___y_1698_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1716_ = lean_ctor_get(v___y_1698_, 13);
v_ref_1717_ = l_Lean_replaceRef(v_ref_1696_, v_ref_1706_);
lean_inc_ref(v_inheritedTraceOptions_1716_);
lean_inc(v_cancelTk_x3f_1714_);
lean_inc(v_currMacroScope_1712_);
lean_inc(v_quotContext_1711_);
lean_inc(v_maxHeartbeats_1710_);
lean_inc(v_initHeartbeats_1709_);
lean_inc(v_openDecls_1708_);
lean_inc(v_currNamespace_1707_);
lean_inc(v_maxRecDepth_1705_);
lean_inc(v_currRecDepth_1704_);
lean_inc_ref(v_options_1703_);
lean_inc_ref(v_fileMap_1702_);
lean_inc_ref(v_fileName_1701_);
v___x_1718_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1718_, 0, v_fileName_1701_);
lean_ctor_set(v___x_1718_, 1, v_fileMap_1702_);
lean_ctor_set(v___x_1718_, 2, v_options_1703_);
lean_ctor_set(v___x_1718_, 3, v_currRecDepth_1704_);
lean_ctor_set(v___x_1718_, 4, v_maxRecDepth_1705_);
lean_ctor_set(v___x_1718_, 5, v_ref_1717_);
lean_ctor_set(v___x_1718_, 6, v_currNamespace_1707_);
lean_ctor_set(v___x_1718_, 7, v_openDecls_1708_);
lean_ctor_set(v___x_1718_, 8, v_initHeartbeats_1709_);
lean_ctor_set(v___x_1718_, 9, v_maxHeartbeats_1710_);
lean_ctor_set(v___x_1718_, 10, v_quotContext_1711_);
lean_ctor_set(v___x_1718_, 11, v_currMacroScope_1712_);
lean_ctor_set(v___x_1718_, 12, v_cancelTk_x3f_1714_);
lean_ctor_set(v___x_1718_, 13, v_inheritedTraceOptions_1716_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*14, v_diag_1713_);
lean_ctor_set_uint8(v___x_1718_, sizeof(void*)*14 + 1, v_suppressElabErrors_1715_);
v___x_1719_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_1697_, v___x_1718_, v___y_1699_);
lean_dec_ref_known(v___x_1718_, 14);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg___boxed(lean_object* v_ref_1720_, lean_object* v_msg_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_1720_, v_msg_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v_ref_1720_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(lean_object* v_msg_1726_, lean_object* v_declHint_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; lean_object* v_env_1731_; uint8_t v___x_1732_; 
v___x_1730_ = lean_st_ref_get(v___y_1728_);
v_env_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc_ref(v_env_1731_);
lean_dec(v___x_1730_);
v___x_1732_ = l_Lean_Name_isAnonymous(v_declHint_1727_);
if (v___x_1732_ == 0)
{
uint8_t v_isExporting_1733_; 
v_isExporting_1733_ = lean_ctor_get_uint8(v_env_1731_, sizeof(void*)*8);
if (v_isExporting_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_dec_ref(v_env_1731_);
lean_dec(v_declHint_1727_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_msg_1726_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; uint8_t v___x_1736_; 
lean_inc_ref(v_env_1731_);
v___x_1735_ = l_Lean_Environment_setExporting(v_env_1731_, v___x_1732_);
lean_inc(v_declHint_1727_);
lean_inc_ref(v___x_1735_);
v___x_1736_ = l_Lean_Environment_contains(v___x_1735_, v_declHint_1727_, v_isExporting_1733_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; 
lean_dec_ref(v___x_1735_);
lean_dec_ref(v_env_1731_);
lean_dec(v_declHint_1727_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v_msg_1726_);
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v_c_1745_; lean_object* v___x_1746_; 
v___x_1738_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1739_ = lean_unsigned_to_nat(32u);
v___x_1740_ = lean_mk_empty_array_with_capacity(v___x_1739_);
lean_dec_ref(v___x_1740_);
v___x_1741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1742_ = l_Lean_Options_empty;
v___x_1743_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1735_);
lean_ctor_set(v___x_1743_, 1, v___x_1738_);
lean_ctor_set(v___x_1743_, 2, v___x_1741_);
lean_ctor_set(v___x_1743_, 3, v___x_1742_);
lean_inc(v_declHint_1727_);
v___x_1744_ = l_Lean_MessageData_ofConstName(v_declHint_1727_, v___x_1732_);
v_c_1745_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1745_, 0, v___x_1743_);
lean_ctor_set(v_c_1745_, 1, v___x_1744_);
v___x_1746_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1731_, v_declHint_1727_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec_ref(v_env_1731_);
lean_dec(v_declHint_1727_);
v___x_1747_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v_c_1745_);
v___x_1749_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1748_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = l_Lean_MessageData_note(v___x_1750_);
v___x_1752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1752_, 0, v_msg_1726_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
else
{
lean_object* v_val_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1789_; 
v_val_1754_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1756_ = v___x_1746_;
v_isShared_1757_ = v_isSharedCheck_1789_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_val_1754_);
lean_dec(v___x_1746_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1789_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_mod_1761_; uint8_t v___x_1762_; 
v___x_1758_ = lean_box(0);
v___x_1759_ = l_Lean_Environment_header(v_env_1731_);
lean_dec_ref(v_env_1731_);
v___x_1760_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1759_);
v_mod_1761_ = lean_array_get(v___x_1758_, v___x_1760_, v_val_1754_);
lean_dec(v_val_1754_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = l_Lean_isPrivateName(v_declHint_1727_);
lean_dec(v_declHint_1727_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1763_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
lean_ctor_set(v___x_1764_, 1, v_c_1745_);
v___x_1765_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1764_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = l_Lean_MessageData_ofName(v_mod_1761_);
v___x_1768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1766_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = l_Lean_MessageData_note(v___x_1770_);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_msg_1726_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1772_);
v___x_1774_ = v___x_1756_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
lean_ctor_set(v___x_1777_, 1, v_c_1745_);
v___x_1778_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = l_Lean_MessageData_ofName(v_mod_1761_);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_MessageData_note(v___x_1783_);
v___x_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1785_, 0, v_msg_1726_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1785_);
v___x_1787_ = v___x_1756_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1790_; 
lean_dec_ref(v_env_1731_);
lean_dec(v_declHint_1727_);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_msg_1726_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg___boxed(lean_object* v_msg_1791_, lean_object* v_declHint_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_1791_, v_declHint_1792_, v___y_1793_);
lean_dec(v___y_1793_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(lean_object* v_msg_1796_, lean_object* v_declHint_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1811_; 
v___x_1801_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_1796_, v_declHint_1797_, v___y_1799_);
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1811_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1811_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1806_ = l_Lean_unknownIdentifierMessageTag;
v___x_1807_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v_a_1802_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1807_);
v___x_1809_ = v___x_1804_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8___boxed(lean_object* v_msg_1812_, lean_object* v_declHint_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_1812_, v_declHint_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_ref_1818_, lean_object* v_msg_1819_, lean_object* v_declHint_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; lean_object* v_a_1825_; lean_object* v___x_1826_; 
v___x_1824_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_1819_, v_declHint_1820_, v___y_1821_, v___y_1822_);
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref(v___x_1824_);
v___x_1826_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_1818_, v_a_1825_, v___y_1821_, v___y_1822_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_ref_1827_, lean_object* v_msg_1828_, lean_object* v_declHint_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1827_, v_msg_1828_, v_declHint_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v_ref_1827_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1834_, lean_object* v_constName_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1839_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_1840_ = 0;
lean_inc(v_constName_1835_);
v___x_1841_ = l_Lean_MessageData_ofConstName(v_constName_1835_, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1839_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1834_, v___x_1844_, v_constName_1835_, v___y_1836_, v___y_1837_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1846_, lean_object* v_constName_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_1846_, v_constName_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v_ref_1846_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(lean_object* v_constName_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_ref_1856_; lean_object* v___x_1857_; 
v_ref_1856_ = lean_ctor_get(v___y_1853_, 5);
v___x_1857_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_1856_, v_constName_1852_, v___y_1853_, v___y_1854_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(lean_object* v_constName_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; lean_object* v_env_1868_; uint8_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1867_ = lean_st_ref_get(v___y_1865_);
v_env_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc_ref(v_env_1868_);
lean_dec(v___x_1867_);
v___x_1869_ = 0;
lean_inc(v_constName_1863_);
v___x_1870_ = l_Lean_Environment_find_x3f(v_env_1868_, v_constName_1863_, v___x_1869_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_1863_, v___y_1864_, v___y_1865_);
return v___x_1871_;
}
else
{
lean_object* v_val_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec(v_constName_1863_);
v_val_1872_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1870_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_val_1872_);
lean_dec(v___x_1870_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 0);
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_val_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0___boxed(lean_object* v_constName_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(v_constName_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1884_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1885_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1888_ = lean_box(1);
v___x_1889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1890_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set(v___x_1891_, 1, v___x_1889_);
lean_ctor_set(v___x_1891_, 2, v___x_1888_);
return v___x_1891_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
lean_ctor_set(v___x_1896_, 2, v___x_1895_);
lean_ctor_set(v___x_1896_, 3, v___x_1895_);
lean_ctor_set(v___x_1896_, 4, v___x_1894_);
lean_ctor_set(v___x_1896_, 5, v___x_1894_);
lean_ctor_set(v___x_1896_, 6, v___x_1894_);
lean_ctor_set(v___x_1896_, 7, v___x_1894_);
lean_ctor_set(v___x_1896_, 8, v___x_1894_);
lean_ctor_set(v___x_1896_, 9, v___x_1894_);
return v___x_1896_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1898_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
lean_ctor_set(v___x_1898_, 2, v___x_1897_);
lean_ctor_set(v___x_1898_, 3, v___x_1897_);
lean_ctor_set(v___x_1898_, 4, v___x_1897_);
lean_ctor_set(v___x_1898_, 5, v___x_1897_);
return v___x_1898_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
lean_ctor_set(v___x_1900_, 2, v___x_1899_);
lean_ctor_set(v___x_1900_, 3, v___x_1899_);
lean_ctor_set(v___x_1900_, 4, v___x_1899_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1901_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6);
v___x_1902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1903_ = lean_box(1);
v___x_1904_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5);
v___x_1905_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4);
v___x_1906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___x_1904_);
lean_ctor_set(v___x_1906_, 2, v___x_1903_);
lean_ctor_set(v___x_1906_, 3, v___x_1902_);
lean_ctor_set(v___x_1906_, 4, v___x_1901_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(lean_object* v_constName_1915_, lean_object* v_ctx_1916_, uint8_t v_builtin_1917_, lean_object* v_catName_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
uint8_t v___y_1923_; uint8_t v___y_1924_; lean_object* v___y_1925_; lean_object* v___x_1960_; 
lean_inc(v_constName_1915_);
v___x_1960_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(v_constName_1915_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1962_; lean_object* v___y_1964_; uint8_t v___y_1965_; uint8_t v___y_1966_; uint8_t v___y_1967_; lean_object* v___x_1970_; uint8_t v___y_1972_; uint8_t v___x_2022_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v___x_1962_ = l_Lean_ConstantInfo_type(v_a_1961_);
lean_dec(v_a_1961_);
v___x_1970_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11));
v___x_2022_ = l_Lean_Expr_isConstOf(v___x_1962_, v___x_1970_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9));
v___x_2024_ = l_Lean_Expr_isConstOf(v___x_1962_, v___x_2023_);
lean_dec_ref(v___x_1962_);
v___y_1972_ = v___x_2024_;
goto v___jp_1971_;
}
else
{
lean_dec_ref(v___x_1962_);
v___y_1972_ = v___x_2022_;
goto v___jp_1971_;
}
v___jp_1963_:
{
if (v___y_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_dec_ref(v___y_1964_);
v___x_1968_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9));
v___x_1969_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v___x_1968_, v_constName_1915_, v___y_1919_, v___y_1920_);
v___y_1923_ = v___y_1965_;
v___y_1924_ = v___y_1966_;
v___y_1925_ = v___x_1969_;
goto v___jp_1922_;
}
else
{
lean_dec(v_constName_1915_);
v___y_1923_ = v___y_1965_;
v___y_1924_ = v___y_1966_;
v___y_1925_ = v___y_1964_;
goto v___jp_1922_;
}
}
v___jp_1971_:
{
uint8_t v___x_1973_; 
v___x_1973_ = 1;
if (v___y_1972_ == 0)
{
uint8_t v___x_1974_; uint8_t v___x_1975_; uint8_t v___x_1976_; lean_object* v___x_1977_; uint64_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1974_ = 1;
v___x_1975_ = 0;
v___x_1976_ = 2;
v___x_1977_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1977_, 0, v___y_1972_);
lean_ctor_set_uint8(v___x_1977_, 1, v___y_1972_);
lean_ctor_set_uint8(v___x_1977_, 2, v___y_1972_);
lean_ctor_set_uint8(v___x_1977_, 3, v___y_1972_);
lean_ctor_set_uint8(v___x_1977_, 4, v___y_1972_);
lean_ctor_set_uint8(v___x_1977_, 5, v___x_1973_);
lean_ctor_set_uint8(v___x_1977_, 6, v___x_1973_);
lean_ctor_set_uint8(v___x_1977_, 7, v___y_1972_);
lean_ctor_set_uint8(v___x_1977_, 8, v___x_1973_);
lean_ctor_set_uint8(v___x_1977_, 9, v___x_1974_);
lean_ctor_set_uint8(v___x_1977_, 10, v___x_1975_);
lean_ctor_set_uint8(v___x_1977_, 11, v___x_1973_);
lean_ctor_set_uint8(v___x_1977_, 12, v___x_1973_);
lean_ctor_set_uint8(v___x_1977_, 13, v___x_1973_);
lean_ctor_set_uint8(v___x_1977_, 14, v___x_1976_);
lean_ctor_set_uint8(v___x_1977_, 15, v___x_1973_);
lean_ctor_set_uint8(v___x_1977_, 16, v___x_1973_);
lean_ctor_set_uint8(v___x_1977_, 17, v___x_1973_);
lean_ctor_set_uint8(v___x_1977_, 18, v___x_1973_);
lean_ctor_set_uint8(v___x_1977_, 19, v___y_1972_);
v___x_1978_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1977_);
v___x_1979_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set_uint64(v___x_1979_, sizeof(void*)*1, v___x_1978_);
v___x_1980_ = lean_box(1);
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2);
v___x_1983_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3));
v___x_1984_ = lean_box(0);
v___x_1985_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1985_, 0, v___x_1979_);
lean_ctor_set(v___x_1985_, 1, v___x_1980_);
lean_ctor_set(v___x_1985_, 2, v___x_1982_);
lean_ctor_set(v___x_1985_, 3, v___x_1983_);
lean_ctor_set(v___x_1985_, 4, v___x_1984_);
lean_ctor_set(v___x_1985_, 5, v___x_1981_);
lean_ctor_set(v___x_1985_, 6, v___x_1984_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*7, v___y_1972_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*7 + 1, v___y_1972_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*7 + 2, v___y_1972_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*7 + 3, v___x_1973_);
v___x_1986_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7);
v___x_1987_ = lean_st_mk_ref(v___x_1986_);
v___x_1988_ = l_Lean_Name_isAnonymous(v_catName_1918_);
v___x_1989_ = lean_box(0);
v___x_1990_ = l_Lean_mkConst(v_constName_1915_, v___x_1989_);
v___x_1991_ = lean_box(0);
v___x_1992_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1916_, v_builtin_1917_, v___x_1988_, v___x_1990_, v___x_1985_, v___x_1987_, v___y_1919_, v___y_1920_);
lean_dec_ref_known(v___x_1985_, 7);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2000_; 
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v___x_1992_, 0);
lean_dec(v_unused_2001_);
v___x_1994_ = v___x_1992_;
v_isShared_1995_ = v_isSharedCheck_2000_;
goto v_resetjp_1993_;
}
else
{
lean_dec(v___x_1992_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2000_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1996_ = lean_st_ref_get(v___x_1987_);
lean_dec(v___x_1987_);
lean_dec(v___x_1996_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_1991_);
v___x_1998_ = v___x_1994_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1991_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
else
{
lean_dec(v___x_1987_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v___x_1992_, 0);
lean_dec(v_unused_2009_);
v___x_2003_ = v___x_1992_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v___x_1992_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set_tag(v___x_2003_, 0);
lean_ctor_set(v___x_2003_, 0, v___x_1991_);
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_1991_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
v_a_2010_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1992_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_1992_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
else
{
lean_object* v___x_2018_; 
lean_inc(v_constName_1915_);
v___x_2018_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v___x_1970_, v_constName_1915_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_dec(v_constName_1915_);
v___y_1923_ = v___x_1973_;
v___y_1924_ = v___y_1972_;
v___y_1925_ = v___x_2018_;
goto v___jp_1922_;
}
else
{
lean_object* v_a_2019_; uint8_t v___x_2020_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
v___x_2020_ = l_Lean_Exception_isInterrupt(v_a_2019_);
if (v___x_2020_ == 0)
{
uint8_t v___x_2021_; 
v___x_2021_ = l_Lean_Exception_isRuntime(v_a_2019_);
v___y_1964_ = v___x_2018_;
v___y_1965_ = v___x_1973_;
v___y_1966_ = v___y_1972_;
v___y_1967_ = v___x_2021_;
goto v___jp_1963_;
}
else
{
lean_dec(v_a_2019_);
v___y_1964_ = v___x_2018_;
v___y_1965_ = v___x_1973_;
v___y_1966_ = v___y_1972_;
v___y_1967_ = v___x_2020_;
goto v___jp_1963_;
}
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec_ref(v_ctx_1916_);
lean_dec(v_constName_1915_);
v_a_2025_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1960_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1960_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
v___jp_1922_:
{
if (lean_obj_tag(v___y_1925_) == 0)
{
lean_object* v_a_1926_; uint8_t v___x_1927_; uint8_t v___x_1928_; uint8_t v___x_1929_; uint8_t v___x_1930_; lean_object* v___x_1931_; uint64_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_a_1926_ = lean_ctor_get(v___y_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___y_1925_, 1);
v___x_1927_ = 0;
v___x_1928_ = 1;
v___x_1929_ = 0;
v___x_1930_ = 2;
v___x_1931_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1931_, 0, v___x_1927_);
lean_ctor_set_uint8(v___x_1931_, 1, v___x_1927_);
lean_ctor_set_uint8(v___x_1931_, 2, v___x_1927_);
lean_ctor_set_uint8(v___x_1931_, 3, v___x_1927_);
lean_ctor_set_uint8(v___x_1931_, 4, v___x_1927_);
lean_ctor_set_uint8(v___x_1931_, 5, v___y_1924_);
lean_ctor_set_uint8(v___x_1931_, 6, v___y_1924_);
lean_ctor_set_uint8(v___x_1931_, 7, v___x_1927_);
lean_ctor_set_uint8(v___x_1931_, 8, v___y_1924_);
lean_ctor_set_uint8(v___x_1931_, 9, v___x_1928_);
lean_ctor_set_uint8(v___x_1931_, 10, v___x_1929_);
lean_ctor_set_uint8(v___x_1931_, 11, v___y_1924_);
lean_ctor_set_uint8(v___x_1931_, 12, v___y_1924_);
lean_ctor_set_uint8(v___x_1931_, 13, v___y_1924_);
lean_ctor_set_uint8(v___x_1931_, 14, v___x_1930_);
lean_ctor_set_uint8(v___x_1931_, 15, v___y_1924_);
lean_ctor_set_uint8(v___x_1931_, 16, v___y_1924_);
lean_ctor_set_uint8(v___x_1931_, 17, v___y_1924_);
lean_ctor_set_uint8(v___x_1931_, 18, v___y_1924_);
lean_ctor_set_uint8(v___x_1931_, 19, v___x_1927_);
v___x_1932_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1931_);
v___x_1933_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set_uint64(v___x_1933_, sizeof(void*)*1, v___x_1932_);
v___x_1934_ = lean_box(1);
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2);
v___x_1937_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3));
v___x_1938_ = lean_box(0);
v___x_1939_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1939_, 0, v___x_1933_);
lean_ctor_set(v___x_1939_, 1, v___x_1934_);
lean_ctor_set(v___x_1939_, 2, v___x_1936_);
lean_ctor_set(v___x_1939_, 3, v___x_1937_);
lean_ctor_set(v___x_1939_, 4, v___x_1938_);
lean_ctor_set(v___x_1939_, 5, v___x_1935_);
lean_ctor_set(v___x_1939_, 6, v___x_1938_);
lean_ctor_set_uint8(v___x_1939_, sizeof(void*)*7, v___x_1927_);
lean_ctor_set_uint8(v___x_1939_, sizeof(void*)*7 + 1, v___x_1927_);
lean_ctor_set_uint8(v___x_1939_, sizeof(void*)*7 + 2, v___x_1927_);
lean_ctor_set_uint8(v___x_1939_, sizeof(void*)*7 + 3, v___y_1923_);
v___x_1940_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7);
v___x_1941_ = lean_st_mk_ref(v___x_1940_);
v___x_1942_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1916_, v_builtin_1917_, v_a_1926_, v___x_1939_, v___x_1941_, v___y_1919_, v___y_1920_);
lean_dec_ref_known(v___x_1939_, 7);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1951_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1951_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1951_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1947_ = lean_st_ref_get(v___x_1941_);
lean_dec(v___x_1941_);
lean_dec(v___x_1947_);
if (v_isShared_1946_ == 0)
{
v___x_1949_ = v___x_1945_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1943_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
else
{
lean_dec(v___x_1941_);
return v___x_1942_;
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v_ctx_1916_);
v_a_1952_ = lean_ctor_get(v___y_1925_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___y_1925_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___y_1925_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___y_1925_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed(lean_object* v_constName_2033_, lean_object* v_ctx_2034_, lean_object* v_builtin_2035_, lean_object* v_catName_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
uint8_t v_builtin_boxed_2040_; lean_object* v_res_2041_; 
v_builtin_boxed_2040_ = lean_unbox(v_builtin_2035_);
v_res_2041_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(v_constName_2033_, v_ctx_2034_, v_builtin_boxed_2040_, v_catName_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v_catName_2036_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(lean_object* v___y_2042_, uint8_t v_isExporting_2043_, lean_object* v___x_2044_, lean_object* v_a_x3f_2045_){
_start:
{
lean_object* v___x_2047_; lean_object* v_env_2048_; lean_object* v_nextMacroScope_2049_; lean_object* v_ngen_2050_; lean_object* v_auxDeclNGen_2051_; lean_object* v_traceState_2052_; lean_object* v_messages_2053_; lean_object* v_infoState_2054_; lean_object* v_snapshotTasks_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2066_; 
v___x_2047_ = lean_st_ref_take(v___y_2042_);
v_env_2048_ = lean_ctor_get(v___x_2047_, 0);
v_nextMacroScope_2049_ = lean_ctor_get(v___x_2047_, 1);
v_ngen_2050_ = lean_ctor_get(v___x_2047_, 2);
v_auxDeclNGen_2051_ = lean_ctor_get(v___x_2047_, 3);
v_traceState_2052_ = lean_ctor_get(v___x_2047_, 4);
v_messages_2053_ = lean_ctor_get(v___x_2047_, 6);
v_infoState_2054_ = lean_ctor_get(v___x_2047_, 7);
v_snapshotTasks_2055_ = lean_ctor_get(v___x_2047_, 8);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2066_ == 0)
{
lean_object* v_unused_2067_; 
v_unused_2067_ = lean_ctor_get(v___x_2047_, 5);
lean_dec(v_unused_2067_);
v___x_2057_ = v___x_2047_;
v_isShared_2058_ = v_isSharedCheck_2066_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_snapshotTasks_2055_);
lean_inc(v_infoState_2054_);
lean_inc(v_messages_2053_);
lean_inc(v_traceState_2052_);
lean_inc(v_auxDeclNGen_2051_);
lean_inc(v_ngen_2050_);
lean_inc(v_nextMacroScope_2049_);
lean_inc(v_env_2048_);
lean_dec(v___x_2047_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2066_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = l_Lean_Environment_setExporting(v_env_2048_, v_isExporting_2043_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 5, v___x_2044_);
lean_ctor_set(v___x_2057_, 0, v___x_2059_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2059_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_nextMacroScope_2049_);
lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_ngen_2050_);
lean_ctor_set(v_reuseFailAlloc_2065_, 3, v_auxDeclNGen_2051_);
lean_ctor_set(v_reuseFailAlloc_2065_, 4, v_traceState_2052_);
lean_ctor_set(v_reuseFailAlloc_2065_, 5, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2065_, 6, v_messages_2053_);
lean_ctor_set(v_reuseFailAlloc_2065_, 7, v_infoState_2054_);
lean_ctor_set(v_reuseFailAlloc_2065_, 8, v_snapshotTasks_2055_);
v___x_2061_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = lean_st_ref_set(v___y_2042_, v___x_2061_);
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
return v___x_2064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v___y_2068_, lean_object* v_isExporting_2069_, lean_object* v___x_2070_, lean_object* v_a_x3f_2071_, lean_object* v___y_2072_){
_start:
{
uint8_t v_isExporting_boxed_2073_; lean_object* v_res_2074_; 
v_isExporting_boxed_2073_ = lean_unbox(v_isExporting_2069_);
v_res_2074_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2068_, v_isExporting_boxed_2073_, v___x_2070_, v_a_x3f_2071_);
lean_dec(v_a_x3f_2071_);
lean_dec(v___y_2068_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(lean_object* v_x_2075_, uint8_t v_isExporting_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; lean_object* v_env_2081_; uint8_t v_isExporting_2082_; lean_object* v___x_2133_; uint8_t v_isModule_2134_; 
v___x_2080_ = lean_st_ref_get(v___y_2078_);
v_env_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc_ref(v_env_2081_);
lean_dec(v___x_2080_);
v_isExporting_2082_ = lean_ctor_get_uint8(v_env_2081_, sizeof(void*)*8);
v___x_2133_ = l_Lean_Environment_header(v_env_2081_);
lean_dec_ref(v_env_2081_);
v_isModule_2134_ = lean_ctor_get_uint8(v___x_2133_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2133_);
if (v_isModule_2134_ == 0)
{
lean_object* v___x_2135_; 
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
v___x_2135_ = lean_apply_3(v_x_2075_, v___y_2077_, v___y_2078_, lean_box(0));
return v___x_2135_;
}
else
{
if (v_isExporting_2082_ == 0)
{
if (v_isExporting_2076_ == 0)
{
lean_object* v___x_2136_; 
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
v___x_2136_ = lean_apply_3(v_x_2075_, v___y_2077_, v___y_2078_, lean_box(0));
return v___x_2136_;
}
else
{
goto v___jp_2083_;
}
}
else
{
if (v_isExporting_2076_ == 0)
{
goto v___jp_2083_;
}
else
{
lean_object* v___x_2137_; 
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
v___x_2137_ = lean_apply_3(v_x_2075_, v___y_2077_, v___y_2078_, lean_box(0));
return v___x_2137_;
}
}
}
v___jp_2083_:
{
lean_object* v___x_2084_; lean_object* v_env_2085_; lean_object* v_nextMacroScope_2086_; lean_object* v_ngen_2087_; lean_object* v_auxDeclNGen_2088_; lean_object* v_traceState_2089_; lean_object* v_messages_2090_; lean_object* v_infoState_2091_; lean_object* v_snapshotTasks_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2131_; 
v___x_2084_ = lean_st_ref_take(v___y_2078_);
v_env_2085_ = lean_ctor_get(v___x_2084_, 0);
v_nextMacroScope_2086_ = lean_ctor_get(v___x_2084_, 1);
v_ngen_2087_ = lean_ctor_get(v___x_2084_, 2);
v_auxDeclNGen_2088_ = lean_ctor_get(v___x_2084_, 3);
v_traceState_2089_ = lean_ctor_get(v___x_2084_, 4);
v_messages_2090_ = lean_ctor_get(v___x_2084_, 6);
v_infoState_2091_ = lean_ctor_get(v___x_2084_, 7);
v_snapshotTasks_2092_ = lean_ctor_get(v___x_2084_, 8);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v___x_2084_, 5);
lean_dec(v_unused_2132_);
v___x_2094_ = v___x_2084_;
v_isShared_2095_ = v_isSharedCheck_2131_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_snapshotTasks_2092_);
lean_inc(v_infoState_2091_);
lean_inc(v_messages_2090_);
lean_inc(v_traceState_2089_);
lean_inc(v_auxDeclNGen_2088_);
lean_inc(v_ngen_2087_);
lean_inc(v_nextMacroScope_2086_);
lean_inc(v_env_2085_);
lean_dec(v___x_2084_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2131_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2096_ = l_Lean_Environment_setExporting(v_env_2085_, v_isExporting_2076_);
v___x_2097_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 5, v___x_2097_);
lean_ctor_set(v___x_2094_, 0, v___x_2096_);
v___x_2099_ = v___x_2094_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_nextMacroScope_2086_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_ngen_2087_);
lean_ctor_set(v_reuseFailAlloc_2130_, 3, v_auxDeclNGen_2088_);
lean_ctor_set(v_reuseFailAlloc_2130_, 4, v_traceState_2089_);
lean_ctor_set(v_reuseFailAlloc_2130_, 5, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2130_, 6, v_messages_2090_);
lean_ctor_set(v_reuseFailAlloc_2130_, 7, v_infoState_2091_);
lean_ctor_set(v_reuseFailAlloc_2130_, 8, v_snapshotTasks_2092_);
v___x_2099_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; lean_object* v_r_2101_; 
v___x_2100_ = lean_st_ref_set(v___y_2078_, v___x_2099_);
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
v_r_2101_ = lean_apply_3(v_x_2075_, v___y_2077_, v___y_2078_, lean_box(0));
if (lean_obj_tag(v_r_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2118_; 
v_a_2102_ = lean_ctor_get(v_r_2101_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_r_2101_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2104_ = v_r_2101_;
v_isShared_2105_ = v_isSharedCheck_2118_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v_r_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2118_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
lean_inc(v_a_2102_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set_tag(v___x_2104_, 1);
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
v___x_2108_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2078_, v_isExporting_2082_, v___x_2097_, v___x_2107_);
lean_dec_ref(v___x_2107_);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v___x_2108_, 0);
lean_dec(v_unused_2116_);
v___x_2110_ = v___x_2108_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_dec(v___x_2108_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v_a_2102_);
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2102_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
v_a_2119_ = lean_ctor_get(v_r_2101_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v_r_2101_, 1);
v___x_2120_ = lean_box(0);
v___x_2121_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2078_, v_isExporting_2082_, v___x_2097_, v___x_2120_);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2128_ == 0)
{
lean_object* v_unused_2129_; 
v_unused_2129_ = lean_ctor_get(v___x_2121_, 0);
lean_dec(v_unused_2129_);
v___x_2123_ = v___x_2121_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_dec(v___x_2121_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set_tag(v___x_2123_, 1);
lean_ctor_set(v___x_2123_, 0, v_a_2119_);
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2119_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___boxed(lean_object* v_x_2138_, lean_object* v_isExporting_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
uint8_t v_isExporting_boxed_2143_; lean_object* v_res_2144_; 
v_isExporting_boxed_2143_ = lean_unbox(v_isExporting_2139_);
v_res_2144_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2138_, v_isExporting_boxed_2143_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(lean_object* v_x_2145_, uint8_t v_when_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
if (v_when_2146_ == 0)
{
lean_object* v___x_2150_; 
lean_inc(v___y_2148_);
lean_inc_ref(v___y_2147_);
v___x_2150_ = lean_apply_3(v_x_2145_, v___y_2147_, v___y_2148_, lean_box(0));
return v___x_2150_;
}
else
{
uint8_t v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = 0;
v___x_2152_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2145_, v___x_2151_, v___y_2147_, v___y_2148_);
return v___x_2152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg___boxed(lean_object* v_x_2153_, lean_object* v_when_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
uint8_t v_when_boxed_2158_; lean_object* v_res_2159_; 
v_when_boxed_2158_ = lean_unbox(v_when_2154_);
v_res_2159_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v_x_2153_, v_when_boxed_2158_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(lean_object* v_ctx_2160_, lean_object* v_catName_2161_, lean_object* v_constName_2162_, uint8_t v_builtin_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; lean_object* v___f_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2167_ = lean_box(v_builtin_2163_);
v___f_2168_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_2168_, 0, v_constName_2162_);
lean_closure_set(v___f_2168_, 1, v_ctx_2160_);
lean_closure_set(v___f_2168_, 2, v___x_2167_);
lean_closure_set(v___f_2168_, 3, v_catName_2161_);
v___x_2169_ = 1;
v___x_2170_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v___f_2168_, v___x_2169_, v___y_2164_, v___y_2165_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed(lean_object* v_ctx_2171_, lean_object* v_catName_2172_, lean_object* v_constName_2173_, lean_object* v_builtin_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v_builtin_boxed_2178_; lean_object* v_res_2179_; 
v_builtin_boxed_2178_ = lean_unbox(v_builtin_2174_);
v_res_2179_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(v_ctx_2171_, v_catName_2172_, v_constName_2173_, v_builtin_boxed_2178_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg(lean_object* v_ctx_2180_){
_start:
{
lean_object* v___f_2182_; lean_object* v___x_2183_; 
v___f_2182_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed), 7, 1);
lean_closure_set(v___f_2182_, 0, v_ctx_2180_);
v___x_2183_ = l_Lean_Parser_registerParserAttributeHook(v___f_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___boxed(lean_object* v_ctx_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v_ctx_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object* v_00_u03b1_2187_, lean_object* v_ctx_2188_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v_ctx_2188_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___boxed(lean_object* v_00_u03b1_2191_, lean_object* v_ctx_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_ParserCompiler_registerParserCompiler(v_00_u03b1_2191_, v_ctx_2192_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(lean_object* v_00_u03b1_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(v_00_u03b1_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(lean_object* v_00_u03b1_2205_, lean_object* v_typeName_2206_, lean_object* v_constName_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v_typeName_2206_, v_constName_2207_, v___y_2208_, v___y_2209_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___boxed(lean_object* v_00_u03b1_2212_, lean_object* v_typeName_2213_, lean_object* v_constName_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(v_00_u03b1_2212_, v_typeName_2213_, v_constName_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(lean_object* v_00_u03b1_2219_, lean_object* v_x_2220_, uint8_t v_isExporting_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2220_, v_isExporting_2221_, v___y_2222_, v___y_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2226_, lean_object* v_x_2227_, lean_object* v_isExporting_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
uint8_t v_isExporting_boxed_2232_; lean_object* v_res_2233_; 
v_isExporting_boxed_2232_ = lean_unbox(v_isExporting_2228_);
v_res_2233_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(v_00_u03b1_2226_, v_x_2227_, v_isExporting_boxed_2232_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(lean_object* v_00_u03b1_2234_, lean_object* v_x_2235_, uint8_t v_when_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v_x_2235_, v_when_2236_, v___y_2237_, v___y_2238_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___boxed(lean_object* v_00_u03b1_2241_, lean_object* v_x_2242_, lean_object* v_when_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
uint8_t v_when_boxed_2247_; lean_object* v_res_2248_; 
v_when_boxed_2247_ = lean_unbox(v_when_2243_);
v_res_2248_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(v_00_u03b1_2241_, v_x_2242_, v_when_boxed_2247_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(lean_object* v_00_u03b1_2249_, lean_object* v_constName_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_2250_, v___y_2251_, v___y_2252_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2255_, lean_object* v_constName_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(v_00_u03b1_2255_, v_constName_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(lean_object* v_00_u03b1_2261_, lean_object* v_x_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v_x_2262_, v___y_2263_, v___y_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2267_, lean_object* v_x_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(v_00_u03b1_2267_, v_x_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2273_, lean_object* v_ref_2274_, lean_object* v_constName_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_2274_, v_constName_2275_, v___y_2276_, v___y_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2280_, lean_object* v_ref_2281_, lean_object* v_constName_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(v_00_u03b1_2280_, v_ref_2281_, v_constName_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v_ref_2281_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2287_, lean_object* v_msg_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_2288_, v___y_2289_, v___y_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2293_, lean_object* v_msg_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(v_00_u03b1_2293_, v_msg_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b1_2299_, lean_object* v_ref_2300_, lean_object* v_msg_2301_, lean_object* v_declHint_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_2300_, v_msg_2301_, v_declHint_2302_, v___y_2303_, v___y_2304_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b1_2307_, lean_object* v_ref_2308_, lean_object* v_msg_2309_, lean_object* v_declHint_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_2307_, v_ref_2308_, v_msg_2309_, v_declHint_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v_ref_2308_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(lean_object* v_msg_2315_, lean_object* v_declHint_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_2315_, v_declHint_2316_, v___y_2318_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___boxed(lean_object* v_msg_2321_, lean_object* v_declHint_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(v_msg_2321_, v_declHint_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_2327_, lean_object* v_ref_2328_, lean_object* v_msg_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_2328_, v_msg_2329_, v___y_2330_, v___y_2331_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2334_, lean_object* v_ref_2335_, lean_object* v_msg_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(v_00_u03b1_2334_, v_ref_2335_, v_msg_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v_ref_2335_);
return v_res_2340_;
}
}
lean_object* runtime_initialize_Lean_Meta_ReduceEval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_ParserCompiler_Attribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ParserCompiler(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
