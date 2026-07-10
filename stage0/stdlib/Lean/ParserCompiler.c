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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_141_; lean_object* v___x_187_; uint8_t v_transparency_188_; uint8_t v___x_189_; uint8_t v___x_190_; 
v___x_187_ = l_Lean_Meta_Context_config(v_a_135_);
v_transparency_188_ = lean_ctor_get_uint8(v___x_187_, 9);
lean_dec_ref(v___x_187_);
v___x_189_ = 1;
v___x_190_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_188_, v___x_189_);
if (v___x_190_ == 0)
{
v___y_141_ = v_transparency_188_;
goto v___jp_140_;
}
else
{
v___y_141_ = v___x_189_;
goto v___jp_140_;
}
v___jp_140_:
{
lean_object* v___x_142_; uint8_t v_foApprox_143_; uint8_t v_ctxApprox_144_; uint8_t v_quasiPatternApprox_145_; uint8_t v_constApprox_146_; uint8_t v_isDefEqStuckEx_147_; uint8_t v_unificationHints_148_; uint8_t v_proofIrrelevance_149_; uint8_t v_assignSyntheticOpaque_150_; uint8_t v_offsetCnstrs_151_; uint8_t v_etaStruct_152_; uint8_t v_univApprox_153_; uint8_t v_iota_154_; uint8_t v_beta_155_; uint8_t v_proj_156_; uint8_t v_zeta_157_; uint8_t v_zetaDelta_158_; uint8_t v_zetaUnused_159_; uint8_t v_zetaHave_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_186_; 
v___x_142_ = l_Lean_Meta_Context_config(v_a_135_);
v_foApprox_143_ = lean_ctor_get_uint8(v___x_142_, 0);
v_ctxApprox_144_ = lean_ctor_get_uint8(v___x_142_, 1);
v_quasiPatternApprox_145_ = lean_ctor_get_uint8(v___x_142_, 2);
v_constApprox_146_ = lean_ctor_get_uint8(v___x_142_, 3);
v_isDefEqStuckEx_147_ = lean_ctor_get_uint8(v___x_142_, 4);
v_unificationHints_148_ = lean_ctor_get_uint8(v___x_142_, 5);
v_proofIrrelevance_149_ = lean_ctor_get_uint8(v___x_142_, 6);
v_assignSyntheticOpaque_150_ = lean_ctor_get_uint8(v___x_142_, 7);
v_offsetCnstrs_151_ = lean_ctor_get_uint8(v___x_142_, 8);
v_etaStruct_152_ = lean_ctor_get_uint8(v___x_142_, 10);
v_univApprox_153_ = lean_ctor_get_uint8(v___x_142_, 11);
v_iota_154_ = lean_ctor_get_uint8(v___x_142_, 12);
v_beta_155_ = lean_ctor_get_uint8(v___x_142_, 13);
v_proj_156_ = lean_ctor_get_uint8(v___x_142_, 14);
v_zeta_157_ = lean_ctor_get_uint8(v___x_142_, 15);
v_zetaDelta_158_ = lean_ctor_get_uint8(v___x_142_, 16);
v_zetaUnused_159_ = lean_ctor_get_uint8(v___x_142_, 17);
v_zetaHave_160_ = lean_ctor_get_uint8(v___x_142_, 18);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_186_ == 0)
{
v___x_162_ = v___x_142_;
v_isShared_163_ = v_isSharedCheck_186_;
goto v_resetjp_161_;
}
else
{
lean_dec(v___x_142_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_186_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
uint8_t v_trackZetaDelta_164_; lean_object* v_zetaDeltaSet_165_; lean_object* v_lctx_166_; lean_object* v_localInstances_167_; lean_object* v_defEqCtx_x3f_168_; lean_object* v_synthPendingDepth_169_; lean_object* v_canUnfold_x3f_170_; uint8_t v_univApprox_171_; uint8_t v_inTypeClassResolution_172_; uint8_t v_cacheInferType_173_; lean_object* v_config_175_; 
v_trackZetaDelta_164_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*7);
v_zetaDeltaSet_165_ = lean_ctor_get(v_a_135_, 1);
v_lctx_166_ = lean_ctor_get(v_a_135_, 2);
v_localInstances_167_ = lean_ctor_get(v_a_135_, 3);
v_defEqCtx_x3f_168_ = lean_ctor_get(v_a_135_, 4);
v_synthPendingDepth_169_ = lean_ctor_get(v_a_135_, 5);
v_canUnfold_x3f_170_ = lean_ctor_get(v_a_135_, 6);
v_univApprox_171_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_172_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*7 + 2);
v_cacheInferType_173_ = lean_ctor_get_uint8(v_a_135_, sizeof(void*)*7 + 3);
if (v_isShared_163_ == 0)
{
v_config_175_ = v___x_162_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 0, v_foApprox_143_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 1, v_ctxApprox_144_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 2, v_quasiPatternApprox_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 3, v_constApprox_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 4, v_isDefEqStuckEx_147_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 5, v_unificationHints_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 6, v_proofIrrelevance_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 7, v_assignSyntheticOpaque_150_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 8, v_offsetCnstrs_151_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 10, v_etaStruct_152_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 11, v_univApprox_153_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 12, v_iota_154_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 13, v_beta_155_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 14, v_proj_156_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 15, v_zeta_157_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 16, v_zetaDelta_158_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 17, v_zetaUnused_159_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, 18, v_zetaHave_160_);
v_config_175_ = v_reuseFailAlloc_185_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
uint64_t v___x_176_; uint64_t v___x_177_; uint64_t v___x_178_; uint64_t v___x_179_; uint64_t v___x_180_; uint64_t v_key_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_ctor_set_uint8(v_config_175_, 9, v___y_141_);
v___x_176_ = l_Lean_Meta_Context_configKey(v_a_135_);
v___x_177_ = 3ULL;
v___x_178_ = lean_uint64_shift_right(v___x_176_, v___x_177_);
v___x_179_ = lean_uint64_shift_left(v___x_178_, v___x_177_);
v___x_180_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_141_);
v_key_181_ = lean_uint64_lor(v___x_179_, v___x_180_);
v___x_182_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_182_, 0, v_config_175_);
lean_ctor_set_uint64(v___x_182_, sizeof(void*)*1, v_key_181_);
lean_inc(v_canUnfold_x3f_170_);
lean_inc(v_synthPendingDepth_169_);
lean_inc(v_defEqCtx_x3f_168_);
lean_inc_ref(v_localInstances_167_);
lean_inc_ref(v_lctx_166_);
lean_inc(v_zetaDeltaSet_165_);
v___x_183_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v_zetaDeltaSet_165_);
lean_ctor_set(v___x_183_, 2, v_lctx_166_);
lean_ctor_set(v___x_183_, 3, v_localInstances_167_);
lean_ctor_set(v___x_183_, 4, v_defEqCtx_x3f_168_);
lean_ctor_set(v___x_183_, 5, v_synthPendingDepth_169_);
lean_ctor_set(v___x_183_, 6, v_canUnfold_x3f_170_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*7, v_trackZetaDelta_164_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*7 + 1, v_univApprox_171_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*7 + 2, v_inTypeClassResolution_172_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*7 + 3, v_cacheInferType_173_);
v___x_184_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(v_e_134_, v___x_183_, v_a_136_, v_a_137_, v_a_138_);
lean_dec_ref_known(v___x_183_, 7);
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1___boxed(lean_object* v_e_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1(v_e_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(lean_object* v_type_198_, lean_object* v_k_199_, uint8_t v_cleanupAnnotations_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___f_206_; uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___f_206_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_206_, 0, v_k_199_);
v___x_207_ = 0;
v___x_208_ = lean_box(0);
v___x_209_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_207_, v___x_208_, v_type_198_, v___f_206_, v_cleanupAnnotations_200_, v___x_207_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v_a_218_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_209_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_209_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg___boxed(lean_object* v_type_226_, lean_object* v_k_227_, lean_object* v_cleanupAnnotations_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_234_; lean_object* v_res_235_; 
v_cleanupAnnotations_boxed_234_ = lean_unbox(v_cleanupAnnotations_228_);
v_res_235_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_type_226_, v_k_227_, v_cleanupAnnotations_boxed_234_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3(lean_object* v_00_u03b1_236_, lean_object* v_type_237_, lean_object* v_k_238_, uint8_t v_cleanupAnnotations_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_type_237_, v_k_238_, v_cleanupAnnotations_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___boxed(lean_object* v_00_u03b1_246_, lean_object* v_type_247_, lean_object* v_k_248_, lean_object* v_cleanupAnnotations_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_255_; lean_object* v_res_256_; 
v_cleanupAnnotations_boxed_255_ = lean_unbox(v_cleanupAnnotations_249_);
v_res_256_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3(v_00_u03b1_246_, v_type_247_, v_k_248_, v_cleanupAnnotations_boxed_255_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(lean_object* v___x_257_, lean_object* v_as_258_, size_t v_i_259_, size_t v_stop_260_, lean_object* v_b_261_){
_start:
{
lean_object* v___y_263_; uint8_t v___x_267_; 
v___x_267_ = lean_usize_dec_eq(v_i_259_, v_stop_260_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v_fst_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_268_ = lean_array_uget_borrowed(v_as_258_, v_i_259_);
v_fst_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc_ref(v___x_257_);
v___x_270_ = l_Lean_LocalContext_getFVar_x21(v___x_257_, v_fst_269_);
v___x_271_ = l_Lean_LocalDecl_type(v___x_270_);
lean_dec_ref(v___x_270_);
v___x_272_ = ((lean_object*)(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2));
v___x_273_ = l_Lean_Expr_isConstOf(v___x_271_, v___x_272_);
lean_dec_ref(v___x_271_);
if (v___x_273_ == 0)
{
v___y_263_ = v_b_261_;
goto v___jp_262_;
}
else
{
lean_object* v___x_274_; 
lean_inc(v___x_268_);
v___x_274_ = lean_array_push(v_b_261_, v___x_268_);
v___y_263_ = v___x_274_;
goto v___jp_262_;
}
}
else
{
lean_dec_ref(v___x_257_);
return v_b_261_;
}
v___jp_262_:
{
size_t v___x_264_; size_t v___x_265_; 
v___x_264_ = ((size_t)1ULL);
v___x_265_ = lean_usize_add(v_i_259_, v___x_264_);
v_i_259_ = v___x_265_;
v_b_261_ = v___y_263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2___boxed(lean_object* v___x_275_, lean_object* v_as_276_, lean_object* v_i_277_, lean_object* v_stop_278_, lean_object* v_b_279_){
_start:
{
size_t v_i_boxed_280_; size_t v_stop_boxed_281_; lean_object* v_res_282_; 
v_i_boxed_280_ = lean_unbox_usize(v_i_277_);
lean_dec(v_i_277_);
v_stop_boxed_281_ = lean_unbox_usize(v_stop_278_);
lean_dec(v_stop_278_);
v_res_282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v___x_275_, v_as_276_, v_i_boxed_280_, v_stop_boxed_281_, v_b_279_);
lean_dec_ref(v_as_276_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed(lean_object* v_x_283_, lean_object* v_e_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(v_x_283_, v_e_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec_ref(v_x_283_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(lean_object* v_a_293_, lean_object* v_params_294_, lean_object* v_x_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; lean_object* v___y_303_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_316_ = l_Array_zipIdx___redArg(v_params_294_, v___x_301_);
v___x_317_ = lean_array_get_size(v___x_316_);
v___x_318_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0));
v___x_319_ = lean_nat_dec_lt(v___x_301_, v___x_317_);
if (v___x_319_ == 0)
{
lean_dec_ref(v___x_316_);
v___y_303_ = v___x_318_;
goto v___jp_302_;
}
else
{
lean_object* v_lctx_320_; uint8_t v___x_321_; 
v_lctx_320_ = lean_ctor_get(v___y_296_, 2);
v___x_321_ = lean_nat_dec_le(v___x_317_, v___x_317_);
if (v___x_321_ == 0)
{
if (v___x_319_ == 0)
{
lean_dec_ref(v___x_316_);
v___y_303_ = v___x_318_;
goto v___jp_302_;
}
else
{
size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; 
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_317_);
lean_inc_ref(v_lctx_320_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v_lctx_320_, v___x_316_, v___x_322_, v___x_323_, v___x_318_);
lean_dec_ref(v___x_316_);
v___y_303_ = v___x_324_;
goto v___jp_302_;
}
}
else
{
size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; 
v___x_325_ = ((size_t)0ULL);
v___x_326_ = lean_usize_of_nat(v___x_317_);
lean_inc_ref(v_lctx_320_);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v_lctx_320_, v___x_316_, v___x_325_, v___x_326_, v___x_318_);
lean_dec_ref(v___x_316_);
v___y_303_ = v___x_327_;
goto v___jp_302_;
}
}
v___jp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = lean_array_get_size(v___y_303_);
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_dec_eq(v___x_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec_ref(v___y_303_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
else
{
lean_object* v___x_309_; lean_object* v_snd_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_309_ = lean_array_fget(v___y_303_, v___x_301_);
lean_dec_ref(v___y_303_);
v_snd_310_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_snd_310_);
lean_dec(v___x_309_);
v___x_311_ = l_Lean_Expr_getAppNumArgs(v_a_293_);
v___x_312_ = lean_nat_sub(v___x_311_, v_snd_310_);
lean_dec(v_snd_310_);
lean_dec(v___x_311_);
v___x_313_ = lean_nat_sub(v___x_312_, v___x_305_);
lean_dec(v___x_312_);
v___x_314_ = l_Lean_Expr_getRevArg_x21(v_a_293_, v___x_313_);
v___x_315_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v___x_314_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed(lean_object* v_a_328_, lean_object* v_params_329_, lean_object* v_x_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(v_a_328_, v_params_329_, v_x_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec_ref(v_x_330_);
lean_dec_ref(v_a_328_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f(lean_object* v_e_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___y_364_; uint8_t v___y_365_; lean_object* v___x_368_; 
v___x_368_ = l_Lean_Meta_whnfCore(v_e_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___f_395_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v___f_395_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed), 7, 0);
switch(lean_obj_tag(v_a_369_))
{
case 6:
{
goto v___jp_396_;
}
case 8:
{
goto v___jp_396_;
}
default: 
{
lean_object* v___f_399_; uint8_t v___y_401_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
lean_dec_ref(v___f_395_);
lean_inc(v_a_369_);
v___f_399_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed), 8, 1);
lean_closure_set(v___f_399_, 0, v_a_369_);
v___x_425_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5));
v___x_426_ = lean_unsigned_to_nat(3u);
v___x_427_ = l_Lean_Expr_isAppOfArity(v_a_369_, v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_428_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7));
v___x_429_ = lean_unsigned_to_nat(4u);
v___x_430_ = l_Lean_Expr_isAppOfArity(v_a_369_, v___x_428_, v___x_429_);
v___y_401_ = v___x_430_;
goto v___jp_400_;
}
else
{
v___y_401_ = v___x_427_;
goto v___jp_400_;
}
v___jp_400_:
{
if (v___y_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_402_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1));
v___x_403_ = lean_unsigned_to_nat(2u);
v___x_404_ = l_Lean_Expr_isAppOfArity(v_a_369_, v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3));
v___x_406_ = l_Lean_Expr_isAppOfArity(v_a_369_, v___x_405_, v___x_403_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = l_Lean_Expr_getAppFn(v_a_369_);
lean_dec(v_a_369_);
lean_inc(v_a_361_);
lean_inc_ref(v_a_360_);
lean_inc(v_a_359_);
lean_inc_ref(v_a_358_);
v___x_408_ = lean_infer_type(v___x_407_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_410_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v___x_410_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_409_, v___f_399_, v___x_406_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
return v___x_410_;
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec_ref(v___f_399_);
v_a_411_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_408_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_408_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref(v___f_399_);
v___x_419_ = lean_unsigned_to_nat(1u);
v___x_420_ = l_Lean_Expr_getAppNumArgs(v_a_369_);
v___x_421_ = lean_nat_sub(v___x_420_, v___x_419_);
lean_dec(v___x_420_);
v___x_422_ = lean_nat_sub(v___x_421_, v___x_419_);
lean_dec(v___x_421_);
v___x_423_ = l_Lean_Expr_getRevArg_x21(v_a_369_, v___x_422_);
lean_dec(v_a_369_);
v_e_357_ = v___x_423_;
goto _start;
}
}
else
{
lean_dec_ref(v___f_399_);
goto v___jp_370_;
}
}
else
{
lean_dec_ref(v___f_399_);
goto v___jp_370_;
}
}
}
}
v___jp_370_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_371_ = l_Lean_Expr_getAppNumArgs(v_a_369_);
v___x_372_ = lean_unsigned_to_nat(1u);
v___x_373_ = lean_nat_sub(v___x_371_, v___x_372_);
lean_dec(v___x_371_);
v___x_374_ = l_Lean_Expr_getRevArg_x21(v_a_369_, v___x_373_);
lean_dec(v_a_369_);
v___x_375_ = l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1(v___x_374_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_384_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_384_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v_a_376_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_380_);
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_394_; 
v_a_385_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_394_ == 0)
{
v___x_387_ = v___x_375_;
v_isShared_388_ = v_isSharedCheck_394_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_375_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_394_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
lean_inc(v_a_385_);
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_393_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
uint8_t v___x_391_; 
v___x_391_ = l_Lean_Exception_isInterrupt(v_a_385_);
if (v___x_391_ == 0)
{
uint8_t v___x_392_; 
v___x_392_ = l_Lean_Exception_isRuntime(v_a_385_);
v___y_364_ = v___x_390_;
v___y_365_ = v___x_392_;
goto v___jp_363_;
}
else
{
lean_dec(v_a_385_);
v___y_364_ = v___x_390_;
v___y_365_ = v___x_391_;
goto v___jp_363_;
}
}
}
}
}
v___jp_396_:
{
uint8_t v___x_397_; lean_object* v___x_398_; 
v___x_397_ = 0;
v___x_398_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_a_369_, v___f_395_, v___x_397_, v___x_397_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
return v___x_398_;
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_a_431_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_368_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_368_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
v___jp_363_:
{
if (v___y_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec_ref(v___y_364_);
v___x_366_ = lean_box(0);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
else
{
return v___y_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(lean_object* v_x_439_, lean_object* v_e_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v_e_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_parserNodeKind_x3f___boxed(lean_object* v_e_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v_e_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(lean_object* v_ctx_457_, lean_object* v_as_458_, size_t v_i_459_, size_t v_stop_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v___x_467_; 
v___x_467_ = lean_usize_dec_eq(v_i_459_, v_stop_460_);
if (v___x_467_ == 0)
{
size_t v___x_468_; size_t v___x_469_; lean_object* v_a_471_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_468_ = ((size_t)1ULL);
v___x_469_ = lean_usize_sub(v_i_459_, v___x_468_);
v___x_476_ = lean_array_uget_borrowed(v_as_458_, v___x_469_);
lean_inc(v___y_465_);
lean_inc_ref(v___y_464_);
lean_inc(v___y_463_);
lean_inc_ref(v___y_462_);
lean_inc(v___x_476_);
v___x_477_ = lean_infer_type(v___x_476_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_479_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_477_, 1);
lean_inc_ref(v_ctx_457_);
v___x_479_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_457_, v_a_478_);
lean_dec(v_a_478_);
v_a_471_ = v___x_479_;
goto v___jp_470_;
}
else
{
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_480_; 
v_a_480_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_477_, 1);
v_a_471_ = v_a_480_;
goto v___jp_470_;
}
else
{
lean_dec_ref(v_b_461_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_481_; 
v_a_481_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_477_, 1);
v_i_459_ = v___x_469_;
v_b_461_ = v_a_481_;
goto _start;
}
else
{
lean_dec_ref(v_ctx_457_);
return v___x_477_;
}
}
}
v___jp_470_:
{
lean_object* v___x_472_; uint8_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__1));
v___x_473_ = 0;
v___x_474_ = l_Lean_mkForall(v___x_472_, v___x_473_, v_a_471_, v_b_461_);
v_i_459_ = v___x_469_;
v_b_461_ = v___x_474_;
goto _start;
}
}
else
{
lean_object* v___x_483_; 
lean_dec_ref(v_ctx_457_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v_b_461_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___boxed(lean_object* v_ctx_484_, lean_object* v_as_485_, lean_object* v_i_486_, lean_object* v_stop_487_, lean_object* v_b_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
size_t v_i_boxed_494_; size_t v_stop_boxed_495_; lean_object* v_res_496_; 
v_i_boxed_494_ = lean_unbox_usize(v_i_486_);
lean_dec(v_i_486_);
v_stop_boxed_495_ = lean_unbox_usize(v_stop_487_);
lean_dec(v_stop_487_);
v_res_496_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_484_, v_as_485_, v_i_boxed_494_, v_stop_boxed_495_, v_b_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec_ref(v_as_485_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3(lean_object* v_ctx_497_, lean_object* v_params_498_, lean_object* v_x_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_505_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_497_);
v___x_506_ = lean_box(0);
v___x_507_ = l_Lean_mkConst(v___x_505_, v___x_506_);
v___x_508_ = lean_array_get_size(v_params_498_);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = lean_nat_dec_lt(v___x_509_, v___x_508_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec_ref(v_ctx_497_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_507_);
return v___x_511_;
}
else
{
size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_usize_of_nat(v___x_508_);
v___x_513_ = ((size_t)0ULL);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_497_, v_params_498_, v___x_512_, v___x_513_, v___x_507_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3___boxed(lean_object* v_ctx_515_, lean_object* v_params_516_, lean_object* v_x_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3(v_ctx_515_, v_params_516_, v_x_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v_x_517_);
lean_dec_ref(v_params_516_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0(lean_object* v_k_524_, uint8_t v_usedLetOnly_525_, lean_object* v_xs_526_, lean_object* v_b_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; 
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
lean_inc_ref(v___y_528_);
lean_inc_ref(v_xs_526_);
v___x_533_ = lean_apply_7(v_k_524_, v_xs_526_, v_b_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, lean_box(0));
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; uint8_t v___x_535_; uint8_t v___x_536_; lean_object* v___x_537_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = 0;
v___x_536_ = 1;
v___x_537_ = l_Lean_Meta_mkLambdaFVars(v_xs_526_, v_a_534_, v___x_535_, v_usedLetOnly_525_, v___x_535_, v___x_535_, v___x_536_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec_ref(v_xs_526_);
return v___x_537_;
}
else
{
lean_dec_ref(v_xs_526_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0___boxed(lean_object* v_k_538_, lean_object* v_usedLetOnly_539_, lean_object* v_xs_540_, lean_object* v_b_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
uint8_t v_usedLetOnly_boxed_547_; lean_object* v_res_548_; 
v_usedLetOnly_boxed_547_ = lean_unbox(v_usedLetOnly_539_);
v_res_548_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0(v_k_538_, v_usedLetOnly_boxed_547_, v_xs_540_, v_b_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(lean_object* v_e_549_, lean_object* v_k_550_, uint8_t v_cleanupAnnotations_551_, uint8_t v_preserveNondepLet_552_, uint8_t v_usedLetOnly_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; lean_object* v___f_560_; lean_object* v___x_561_; 
v___x_559_ = lean_box(v_usedLetOnly_553_);
v___f_560_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0___boxed), 9, 2);
lean_closure_set(v___f_560_, 0, v_k_550_);
lean_closure_set(v___f_560_, 1, v___x_559_);
v___x_561_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_e_549_, v___f_560_, v_cleanupAnnotations_551_, v_preserveNondepLet_552_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___boxed(lean_object* v_e_562_, lean_object* v_k_563_, lean_object* v_cleanupAnnotations_564_, lean_object* v_preserveNondepLet_565_, lean_object* v_usedLetOnly_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_572_; uint8_t v_preserveNondepLet_boxed_573_; uint8_t v_usedLetOnly_boxed_574_; lean_object* v_res_575_; 
v_cleanupAnnotations_boxed_572_ = lean_unbox(v_cleanupAnnotations_564_);
v_preserveNondepLet_boxed_573_ = lean_unbox(v_preserveNondepLet_565_);
v_usedLetOnly_boxed_574_ = lean_unbox(v_usedLetOnly_566_);
v_res_575_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_e_562_, v_k_563_, v_cleanupAnnotations_boxed_572_, v_preserveNondepLet_boxed_573_, v_usedLetOnly_boxed_574_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_575_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_576_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
lean_ctor_set(v___x_581_, 3, v___x_580_);
lean_ctor_set(v___x_581_, 4, v___x_579_);
lean_ctor_set(v___x_581_, 5, v___x_579_);
lean_ctor_set(v___x_581_, 6, v___x_579_);
lean_ctor_set(v___x_581_, 7, v___x_579_);
lean_ctor_set(v___x_581_, 8, v___x_579_);
lean_ctor_set(v___x_581_, 9, v___x_579_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_unsigned_to_nat(32u);
v___x_583_ = lean_mk_empty_array_with_capacity(v___x_582_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4(void){
_start:
{
size_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_585_ = ((size_t)5ULL);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_unsigned_to_nat(32u);
v___x_588_ = lean_mk_empty_array_with_capacity(v___x_587_);
v___x_589_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
v___x_590_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___x_588_);
lean_ctor_set(v___x_590_, 2, v___x_586_);
lean_ctor_set(v___x_590_, 3, v___x_586_);
lean_ctor_set_usize(v___x_590_, 4, v___x_585_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = lean_box(1);
v___x_592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_593_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
v___x_594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_592_);
lean_ctor_set(v___x_594_, 2, v___x_591_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
v___x_597_ = l_Lean_stringToMessageData(v___x_596_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
v___x_600_ = l_Lean_stringToMessageData(v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
v___x_603_ = l_Lean_stringToMessageData(v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
v___x_606_ = l_Lean_stringToMessageData(v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14));
v___x_609_ = l_Lean_stringToMessageData(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16));
v___x_612_ = l_Lean_stringToMessageData(v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18));
v___x_615_ = l_Lean_stringToMessageData(v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* v_msg_616_, lean_object* v_declHint_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; lean_object* v_env_621_; uint8_t v___y_623_; uint8_t v___x_679_; uint8_t v___x_680_; 
v___x_620_ = lean_st_ref_get(v___y_618_);
v_env_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc_ref(v_env_621_);
lean_dec(v___x_620_);
v___x_679_ = l_Lean_Name_isAnonymous(v_declHint_617_);
v___x_680_ = lean_bool_not(v___x_679_);
if (v___x_680_ == 0)
{
v___y_623_ = v___x_680_;
goto v___jp_622_;
}
else
{
uint8_t v_isExporting_681_; 
v_isExporting_681_ = lean_ctor_get_uint8(v_env_621_, sizeof(void*)*8);
v___y_623_ = v_isExporting_681_;
goto v___jp_622_;
}
v___jp_622_:
{
if (v___y_623_ == 0)
{
lean_object* v___x_624_; 
lean_dec_ref(v_env_621_);
lean_dec(v_declHint_617_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_msg_616_);
return v___x_624_;
}
else
{
uint8_t v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = 0;
lean_inc_ref(v_env_621_);
v___x_626_ = l_Lean_Environment_setExporting(v_env_621_, v___x_625_);
lean_inc(v_declHint_617_);
lean_inc_ref(v___x_626_);
v___x_627_ = l_Lean_Environment_contains(v___x_626_, v_declHint_617_, v___y_623_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
lean_dec_ref(v___x_626_);
lean_dec_ref(v_env_621_);
lean_dec(v_declHint_617_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_msg_616_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_c_634_; lean_object* v___x_635_; 
v___x_629_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_630_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_631_ = l_Lean_Options_empty;
v___x_632_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_632_, 0, v___x_626_);
lean_ctor_set(v___x_632_, 1, v___x_629_);
lean_ctor_set(v___x_632_, 2, v___x_630_);
lean_ctor_set(v___x_632_, 3, v___x_631_);
lean_inc(v_declHint_617_);
v___x_633_ = l_Lean_MessageData_ofConstName(v_declHint_617_, v___x_625_);
v_c_634_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_634_, 0, v___x_632_);
lean_ctor_set(v_c_634_, 1, v___x_633_);
v___x_635_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_621_, v_declHint_617_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec_ref(v_env_621_);
lean_dec(v_declHint_617_);
v___x_636_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_c_634_);
v___x_638_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_MessageData_note(v___x_639_);
v___x_641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_641_, 0, v_msg_616_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
else
{
lean_object* v_val_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_678_; 
v_val_643_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_678_ == 0)
{
v___x_645_ = v___x_635_;
v_isShared_646_ = v_isSharedCheck_678_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_val_643_);
lean_dec(v___x_635_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_678_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_mod_650_; uint8_t v___x_651_; 
v___x_647_ = lean_box(0);
v___x_648_ = l_Lean_Environment_header(v_env_621_);
lean_dec_ref(v_env_621_);
v___x_649_ = l_Lean_EnvironmentHeader_moduleNames(v___x_648_);
v_mod_650_ = lean_array_get(v___x_647_, v___x_649_, v_val_643_);
lean_dec(v_val_643_);
lean_dec_ref(v___x_649_);
v___x_651_ = l_Lean_isPrivateName(v_declHint_617_);
lean_dec(v_declHint_617_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_652_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v_c_634_);
v___x_654_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Lean_MessageData_ofName(v_mod_650_);
v___x_657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = l_Lean_MessageData_note(v___x_659_);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v_msg_616_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 0);
lean_ctor_set(v___x_645_, 0, v___x_661_);
v___x_663_ = v___x_645_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_665_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v_c_634_);
v___x_667_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Lean_MessageData_ofName(v_mod_650_);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = l_Lean_MessageData_note(v___x_672_);
v___x_674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_674_, 0, v_msg_616_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 0);
lean_ctor_set(v___x_645_, 0, v___x_674_);
v___x_676_ = v___x_645_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_682_, lean_object* v_declHint_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_682_, v_declHint_683_, v___y_684_);
lean_dec(v___y_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_687_, lean_object* v_declHint_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_704_; 
v___x_694_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_687_, v_declHint_688_, v___y_692_);
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_704_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_704_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_704_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_699_ = l_Lean_unknownIdentifierMessageTag;
v___x_700_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v_a_695_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_700_);
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_705_, lean_object* v_declHint_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_705_, v_declHint_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(lean_object* v_msgData_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; lean_object* v_env_720_; lean_object* v___x_721_; lean_object* v_mctx_722_; lean_object* v_lctx_723_; lean_object* v_options_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_719_ = lean_st_ref_get(v___y_717_);
v_env_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc_ref(v_env_720_);
lean_dec(v___x_719_);
v___x_721_ = lean_st_ref_get(v___y_715_);
v_mctx_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc_ref(v_mctx_722_);
lean_dec(v___x_721_);
v_lctx_723_ = lean_ctor_get(v___y_714_, 2);
v_options_724_ = lean_ctor_get(v___y_716_, 2);
lean_inc_ref(v_options_724_);
lean_inc_ref(v_lctx_723_);
v___x_725_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_725_, 0, v_env_720_);
lean_ctor_set(v___x_725_, 1, v_mctx_722_);
lean_ctor_set(v___x_725_, 2, v_lctx_723_);
lean_ctor_set(v___x_725_, 3, v_options_724_);
v___x_726_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v_msgData_713_);
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
v_ref_741_ = lean_ctor_get(v___y_738_, 5);
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
lean_object* v_fileName_766_; lean_object* v_fileMap_767_; lean_object* v_options_768_; lean_object* v_currRecDepth_769_; lean_object* v_maxRecDepth_770_; lean_object* v_ref_771_; lean_object* v_currNamespace_772_; lean_object* v_openDecls_773_; lean_object* v_initHeartbeats_774_; lean_object* v_maxHeartbeats_775_; lean_object* v_quotContext_776_; lean_object* v_currMacroScope_777_; uint8_t v_diag_778_; lean_object* v_cancelTk_x3f_779_; uint8_t v_suppressElabErrors_780_; lean_object* v_inheritedTraceOptions_781_; lean_object* v_ref_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_fileName_766_ = lean_ctor_get(v___y_763_, 0);
v_fileMap_767_ = lean_ctor_get(v___y_763_, 1);
v_options_768_ = lean_ctor_get(v___y_763_, 2);
v_currRecDepth_769_ = lean_ctor_get(v___y_763_, 3);
v_maxRecDepth_770_ = lean_ctor_get(v___y_763_, 4);
v_ref_771_ = lean_ctor_get(v___y_763_, 5);
v_currNamespace_772_ = lean_ctor_get(v___y_763_, 6);
v_openDecls_773_ = lean_ctor_get(v___y_763_, 7);
v_initHeartbeats_774_ = lean_ctor_get(v___y_763_, 8);
v_maxHeartbeats_775_ = lean_ctor_get(v___y_763_, 9);
v_quotContext_776_ = lean_ctor_get(v___y_763_, 10);
v_currMacroScope_777_ = lean_ctor_get(v___y_763_, 11);
v_diag_778_ = lean_ctor_get_uint8(v___y_763_, sizeof(void*)*14);
v_cancelTk_x3f_779_ = lean_ctor_get(v___y_763_, 12);
v_suppressElabErrors_780_ = lean_ctor_get_uint8(v___y_763_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_781_ = lean_ctor_get(v___y_763_, 13);
v_ref_782_ = l_Lean_replaceRef(v_ref_759_, v_ref_771_);
lean_inc_ref(v_inheritedTraceOptions_781_);
lean_inc(v_cancelTk_x3f_779_);
lean_inc(v_currMacroScope_777_);
lean_inc(v_quotContext_776_);
lean_inc(v_maxHeartbeats_775_);
lean_inc(v_initHeartbeats_774_);
lean_inc(v_openDecls_773_);
lean_inc(v_currNamespace_772_);
lean_inc(v_maxRecDepth_770_);
lean_inc(v_currRecDepth_769_);
lean_inc_ref(v_options_768_);
lean_inc_ref(v_fileMap_767_);
lean_inc_ref(v_fileName_766_);
v___x_783_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_783_, 0, v_fileName_766_);
lean_ctor_set(v___x_783_, 1, v_fileMap_767_);
lean_ctor_set(v___x_783_, 2, v_options_768_);
lean_ctor_set(v___x_783_, 3, v_currRecDepth_769_);
lean_ctor_set(v___x_783_, 4, v_maxRecDepth_770_);
lean_ctor_set(v___x_783_, 5, v_ref_782_);
lean_ctor_set(v___x_783_, 6, v_currNamespace_772_);
lean_ctor_set(v___x_783_, 7, v_openDecls_773_);
lean_ctor_set(v___x_783_, 8, v_initHeartbeats_774_);
lean_ctor_set(v___x_783_, 9, v_maxHeartbeats_775_);
lean_ctor_set(v___x_783_, 10, v_quotContext_776_);
lean_ctor_set(v___x_783_, 11, v_currMacroScope_777_);
lean_ctor_set(v___x_783_, 12, v_cancelTk_x3f_779_);
lean_ctor_set(v___x_783_, 13, v_inheritedTraceOptions_781_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*14, v_diag_778_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*14 + 1, v_suppressElabErrors_780_);
v___x_784_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v_msg_760_, v___y_761_, v___y_762_, v___x_783_, v___y_764_);
lean_dec_ref_known(v___x_783_, 14);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_785_, lean_object* v_msg_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_785_, v_msg_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v_ref_785_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_793_, lean_object* v_msg_794_, lean_object* v_declHint_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v_a_802_; lean_object* v___x_803_; 
v___x_801_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_794_, v_declHint_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref(v___x_801_);
v___x_803_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_793_, v_a_802_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_804_, lean_object* v_msg_805_, lean_object* v_declHint_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_804_, v_msg_805_, v_declHint_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v_ref_804_);
return v_res_812_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__0));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__2));
v___x_818_ = l_Lean_stringToMessageData(v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_819_, lean_object* v_constName_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_826_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_827_ = 0;
lean_inc(v_constName_820_);
v___x_828_ = l_Lean_MessageData_ofConstName(v_constName_820_, v___x_827_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_826_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_819_, v___x_831_, v_constName_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_833_, lean_object* v_constName_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_833_, v_constName_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v_ref_833_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(lean_object* v_constName_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_ref_847_; lean_object* v___x_848_; 
v_ref_847_ = lean_ctor_get(v___y_844_, 5);
v___x_848_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_847_, v_constName_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg___boxed(lean_object* v_constName_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(lean_object* v_constName_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; lean_object* v_env_863_; uint8_t v___x_864_; lean_object* v___x_865_; 
v___x_862_ = lean_st_ref_get(v___y_860_);
v_env_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc_ref(v_env_863_);
lean_dec(v___x_862_);
v___x_864_ = 0;
lean_inc(v_constName_856_);
v___x_865_ = l_Lean_Environment_find_x3f(v_env_863_, v_constName_856_, v___x_864_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
return v___x_866_;
}
else
{
lean_object* v_val_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec(v_constName_856_);
v_val_867_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_865_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_val_867_);
lean_dec(v___x_865_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set_tag(v___x_869_, 0);
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_val_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3___boxed(lean_object* v_constName_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(v_constName_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(lean_object* v_b_882_, lean_object* v_arg_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = l_Lean_Expr_app___override(v_b_882_, v_arg_883_);
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1___boxed(lean_object* v_b_892_, lean_object* v_arg_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_892_, v_arg_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(lean_object* v_x_900_, lean_object* v_b_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v_b_901_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed(lean_object* v_x_908_, lean_object* v_b_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(v_x_908_, v_b_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec_ref(v_x_908_);
return v_res_915_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_916_; lean_object* v_dummy_917_; 
v___x_916_ = lean_box(0);
v_dummy_917_ = l_Lean_Expr_sort___override(v___x_916_);
return v_dummy_917_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(lean_object* v_upperBound_919_, lean_object* v_params_920_, lean_object* v___x_921_, lean_object* v_ctx_922_, uint8_t v_builtin_923_, uint8_t v_force_924_, lean_object* v_a_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___y_933_; uint8_t v___x_955_; 
v___x_955_ = lean_nat_dec_lt(v_a_925_, v_upperBound_919_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_dec(v_a_925_);
lean_dec_ref(v_ctx_922_);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v_b_926_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = l_Lean_instInhabitedExpr;
v___x_958_ = lean_array_get_borrowed(v___x_957_, v_params_920_, v_a_925_);
lean_inc(v___y_930_);
lean_inc_ref(v___y_929_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___x_958_);
v___x_959_ = lean_infer_type(v___x_958_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___f_961_; uint8_t v___x_962_; lean_object* v___x_963_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v___f_961_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0));
v___x_962_ = 0;
v___x_963_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_960_, v___f_961_, v___x_962_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = lean_array_get_borrowed(v___x_957_, v___x_921_, v_a_925_);
v___x_966_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_922_);
v___x_967_ = l_Lean_Expr_isConstOf(v_a_964_, v___x_966_);
lean_dec(v___x_966_);
lean_dec(v_a_964_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; 
lean_inc(v___x_965_);
v___x_968_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_926_, v___x_965_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
v___y_933_ = v___x_968_;
goto v___jp_932_;
}
else
{
lean_object* v___x_969_; 
lean_inc(v___x_965_);
lean_inc_ref(v_ctx_922_);
v___x_969_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_922_, v_builtin_923_, v_force_924_, v___x_965_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_926_, v_a_970_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
v___y_933_ = v___x_971_;
goto v___jp_932_;
}
else
{
lean_dec_ref(v_b_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_ctx_922_);
return v___x_969_;
}
}
}
else
{
lean_dec_ref(v_b_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_ctx_922_);
return v___x_963_;
}
}
else
{
lean_dec_ref(v_b_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_ctx_922_);
return v___x_959_;
}
}
v___jp_932_:
{
if (lean_obj_tag(v___y_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_946_; 
v_a_934_ = lean_ctor_get(v___y_933_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___y_933_);
if (v_isSharedCheck_946_ == 0)
{
v___x_936_ = v___y_933_;
v_isShared_937_ = v_isSharedCheck_946_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___y_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_946_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
if (lean_obj_tag(v_a_934_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; 
lean_dec(v_a_925_);
lean_dec_ref(v_ctx_922_);
v_a_938_ = lean_ctor_get(v_a_934_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v_a_934_, 1);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_a_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_del_object(v___x_936_);
v_a_942_ = lean_ctor_get(v_a_934_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v_a_934_, 1);
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_add(v_a_925_, v___x_943_);
lean_dec(v_a_925_);
v_a_925_ = v___x_944_;
v_b_926_ = v_a_942_;
goto _start;
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec(v_a_925_);
lean_dec_ref(v_ctx_922_);
v_a_947_ = lean_ctor_get(v___y_933_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___y_933_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___y_933_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___y_933_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(lean_object* v_a_972_, lean_object* v_ctx_973_, uint8_t v_builtin_974_, uint8_t v_force_975_, lean_object* v___x_976_, lean_object* v_params_977_, lean_object* v_x_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_dummy_984_; lean_object* v_nargs_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___y_991_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v_dummy_984_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0, &l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0);
v_nargs_985_ = l_Lean_Expr_getAppNumArgs(v_a_972_);
lean_inc(v_nargs_985_);
v___x_986_ = lean_mk_array(v_nargs_985_, v_dummy_984_);
v___x_987_ = lean_unsigned_to_nat(1u);
v___x_988_ = lean_nat_sub(v_nargs_985_, v___x_987_);
lean_dec(v_nargs_985_);
v___x_989_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_972_, v___x_986_, v___x_988_);
v___x_994_ = lean_array_get_size(v_params_977_);
v___x_995_ = lean_array_get_size(v___x_989_);
v___x_996_ = lean_nat_dec_le(v___x_994_, v___x_995_);
if (v___x_996_ == 0)
{
v___y_991_ = v___x_995_;
goto v___jp_990_;
}
else
{
v___y_991_ = v___x_994_;
goto v___jp_990_;
}
v___jp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v___y_991_, v_params_977_, v___x_989_, v_ctx_973_, v_builtin_974_, v_force_975_, v___x_992_, v___x_976_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec_ref(v___x_989_);
lean_dec(v___y_991_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed(lean_object* v_a_997_, lean_object* v_ctx_998_, lean_object* v_builtin_999_, lean_object* v_force_1000_, lean_object* v___x_1001_, lean_object* v_params_1002_, lean_object* v_x_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
uint8_t v_builtin_boxed_1009_; uint8_t v_force_boxed_1010_; lean_object* v_res_1011_; 
v_builtin_boxed_1009_ = lean_unbox(v_builtin_999_);
v_force_boxed_1010_ = lean_unbox(v_force_1000_);
v_res_1011_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(v_a_997_, v_ctx_998_, v_builtin_boxed_1009_, v_force_boxed_1010_, v___x_1001_, v_params_1002_, v_x_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec_ref(v_x_1003_);
lean_dec_ref(v_params_1002_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed(lean_object* v_ctx_1012_, lean_object* v_builtin_1013_, lean_object* v_force_1014_, lean_object* v_x_1015_, lean_object* v_b_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
uint8_t v_builtin_boxed_1022_; uint8_t v_force_boxed_1023_; lean_object* v_res_1024_; 
v_builtin_boxed_1022_ = lean_unbox(v_builtin_1013_);
v_force_boxed_1023_ = lean_unbox(v_force_1014_);
v_res_1024_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(v_ctx_1012_, v_builtin_boxed_1022_, v_force_boxed_1023_, v_x_1015_, v_b_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_x_1015_);
return v_res_1024_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5);
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6);
v___x_1041_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
lean_ctor_set(v___x_1041_, 2, v___x_1040_);
lean_ctor_set(v___x_1041_, 3, v___x_1040_);
lean_ctor_set(v___x_1041_, 4, v___x_1040_);
lean_ctor_set(v___x_1041_, 5, v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9));
v___x_1044_ = l_Lean_stringToMessageData(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11));
v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15));
v___x_1053_ = l_Lean_stringToMessageData(v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17));
v___x_1056_ = l_Lean_stringToMessageData(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg(lean_object* v_ctx_1065_, uint8_t v_builtin_1066_, uint8_t v_force_1067_, lean_object* v_e_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_Meta_whnfCore(v_e_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v_p_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
switch(lean_obj_tag(v_a_1075_))
{
case 6:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___f_1093_; uint8_t v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; 
lean_dec_ref_known(v___x_1074_, 1);
v___x_1091_ = lean_box(v_builtin_1066_);
v___x_1092_ = lean_box(v_force_1067_);
v___f_1093_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1093_, 0, v_ctx_1065_);
lean_closure_set(v___f_1093_, 1, v___x_1091_);
lean_closure_set(v___f_1093_, 2, v___x_1092_);
v___x_1094_ = 0;
v___x_1095_ = 1;
v___x_1096_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_a_1075_, v___f_1093_, v___x_1094_, v___x_1094_, v___x_1095_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
return v___x_1096_;
}
case 8:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___f_1099_; uint8_t v___x_1100_; uint8_t v___x_1101_; lean_object* v___x_1102_; 
lean_dec_ref_known(v___x_1074_, 1);
v___x_1097_ = lean_box(v_builtin_1066_);
v___x_1098_ = lean_box(v_force_1067_);
v___f_1099_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1099_, 0, v_ctx_1065_);
lean_closure_set(v___f_1099_, 1, v___x_1097_);
lean_closure_set(v___f_1099_, 2, v___x_1098_);
v___x_1100_ = 0;
v___x_1101_ = 1;
v___x_1102_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_a_1075_, v___f_1099_, v___x_1100_, v___x_1100_, v___x_1101_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
return v___x_1102_;
}
case 1:
{
lean_dec_ref_known(v_a_1075_, 1);
lean_dec_ref(v_ctx_1065_);
return v___x_1074_;
}
default: 
{
lean_object* v___x_1103_; 
lean_dec_ref_known(v___x_1074_, 1);
v___x_1103_ = l_Lean_Expr_getAppFn(v_a_1075_);
if (lean_obj_tag(v___x_1103_) == 4)
{
lean_object* v_declName_1104_; lean_object* v___x_1105_; lean_object* v_env_1106_; lean_object* v_varName_1107_; lean_object* v_categoryAttr_1108_; lean_object* v_combinatorAttr_1109_; lean_object* v___x_1110_; 
v_declName_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_declName_1104_);
lean_dec_ref_known(v___x_1103_, 2);
v___x_1105_ = lean_st_ref_get(v_a_1072_);
v_env_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc_ref_n(v_env_1106_, 2);
lean_dec(v___x_1105_);
v_varName_1107_ = lean_ctor_get(v_ctx_1065_, 0);
v_categoryAttr_1108_ = lean_ctor_get(v_ctx_1065_, 1);
v_combinatorAttr_1109_ = lean_ctor_get(v_ctx_1065_, 2);
v___x_1110_ = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(v_combinatorAttr_1109_, v_env_1106_, v_declName_1104_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_inc(v_varName_1107_);
lean_inc_n(v_declName_1104_, 2);
v___x_1111_ = l_Lean_Name_append(v_declName_1104_, v_varName_1107_);
v___x_1112_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(v_declName_1104_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___f_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v___f_1114_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0));
v___x_1115_ = l_Lean_ConstantInfo_type(v_a_1113_);
v___x_1116_ = 0;
lean_inc_ref(v___x_1115_);
v___x_1117_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v___x_1115_, v___f_1114_, v___x_1116_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___f_1119_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; uint8_t v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; uint8_t v___y_1242_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
lean_inc_ref(v_ctx_1065_);
v___f_1119_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_1119_, 0, v_ctx_1065_);
v___x_1292_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20));
v___x_1293_ = l_Lean_Expr_isConstOf(v_a_1118_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = ((lean_object*)(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2));
v___x_1295_ = l_Lean_Expr_isConstOf(v_a_1118_, v___x_1294_);
lean_dec(v_a_1118_);
v___y_1242_ = v___x_1295_;
goto v___jp_1241_;
}
else
{
lean_dec(v_a_1118_);
v___y_1242_ = v___x_1293_;
goto v___jp_1241_;
}
v___jp_1120_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1127_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2));
lean_inc(v___y_1126_);
v___x_1128_ = l_Lean_mkIdent(v___y_1126_);
v___x_1129_ = l_Lean_mkIdent(v___y_1121_);
v___x_1130_ = lean_unsigned_to_nat(1u);
v___x_1131_ = lean_mk_empty_array_with_capacity(v___x_1130_);
v___x_1132_ = lean_array_push(v___x_1131_, v___x_1129_);
v___x_1133_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__4));
v___x_1134_ = lean_box(2);
v___x_1135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v___x_1133_);
lean_ctor_set(v___x_1135_, 2, v___x_1132_);
v___x_1136_ = lean_unsigned_to_nat(2u);
v___x_1137_ = lean_mk_empty_array_with_capacity(v___x_1136_);
v___x_1138_ = lean_array_push(v___x_1137_, v___x_1128_);
v___x_1139_ = lean_array_push(v___x_1138_, v___x_1135_);
v___x_1140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1134_);
lean_ctor_set(v___x_1140_, 1, v___x_1127_);
lean_ctor_set(v___x_1140_, 2, v___x_1139_);
v___x_1141_ = 0;
lean_inc(v___x_1111_);
v___x_1142_ = l_Lean_Attribute_add(v___x_1111_, v___y_1126_, v___x_1140_, v___x_1141_, v___y_1125_, v___y_1123_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_dec_ref_known(v___x_1142_, 1);
v_p_1077_ = v___x_1111_;
v___y_1078_ = v___y_1124_;
v___y_1079_ = v___y_1122_;
v___y_1080_ = v___y_1125_;
v___y_1081_ = v___y_1123_;
goto v___jp_1076_;
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v___x_1111_);
lean_dec(v_a_1075_);
lean_dec_ref(v_ctx_1065_);
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
v___jp_1151_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_inc_ref_n(v_ctx_1065_, 2);
v___x_1158_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_1065_, v___y_1153_);
lean_dec_ref(v___y_1153_);
v___x_1159_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1065_, v_builtin_1066_, v_force_1067_, v___x_1158_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1161_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1159_, 1);
lean_inc_ref(v___x_1115_);
v___x_1161_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v___x_1115_, v___f_1119_, v___x_1116_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1240_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1240_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1240_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v_env_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1166_ = lean_st_ref_get(v___y_1157_);
v_env_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc_ref(v_env_1167_);
lean_dec(v___x_1166_);
v___x_1168_ = lean_box(0);
lean_inc_n(v___x_1111_, 2);
v___x_1169_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1111_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
lean_ctor_set(v___x_1169_, 2, v_a_1162_);
v___x_1170_ = lean_box(0);
v___x_1171_ = 1;
v___x_1172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1111_);
lean_ctor_set(v___x_1172_, 1, v___x_1168_);
v___x_1173_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1173_, 0, v___x_1169_);
lean_ctor_set(v___x_1173_, 1, v_a_1160_);
lean_ctor_set(v___x_1173_, 2, v___x_1170_);
lean_ctor_set(v___x_1173_, 3, v___x_1172_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*4, v___x_1171_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 1);
lean_ctor_set(v___x_1164_, 0, v___x_1173_);
v___x_1175_ = v___x_1164_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
uint8_t v___x_1176_; lean_object* v___x_1177_; 
lean_inc(v_declName_1104_);
v___x_1176_ = l_Lean_isMarkedMeta(v_env_1167_, v_declName_1104_);
v___x_1177_ = l_Lean_addAndCompile(v___x_1175_, v___y_1152_, v___x_1176_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v___x_1178_; lean_object* v_env_1179_; lean_object* v_nextMacroScope_1180_; lean_object* v_ngen_1181_; lean_object* v_auxDeclNGen_1182_; lean_object* v_traceState_1183_; lean_object* v_messages_1184_; lean_object* v_infoState_1185_; lean_object* v_snapshotTasks_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1229_; 
lean_dec_ref_known(v___x_1177_, 1);
v___x_1178_ = lean_st_ref_take(v___y_1157_);
v_env_1179_ = lean_ctor_get(v___x_1178_, 0);
v_nextMacroScope_1180_ = lean_ctor_get(v___x_1178_, 1);
v_ngen_1181_ = lean_ctor_get(v___x_1178_, 2);
v_auxDeclNGen_1182_ = lean_ctor_get(v___x_1178_, 3);
v_traceState_1183_ = lean_ctor_get(v___x_1178_, 4);
v_messages_1184_ = lean_ctor_get(v___x_1178_, 6);
v_infoState_1185_ = lean_ctor_get(v___x_1178_, 7);
v_snapshotTasks_1186_ = lean_ctor_get(v___x_1178_, 8);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v___x_1178_, 5);
lean_dec(v_unused_1230_);
v___x_1188_ = v___x_1178_;
v_isShared_1189_ = v_isSharedCheck_1229_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_snapshotTasks_1186_);
lean_inc(v_infoState_1185_);
lean_inc(v_messages_1184_);
lean_inc(v_traceState_1183_);
lean_inc(v_auxDeclNGen_1182_);
lean_inc(v_ngen_1181_);
lean_inc(v_nextMacroScope_1180_);
lean_inc(v_env_1179_);
lean_dec(v___x_1178_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1229_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
lean_inc(v___x_1111_);
lean_inc_ref(v_combinatorAttr_1109_);
v___x_1190_ = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(v_combinatorAttr_1109_, v_env_1179_, v_declName_1104_, v___x_1111_);
v___x_1191_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 5, v___x_1191_);
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1193_ = v___x_1188_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_nextMacroScope_1180_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_ngen_1181_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_auxDeclNGen_1182_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_traceState_1183_);
lean_ctor_set(v_reuseFailAlloc_1228_, 5, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1228_, 6, v_messages_1184_);
lean_ctor_set(v_reuseFailAlloc_1228_, 7, v_infoState_1185_);
lean_ctor_set(v_reuseFailAlloc_1228_, 8, v_snapshotTasks_1186_);
v___x_1193_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v_mctx_1196_; lean_object* v_zetaDeltaFVarIds_1197_; lean_object* v_postponed_1198_; lean_object* v_diag_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1226_; 
v___x_1194_ = lean_st_ref_set(v___y_1157_, v___x_1193_);
v___x_1195_ = lean_st_ref_take(v___y_1155_);
v_mctx_1196_ = lean_ctor_get(v___x_1195_, 0);
v_zetaDeltaFVarIds_1197_ = lean_ctor_get(v___x_1195_, 2);
v_postponed_1198_ = lean_ctor_get(v___x_1195_, 3);
v_diag_1199_ = lean_ctor_get(v___x_1195_, 4);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v___x_1195_, 1);
lean_dec(v_unused_1227_);
v___x_1201_ = v___x_1195_;
v_isShared_1202_ = v_isSharedCheck_1226_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_diag_1199_);
lean_inc(v_postponed_1198_);
lean_inc(v_zetaDeltaFVarIds_1197_);
lean_inc(v_mctx_1196_);
lean_dec(v___x_1195_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1226_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v___x_1203_);
v___x_1205_ = v___x_1201_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_mctx_1196_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_zetaDeltaFVarIds_1197_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_postponed_1198_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_diag_1199_);
v___x_1205_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = lean_st_ref_set(v___y_1155_, v___x_1205_);
v___x_1207_ = l_Lean_Expr_isConst(v___x_1115_);
lean_dec_ref(v___x_1115_);
if (v___x_1207_ == 0)
{
lean_dec(v_a_1113_);
v_p_1077_ = v___x_1111_;
v___y_1078_ = v___y_1154_;
v___y_1079_ = v___y_1155_;
v___y_1080_ = v___y_1156_;
v___y_1081_ = v___y_1157_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = l_Lean_ConstantInfo_value_x21(v_a_1113_, v___x_1116_);
lean_dec(v_a_1113_);
v___x_1209_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v___x_1208_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
if (lean_obj_tag(v_a_1210_) == 1)
{
if (v_builtin_1066_ == 0)
{
lean_object* v_defn_1211_; lean_object* v_val_1212_; lean_object* v_name_1213_; 
v_defn_1211_ = lean_ctor_get(v_categoryAttr_1108_, 0);
v_val_1212_ = lean_ctor_get(v_a_1210_, 0);
lean_inc(v_val_1212_);
lean_dec_ref_known(v_a_1210_, 1);
v_name_1213_ = lean_ctor_get(v_defn_1211_, 1);
lean_inc(v_name_1213_);
v___y_1121_ = v_val_1212_;
v___y_1122_ = v___y_1155_;
v___y_1123_ = v___y_1157_;
v___y_1124_ = v___y_1154_;
v___y_1125_ = v___y_1156_;
v___y_1126_ = v_name_1213_;
goto v___jp_1120_;
}
else
{
lean_object* v_defn_1214_; lean_object* v_val_1215_; lean_object* v_builtinName_1216_; 
v_defn_1214_ = lean_ctor_get(v_categoryAttr_1108_, 0);
v_val_1215_ = lean_ctor_get(v_a_1210_, 0);
lean_inc(v_val_1215_);
lean_dec_ref_known(v_a_1210_, 1);
v_builtinName_1216_ = lean_ctor_get(v_defn_1214_, 0);
lean_inc(v_builtinName_1216_);
v___y_1121_ = v_val_1215_;
v___y_1122_ = v___y_1155_;
v___y_1123_ = v___y_1157_;
v___y_1124_ = v___y_1154_;
v___y_1125_ = v___y_1156_;
v___y_1126_ = v_builtinName_1216_;
goto v___jp_1120_;
}
}
else
{
lean_dec(v_a_1210_);
v_p_1077_ = v___x_1111_;
v___y_1078_ = v___y_1154_;
v___y_1079_ = v___y_1155_;
v___y_1080_ = v___y_1156_;
v___y_1081_ = v___y_1157_;
goto v___jp_1076_;
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v___x_1111_);
lean_dec(v_a_1075_);
lean_dec_ref(v_ctx_1065_);
v_a_1217_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1209_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1209_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
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
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec_ref(v___x_1115_);
lean_dec(v_a_1113_);
lean_dec(v___x_1111_);
lean_dec(v_declName_1104_);
lean_dec(v_a_1075_);
lean_dec_ref(v_ctx_1065_);
v_a_1231_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1177_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1177_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1160_);
lean_dec_ref(v___x_1115_);
lean_dec(v_a_1113_);
lean_dec(v___x_1111_);
lean_dec(v_declName_1104_);
lean_dec(v_a_1075_);
lean_dec_ref(v_ctx_1065_);
return v___x_1161_;
}
}
else
{
lean_dec_ref(v___f_1119_);
lean_dec_ref(v___x_1115_);
lean_dec(v_a_1113_);
lean_dec(v___x_1111_);
lean_dec(v_declName_1104_);
lean_dec(v_a_1075_);
lean_dec_ref(v_ctx_1065_);
return v___x_1159_;
}
}
v___jp_1241_:
{
if (v___y_1242_ == 0)
{
lean_object* v___x_1243_; 
lean_dec_ref(v___f_1119_);
lean_dec_ref(v___x_1115_);
lean_dec(v_a_1113_);
lean_dec(v___x_1111_);
lean_dec_ref(v_env_1106_);
lean_dec(v_declName_1104_);
lean_inc(v_a_1075_);
v___x_1243_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_1075_, v___x_1116_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1243_, 1);
if (lean_obj_tag(v_a_1244_) == 1)
{
lean_object* v_val_1245_; 
lean_dec(v_a_1075_);
v_val_1245_ = lean_ctor_get(v_a_1244_, 0);
lean_inc(v_val_1245_);
lean_dec_ref_known(v_a_1244_, 1);
v_e_1068_ = v_val_1245_;
goto _start;
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_inc(v_varName_1107_);
lean_dec(v_a_1244_);
lean_dec_ref(v_ctx_1065_);
v___x_1247_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10);
v___x_1248_ = l_Lean_MessageData_ofName(v_varName_1107_);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12);
v___x_1251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = l_Lean_MessageData_ofExpr(v_a_1075_);
v___x_1253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1253_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1255_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
return v___x_1256_;
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_a_1075_);
lean_dec_ref(v_ctx_1065_);
v_a_1257_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1243_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1243_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v___x_1265_; 
lean_inc(v_a_1113_);
v___x_1265_ = l_Lean_ConstantInfo_value_x3f(v_a_1113_, v___x_1116_);
if (lean_obj_tag(v___x_1265_) == 1)
{
lean_object* v_val_1266_; lean_object* v___x_1267_; 
v_val_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_val_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1106_, v_declName_1104_);
lean_dec_ref(v_env_1106_);
if (lean_obj_tag(v___x_1267_) == 0)
{
v___y_1152_ = v___y_1242_;
v___y_1153_ = v_val_1266_;
v___y_1154_ = v_a_1069_;
v___y_1155_ = v_a_1070_;
v___y_1156_ = v_a_1071_;
v___y_1157_ = v_a_1072_;
goto v___jp_1151_;
}
else
{
lean_dec_ref_known(v___x_1267_, 1);
if (v_force_1067_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1268_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14);
lean_inc(v_declName_1104_);
v___x_1269_ = l_Lean_MessageData_ofName(v_declName_1104_);
v___x_1270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16);
v___x_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1272_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_dec_ref_known(v___x_1273_, 1);
v___y_1152_ = v___y_1242_;
v___y_1153_ = v_val_1266_;
v___y_1154_ = v_a_1069_;
v___y_1155_ = v_a_1070_;
v___y_1156_ = v_a_1071_;
v___y_1157_ = v_a_1072_;
goto v___jp_1151_;
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec(v_val_1266_);
lean_dec_ref(v___f_1119_);
lean_dec_ref(v___x_1115_);
lean_dec(v_a_1113_);
lean_dec(v___x_1111_);
lean_dec(v_declName_1104_);
lean_dec(v_a_1075_);
lean_dec_ref(v_ctx_1065_);
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
v___y_1152_ = v___y_1242_;
v___y_1153_ = v_val_1266_;
v___y_1154_ = v_a_1069_;
v___y_1155_ = v_a_1070_;
v___y_1156_ = v_a_1071_;
v___y_1157_ = v_a_1072_;
goto v___jp_1151_;
}
}
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_inc(v_varName_1107_);
lean_dec(v___x_1265_);
lean_dec_ref(v___f_1119_);
lean_dec_ref(v___x_1115_);
lean_dec(v_a_1113_);
lean_dec(v___x_1111_);
lean_dec_ref(v_env_1106_);
lean_dec(v_declName_1104_);
lean_dec_ref(v_ctx_1065_);
v___x_1282_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10);
v___x_1283_ = l_Lean_MessageData_ofName(v_varName_1107_);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_MessageData_ofExpr(v_a_1075_);
v___x_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1286_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1290_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
return v___x_1291_;
}
}
}
}
else
{
lean_dec_ref(v___x_1115_);
lean_dec(v_a_1113_);
lean_dec(v___x_1111_);
lean_dec_ref(v_env_1106_);
lean_dec(v_declName_1104_);
lean_dec(v_a_1075_);
lean_dec_ref(v_ctx_1065_);
return v___x_1117_;
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v___x_1111_);
lean_dec_ref(v_env_1106_);
lean_dec(v_declName_1104_);
lean_dec(v_a_1075_);
lean_dec_ref(v_ctx_1065_);
v_a_1296_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1112_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1112_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
lean_object* v_val_1304_; 
lean_dec_ref(v_env_1106_);
lean_dec(v_declName_1104_);
v_val_1304_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v___x_1110_, 1);
v_p_1077_ = v_val_1304_;
v___y_1078_ = v_a_1069_;
v___y_1079_ = v_a_1070_;
v___y_1080_ = v_a_1071_;
v___y_1081_ = v_a_1072_;
goto v___jp_1076_;
}
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec_ref(v___x_1103_);
lean_dec_ref(v_ctx_1065_);
v___x_1305_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22);
v___x_1306_ = l_Lean_MessageData_ofExpr(v_a_1075_);
v___x_1307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1305_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1309_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
return v___x_1310_;
}
}
}
v___jp_1076_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_box(0);
v___x_1083_ = l_Lean_mkConst(v_p_1077_, v___x_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
lean_inc_ref(v___x_1083_);
v___x_1084_ = lean_infer_type(v___x_1083_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___f_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = lean_box(v_builtin_1066_);
v___x_1087_ = lean_box(v_force_1067_);
v___f_1088_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed), 12, 5);
lean_closure_set(v___f_1088_, 0, v_a_1075_);
lean_closure_set(v___f_1088_, 1, v_ctx_1065_);
lean_closure_set(v___f_1088_, 2, v___x_1086_);
lean_closure_set(v___f_1088_, 3, v___x_1087_);
lean_closure_set(v___f_1088_, 4, v___x_1083_);
v___x_1089_ = 0;
v___x_1090_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_1085_, v___f_1088_, v___x_1089_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
return v___x_1090_;
}
else
{
lean_dec_ref(v___x_1083_);
lean_dec(v_a_1075_);
lean_dec_ref(v_ctx_1065_);
return v___x_1084_;
}
}
}
else
{
lean_dec_ref(v_ctx_1065_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(lean_object* v_ctx_1311_, uint8_t v_builtin_1312_, uint8_t v_force_1313_, lean_object* v_x_1314_, lean_object* v_b_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1311_, v_builtin_1312_, v_force_1313_, v_b_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___boxed(lean_object* v_upperBound_1322_, lean_object* v_params_1323_, lean_object* v___x_1324_, lean_object* v_ctx_1325_, lean_object* v_builtin_1326_, lean_object* v_force_1327_, lean_object* v_a_1328_, lean_object* v_b_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
uint8_t v_builtin_boxed_1335_; uint8_t v_force_boxed_1336_; lean_object* v_res_1337_; 
v_builtin_boxed_1335_ = lean_unbox(v_builtin_1326_);
v_force_boxed_1336_ = lean_unbox(v_force_1327_);
v_res_1337_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v_upperBound_1322_, v_params_1323_, v___x_1324_, v_ctx_1325_, v_builtin_boxed_1335_, v_force_boxed_1336_, v_a_1328_, v_b_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_params_1323_);
lean_dec(v_upperBound_1322_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___boxed(lean_object* v_ctx_1338_, lean_object* v_builtin_1339_, lean_object* v_force_1340_, lean_object* v_e_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
uint8_t v_builtin_boxed_1347_; uint8_t v_force_boxed_1348_; lean_object* v_res_1349_; 
v_builtin_boxed_1347_ = lean_unbox(v_builtin_1339_);
v_force_boxed_1348_ = lean_unbox(v_force_1340_);
v_res_1349_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1338_, v_builtin_boxed_1347_, v_force_boxed_1348_, v_e_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr(lean_object* v_00_u03b1_1350_, lean_object* v_ctx_1351_, uint8_t v_builtin_1352_, uint8_t v_force_1353_, lean_object* v_e_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1351_, v_builtin_1352_, v_force_1353_, v_e_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___boxed(lean_object* v_00_u03b1_1361_, lean_object* v_ctx_1362_, lean_object* v_builtin_1363_, lean_object* v_force_1364_, lean_object* v_e_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
uint8_t v_builtin_boxed_1371_; uint8_t v_force_boxed_1372_; lean_object* v_res_1373_; 
v_builtin_boxed_1371_ = lean_unbox(v_builtin_1363_);
v_force_boxed_1372_ = lean_unbox(v_force_1364_);
v_res_1373_ = l_Lean_ParserCompiler_compileParserExpr(v_00_u03b1_1361_, v_ctx_1362_, v_builtin_boxed_1371_, v_force_boxed_1372_, v_e_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(lean_object* v_00_u03b1_1374_, lean_object* v_ctx_1375_, lean_object* v_as_1376_, size_t v_i_1377_, size_t v_stop_1378_, lean_object* v_b_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_1375_, v_as_1376_, v_i_1377_, v_stop_1378_, v_b_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___boxed(lean_object* v_00_u03b1_1386_, lean_object* v_ctx_1387_, lean_object* v_as_1388_, lean_object* v_i_1389_, lean_object* v_stop_1390_, lean_object* v_b_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
size_t v_i_boxed_1397_; size_t v_stop_boxed_1398_; lean_object* v_res_1399_; 
v_i_boxed_1397_ = lean_unbox_usize(v_i_1389_);
lean_dec(v_i_1389_);
v_stop_boxed_1398_ = lean_unbox_usize(v_stop_1390_);
lean_dec(v_stop_1390_);
v_res_1399_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(v_00_u03b1_1386_, v_ctx_1387_, v_as_1388_, v_i_boxed_1397_, v_stop_boxed_1398_, v_b_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec_ref(v_as_1388_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(lean_object* v_upperBound_1400_, lean_object* v_params_1401_, lean_object* v___x_1402_, lean_object* v_00_u03b1_1403_, lean_object* v_ctx_1404_, uint8_t v_builtin_1405_, uint8_t v_force_1406_, lean_object* v_inst_1407_, lean_object* v_R_1408_, lean_object* v_a_1409_, lean_object* v_b_1410_, lean_object* v_c_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v_upperBound_1400_, v_params_1401_, v___x_1402_, v_ctx_1404_, v_builtin_1405_, v_force_1406_, v_a_1409_, v_b_1410_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1418_ = _args[0];
lean_object* v_params_1419_ = _args[1];
lean_object* v___x_1420_ = _args[2];
lean_object* v_00_u03b1_1421_ = _args[3];
lean_object* v_ctx_1422_ = _args[4];
lean_object* v_builtin_1423_ = _args[5];
lean_object* v_force_1424_ = _args[6];
lean_object* v_inst_1425_ = _args[7];
lean_object* v_R_1426_ = _args[8];
lean_object* v_a_1427_ = _args[9];
lean_object* v_b_1428_ = _args[10];
lean_object* v_c_1429_ = _args[11];
lean_object* v___y_1430_ = _args[12];
lean_object* v___y_1431_ = _args[13];
lean_object* v___y_1432_ = _args[14];
lean_object* v___y_1433_ = _args[15];
lean_object* v___y_1434_ = _args[16];
_start:
{
uint8_t v_builtin_boxed_1435_; uint8_t v_force_boxed_1436_; lean_object* v_res_1437_; 
v_builtin_boxed_1435_ = lean_unbox(v_builtin_1423_);
v_force_boxed_1436_ = lean_unbox(v_force_1424_);
v_res_1437_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(v_upperBound_1418_, v_params_1419_, v___x_1420_, v_00_u03b1_1421_, v_ctx_1422_, v_builtin_boxed_1435_, v_force_boxed_1436_, v_inst_1425_, v_R_1426_, v_a_1427_, v_b_1428_, v_c_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec_ref(v___x_1420_);
lean_dec_ref(v_params_1419_);
lean_dec(v_upperBound_1418_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4(lean_object* v_00_u03b1_1438_, lean_object* v_msg_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v_msg_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___boxed(lean_object* v_00_u03b1_1446_, lean_object* v_msg_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4(v_00_u03b1_1446_, v_msg_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(lean_object* v_00_u03b1_1454_, lean_object* v_constName_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1462_, lean_object* v_constName_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(v_00_u03b1_1462_, v_constName_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_1470_, lean_object* v_ref_1471_, lean_object* v_constName_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_1471_, v_constName_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1479_, lean_object* v_ref_1480_, lean_object* v_constName_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(v_00_u03b1_1479_, v_ref_1480_, v_constName_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v_ref_1480_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_1488_, lean_object* v_ref_1489_, lean_object* v_msg_1490_, lean_object* v_declHint_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_1489_, v_msg_1490_, v_declHint_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1498_, lean_object* v_ref_1499_, lean_object* v_msg_1500_, lean_object* v_declHint_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7(v_00_u03b1_1498_, v_ref_1499_, v_msg_1500_, v_declHint_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v_ref_1499_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_1508_, lean_object* v_declHint_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1508_, v_declHint_1509_, v___y_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1516_, lean_object* v_declHint_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_1516_, v_declHint_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1524_, lean_object* v_ref_1525_, lean_object* v_msg_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1525_, v_msg_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1533_, lean_object* v_ref_1534_, lean_object* v_msg_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_1533_, v_ref_1534_, v_msg_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v_ref_1534_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(lean_object* v_ctx_1542_, uint8_t v_builtin_1543_, lean_object* v_x_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_p_1551_; lean_object* v_psep_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; 
switch(lean_obj_tag(v_x_1544_))
{
case 1:
{
lean_object* v_p_1559_; 
v_p_1559_ = lean_ctor_get(v_x_1544_, 1);
lean_inc_ref(v_p_1559_);
lean_dec_ref_known(v_x_1544_, 2);
v_x_1544_ = v_p_1559_;
goto _start;
}
case 2:
{
lean_object* v_p_u2081_1561_; lean_object* v_p_u2082_1562_; lean_object* v___x_1563_; 
v_p_u2081_1561_ = lean_ctor_get(v_x_1544_, 1);
lean_inc_ref(v_p_u2081_1561_);
v_p_u2082_1562_ = lean_ctor_get(v_x_1544_, 2);
lean_inc_ref(v_p_u2082_1562_);
lean_dec_ref_known(v_x_1544_, 3);
lean_inc_ref(v_ctx_1542_);
v___x_1563_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1542_, v_builtin_1543_, v_p_u2081_1561_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_dec_ref_known(v___x_1563_, 1);
v_x_1544_ = v_p_u2082_1562_;
goto _start;
}
else
{
lean_dec_ref(v_p_u2082_1562_);
lean_dec_ref(v_ctx_1542_);
return v___x_1563_;
}
}
case 3:
{
lean_object* v_p_1565_; 
v_p_1565_ = lean_ctor_get(v_x_1544_, 2);
lean_inc_ref(v_p_1565_);
lean_dec_ref_known(v_x_1544_, 3);
v_x_1544_ = v_p_1565_;
goto _start;
}
case 4:
{
lean_object* v_p_1567_; 
v_p_1567_ = lean_ctor_get(v_x_1544_, 3);
lean_inc_ref(v_p_1567_);
lean_dec_ref_known(v_x_1544_, 4);
v_x_1544_ = v_p_1567_;
goto _start;
}
case 8:
{
lean_object* v_declName_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_declName_1569_ = lean_ctor_get(v_x_1544_, 0);
lean_inc(v_declName_1569_);
lean_dec_ref_known(v_x_1544_, 1);
v___x_1570_ = 0;
v___x_1571_ = lean_box(0);
v___x_1572_ = l_Lean_mkConst(v_declName_1569_, v___x_1571_);
v___x_1573_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1542_, v_builtin_1543_, v___x_1570_, v___x_1572_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1581_; 
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; 
v_unused_1582_ = lean_ctor_get(v___x_1573_, 0);
lean_dec(v_unused_1582_);
v___x_1575_ = v___x_1573_;
v_isShared_1576_ = v_isSharedCheck_1581_;
goto v_resetjp_1574_;
}
else
{
lean_dec(v___x_1573_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1581_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_box(0);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1577_);
v___x_1579_ = v___x_1575_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
v_a_1583_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1573_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1573_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
case 9:
{
lean_object* v_p_1591_; 
v_p_1591_ = lean_ctor_get(v_x_1544_, 2);
lean_inc_ref(v_p_1591_);
lean_dec_ref_known(v_x_1544_, 3);
v_x_1544_ = v_p_1591_;
goto _start;
}
case 10:
{
lean_object* v_p_1593_; lean_object* v_psep_1594_; 
v_p_1593_ = lean_ctor_get(v_x_1544_, 0);
lean_inc_ref(v_p_1593_);
v_psep_1594_ = lean_ctor_get(v_x_1544_, 2);
lean_inc_ref(v_psep_1594_);
lean_dec_ref_known(v_x_1544_, 3);
v_p_1551_ = v_p_1593_;
v_psep_1552_ = v_psep_1594_;
v___y_1553_ = v_a_1545_;
v___y_1554_ = v_a_1546_;
v___y_1555_ = v_a_1547_;
v___y_1556_ = v_a_1548_;
goto v___jp_1550_;
}
case 11:
{
lean_object* v_p_1595_; lean_object* v_psep_1596_; 
v_p_1595_ = lean_ctor_get(v_x_1544_, 0);
lean_inc_ref(v_p_1595_);
v_psep_1596_ = lean_ctor_get(v_x_1544_, 2);
lean_inc_ref(v_psep_1596_);
lean_dec_ref_known(v_x_1544_, 3);
v_p_1551_ = v_p_1595_;
v_psep_1552_ = v_psep_1596_;
v___y_1553_ = v_a_1545_;
v___y_1554_ = v_a_1546_;
v___y_1555_ = v_a_1547_;
v___y_1556_ = v_a_1548_;
goto v___jp_1550_;
}
default: 
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec_ref(v_x_1544_);
lean_dec_ref(v_ctx_1542_);
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
return v___x_1598_;
}
}
v___jp_1550_:
{
lean_object* v___x_1557_; 
lean_inc_ref(v_ctx_1542_);
v___x_1557_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1542_, v_builtin_1543_, v_p_1551_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_dec_ref_known(v___x_1557_, 1);
v_x_1544_ = v_psep_1552_;
v_a_1545_ = v___y_1553_;
v_a_1546_ = v___y_1554_;
v_a_1547_ = v___y_1555_;
v_a_1548_ = v___y_1556_;
goto _start;
}
else
{
lean_dec_ref(v_psep_1552_);
lean_dec_ref(v_ctx_1542_);
return v___x_1557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg___boxed(lean_object* v_ctx_1599_, lean_object* v_builtin_1600_, lean_object* v_x_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
uint8_t v_builtin_boxed_1607_; lean_object* v_res_1608_; 
v_builtin_boxed_1607_ = lean_unbox(v_builtin_1600_);
v_res_1608_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1599_, v_builtin_boxed_1607_, v_x_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers(lean_object* v_00_u03b1_1609_, lean_object* v_ctx_1610_, uint8_t v_builtin_1611_, lean_object* v_x_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1610_, v_builtin_1611_, v_x_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___boxed(lean_object* v_00_u03b1_1619_, lean_object* v_ctx_1620_, lean_object* v_builtin_1621_, lean_object* v_x_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
uint8_t v_builtin_boxed_1628_; lean_object* v_res_1629_; 
v_builtin_boxed_1628_ = lean_unbox(v_builtin_1621_);
v_res_1629_ = l_Lean_ParserCompiler_compileEmbeddedParsers(v_00_u03b1_1619_, v_ctx_1620_, v_builtin_boxed_1628_, v_x_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
return v_res_1629_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = lean_box(0);
v___x_1631_ = l_Lean_Elab_abortCommandExceptionId;
v___x_1632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v___x_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg(){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0);
v___x_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___boxed(lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(lean_object* v_msgData_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; lean_object* v_env_1643_; lean_object* v_options_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1642_ = lean_st_ref_get(v___y_1640_);
v_env_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc_ref(v_env_1643_);
lean_dec(v___x_1642_);
v_options_1644_ = lean_ctor_get(v___y_1639_, 2);
v___x_1645_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1646_ = lean_unsigned_to_nat(32u);
v___x_1647_ = lean_mk_empty_array_with_capacity(v___x_1646_);
lean_dec_ref(v___x_1647_);
v___x_1648_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
lean_inc_ref(v_options_1644_);
v___x_1649_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1649_, 0, v_env_1643_);
lean_ctor_set(v___x_1649_, 1, v___x_1645_);
lean_ctor_set(v___x_1649_, 2, v___x_1648_);
lean_ctor_set(v___x_1649_, 3, v_options_1644_);
v___x_1650_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
lean_ctor_set(v___x_1650_, 1, v_msgData_1638_);
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9___boxed(lean_object* v_msgData_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(v_msgData_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(lean_object* v_msg_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_ref_1661_; lean_object* v___x_1662_; lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1671_; 
v_ref_1661_ = lean_ctor_get(v___y_1658_, 5);
v___x_1662_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(v_msg_1657_, v___y_1658_, v___y_1659_);
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1671_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1671_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_inc(v_ref_1661_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_ref_1661_);
lean_ctor_set(v___x_1667_, 1, v_a_1663_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set_tag(v___x_1665_, 1);
lean_ctor_set(v___x_1665_, 0, v___x_1667_);
v___x_1669_ = v___x_1665_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msg_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
if (lean_obj_tag(v_x_1677_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_a_1681_ = lean_ctor_get(v_x_1677_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v_x_1677_, 1);
v___x_1682_ = l_Lean_stringToMessageData(v_a_1681_);
v___x_1683_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v___x_1682_, v___y_1678_, v___y_1679_);
return v___x_1683_;
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
v_a_1684_ = lean_ctor_get(v_x_1677_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_x_1677_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v_x_1677_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v_x_1677_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 0);
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg___boxed(lean_object* v_x_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v_x_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(lean_object* v_typeName_1697_, lean_object* v_constName_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v_env_1703_; uint8_t v___x_1704_; 
v___x_1702_ = lean_st_ref_get(v___y_1700_);
v_env_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc_ref(v_env_1703_);
lean_dec(v___x_1702_);
lean_inc(v_constName_1698_);
v___x_1704_ = lean_has_compile_error(v_env_1703_, v_constName_1698_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; lean_object* v_env_1706_; lean_object* v_options_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1705_ = lean_st_ref_get(v___y_1700_);
v_env_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc_ref(v_env_1706_);
lean_dec(v___x_1705_);
v_options_1707_ = lean_ctor_get(v___y_1699_, 2);
v___x_1708_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1706_, v_options_1707_, v_typeName_1697_, v_constName_1698_);
v___x_1709_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v___x_1708_, v___y_1699_, v___y_1700_);
return v___x_1709_;
}
else
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v___x_1711_; lean_object* v_env_1712_; lean_object* v_options_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec_ref_known(v___x_1710_, 1);
v___x_1711_ = lean_st_ref_get(v___y_1700_);
v_env_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc_ref(v_env_1712_);
lean_dec(v___x_1711_);
v_options_1713_ = lean_ctor_get(v___y_1699_, 2);
v___x_1714_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1712_, v_options_1713_, v_typeName_1697_, v_constName_1698_);
v___x_1715_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v___x_1714_, v___y_1699_, v___y_1700_);
return v___x_1715_;
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_constName_1698_);
lean_dec(v_typeName_1697_);
v_a_1716_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1710_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1710_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg___boxed(lean_object* v_typeName_1724_, lean_object* v_constName_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v_typeName_1724_, v_constName_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(lean_object* v_ref_1730_, lean_object* v_msg_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_fileName_1735_; lean_object* v_fileMap_1736_; lean_object* v_options_1737_; lean_object* v_currRecDepth_1738_; lean_object* v_maxRecDepth_1739_; lean_object* v_ref_1740_; lean_object* v_currNamespace_1741_; lean_object* v_openDecls_1742_; lean_object* v_initHeartbeats_1743_; lean_object* v_maxHeartbeats_1744_; lean_object* v_quotContext_1745_; lean_object* v_currMacroScope_1746_; uint8_t v_diag_1747_; lean_object* v_cancelTk_x3f_1748_; uint8_t v_suppressElabErrors_1749_; lean_object* v_inheritedTraceOptions_1750_; lean_object* v_ref_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_fileName_1735_ = lean_ctor_get(v___y_1732_, 0);
v_fileMap_1736_ = lean_ctor_get(v___y_1732_, 1);
v_options_1737_ = lean_ctor_get(v___y_1732_, 2);
v_currRecDepth_1738_ = lean_ctor_get(v___y_1732_, 3);
v_maxRecDepth_1739_ = lean_ctor_get(v___y_1732_, 4);
v_ref_1740_ = lean_ctor_get(v___y_1732_, 5);
v_currNamespace_1741_ = lean_ctor_get(v___y_1732_, 6);
v_openDecls_1742_ = lean_ctor_get(v___y_1732_, 7);
v_initHeartbeats_1743_ = lean_ctor_get(v___y_1732_, 8);
v_maxHeartbeats_1744_ = lean_ctor_get(v___y_1732_, 9);
v_quotContext_1745_ = lean_ctor_get(v___y_1732_, 10);
v_currMacroScope_1746_ = lean_ctor_get(v___y_1732_, 11);
v_diag_1747_ = lean_ctor_get_uint8(v___y_1732_, sizeof(void*)*14);
v_cancelTk_x3f_1748_ = lean_ctor_get(v___y_1732_, 12);
v_suppressElabErrors_1749_ = lean_ctor_get_uint8(v___y_1732_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1750_ = lean_ctor_get(v___y_1732_, 13);
v_ref_1751_ = l_Lean_replaceRef(v_ref_1730_, v_ref_1740_);
lean_inc_ref(v_inheritedTraceOptions_1750_);
lean_inc(v_cancelTk_x3f_1748_);
lean_inc(v_currMacroScope_1746_);
lean_inc(v_quotContext_1745_);
lean_inc(v_maxHeartbeats_1744_);
lean_inc(v_initHeartbeats_1743_);
lean_inc(v_openDecls_1742_);
lean_inc(v_currNamespace_1741_);
lean_inc(v_maxRecDepth_1739_);
lean_inc(v_currRecDepth_1738_);
lean_inc_ref(v_options_1737_);
lean_inc_ref(v_fileMap_1736_);
lean_inc_ref(v_fileName_1735_);
v___x_1752_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1752_, 0, v_fileName_1735_);
lean_ctor_set(v___x_1752_, 1, v_fileMap_1736_);
lean_ctor_set(v___x_1752_, 2, v_options_1737_);
lean_ctor_set(v___x_1752_, 3, v_currRecDepth_1738_);
lean_ctor_set(v___x_1752_, 4, v_maxRecDepth_1739_);
lean_ctor_set(v___x_1752_, 5, v_ref_1751_);
lean_ctor_set(v___x_1752_, 6, v_currNamespace_1741_);
lean_ctor_set(v___x_1752_, 7, v_openDecls_1742_);
lean_ctor_set(v___x_1752_, 8, v_initHeartbeats_1743_);
lean_ctor_set(v___x_1752_, 9, v_maxHeartbeats_1744_);
lean_ctor_set(v___x_1752_, 10, v_quotContext_1745_);
lean_ctor_set(v___x_1752_, 11, v_currMacroScope_1746_);
lean_ctor_set(v___x_1752_, 12, v_cancelTk_x3f_1748_);
lean_ctor_set(v___x_1752_, 13, v_inheritedTraceOptions_1750_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*14, v_diag_1747_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*14 + 1, v_suppressElabErrors_1749_);
v___x_1753_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_1731_, v___x_1752_, v___y_1733_);
lean_dec_ref_known(v___x_1752_, 14);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg___boxed(lean_object* v_ref_1754_, lean_object* v_msg_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_1754_, v_msg_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v_ref_1754_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(lean_object* v_msg_1760_, lean_object* v_declHint_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___x_1764_; lean_object* v_env_1765_; uint8_t v___y_1767_; uint8_t v___x_1825_; uint8_t v___x_1826_; 
v___x_1764_ = lean_st_ref_get(v___y_1762_);
v_env_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc_ref(v_env_1765_);
lean_dec(v___x_1764_);
v___x_1825_ = l_Lean_Name_isAnonymous(v_declHint_1761_);
v___x_1826_ = lean_bool_not(v___x_1825_);
if (v___x_1826_ == 0)
{
v___y_1767_ = v___x_1826_;
goto v___jp_1766_;
}
else
{
uint8_t v_isExporting_1827_; 
v_isExporting_1827_ = lean_ctor_get_uint8(v_env_1765_, sizeof(void*)*8);
v___y_1767_ = v_isExporting_1827_;
goto v___jp_1766_;
}
v___jp_1766_:
{
if (v___y_1767_ == 0)
{
lean_object* v___x_1768_; 
lean_dec_ref(v_env_1765_);
lean_dec(v_declHint_1761_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_msg_1760_);
return v___x_1768_;
}
else
{
uint8_t v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1769_ = 0;
lean_inc_ref(v_env_1765_);
v___x_1770_ = l_Lean_Environment_setExporting(v_env_1765_, v___x_1769_);
lean_inc(v_declHint_1761_);
lean_inc_ref(v___x_1770_);
v___x_1771_ = l_Lean_Environment_contains(v___x_1770_, v_declHint_1761_, v___y_1767_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_dec_ref(v___x_1770_);
lean_dec_ref(v_env_1765_);
lean_dec(v_declHint_1761_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v_msg_1760_);
return v___x_1772_;
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v_c_1780_; lean_object* v___x_1781_; 
v___x_1773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1774_ = lean_unsigned_to_nat(32u);
v___x_1775_ = lean_mk_empty_array_with_capacity(v___x_1774_);
lean_dec_ref(v___x_1775_);
v___x_1776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1777_ = l_Lean_Options_empty;
v___x_1778_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1770_);
lean_ctor_set(v___x_1778_, 1, v___x_1773_);
lean_ctor_set(v___x_1778_, 2, v___x_1776_);
lean_ctor_set(v___x_1778_, 3, v___x_1777_);
lean_inc(v_declHint_1761_);
v___x_1779_ = l_Lean_MessageData_ofConstName(v_declHint_1761_, v___x_1769_);
v_c_1780_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1780_, 0, v___x_1778_);
lean_ctor_set(v_c_1780_, 1, v___x_1779_);
v___x_1781_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1765_, v_declHint_1761_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_dec_ref(v_env_1765_);
lean_dec(v_declHint_1761_);
v___x_1782_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v_c_1780_);
v___x_1784_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1783_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = l_Lean_MessageData_note(v___x_1785_);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v_msg_1760_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
else
{
lean_object* v_val_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1824_; 
v_val_1789_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1791_ = v___x_1781_;
v_isShared_1792_ = v_isSharedCheck_1824_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_val_1789_);
lean_dec(v___x_1781_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1824_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v_mod_1796_; uint8_t v___x_1797_; 
v___x_1793_ = lean_box(0);
v___x_1794_ = l_Lean_Environment_header(v_env_1765_);
lean_dec_ref(v_env_1765_);
v___x_1795_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1794_);
v_mod_1796_ = lean_array_get(v___x_1793_, v___x_1795_, v_val_1789_);
lean_dec(v_val_1789_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = l_Lean_isPrivateName(v_declHint_1761_);
lean_dec(v_declHint_1761_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1798_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v_c_1780_);
v___x_1800_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1799_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = l_Lean_MessageData_ofName(v_mod_1796_);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1801_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1803_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = l_Lean_MessageData_note(v___x_1805_);
v___x_1807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1807_, 0, v_msg_1760_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set_tag(v___x_1791_, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1807_);
v___x_1809_ = v___x_1791_;
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
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
lean_ctor_set(v___x_1812_, 1, v_c_1780_);
v___x_1813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = l_Lean_MessageData_ofName(v_mod_1796_);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = l_Lean_MessageData_note(v___x_1818_);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v_msg_1760_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set_tag(v___x_1791_, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1820_);
v___x_1822_ = v___x_1791_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg___boxed(lean_object* v_msg_1828_, lean_object* v_declHint_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_1828_, v_declHint_1829_, v___y_1830_);
lean_dec(v___y_1830_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(lean_object* v_msg_1833_, lean_object* v_declHint_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___x_1838_; lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1848_; 
v___x_1838_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_1833_, v_declHint_1834_, v___y_1836_);
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1848_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1848_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1843_ = l_Lean_unknownIdentifierMessageTag;
v___x_1844_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v_a_1839_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1844_);
v___x_1846_ = v___x_1841_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8___boxed(lean_object* v_msg_1849_, lean_object* v_declHint_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_1849_, v_declHint_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_ref_1855_, lean_object* v_msg_1856_, lean_object* v_declHint_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; lean_object* v_a_1862_; lean_object* v___x_1863_; 
v___x_1861_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_1856_, v_declHint_1857_, v___y_1858_, v___y_1859_);
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref(v___x_1861_);
v___x_1863_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_1855_, v_a_1862_, v___y_1858_, v___y_1859_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_ref_1864_, lean_object* v_msg_1865_, lean_object* v_declHint_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1864_, v_msg_1865_, v_declHint_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v_ref_1864_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1871_, lean_object* v_constName_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1876_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_1877_ = 0;
lean_inc(v_constName_1872_);
v___x_1878_ = l_Lean_MessageData_ofConstName(v_constName_1872_, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1876_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1871_, v___x_1881_, v_constName_1872_, v___y_1873_, v___y_1874_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1883_, lean_object* v_constName_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_1883_, v_constName_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v_ref_1883_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(lean_object* v_constName_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_ref_1893_; lean_object* v___x_1894_; 
v_ref_1893_ = lean_ctor_get(v___y_1890_, 5);
v___x_1894_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_1893_, v_constName_1889_, v___y_1890_, v___y_1891_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(lean_object* v_constName_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; lean_object* v_env_1905_; uint8_t v___x_1906_; lean_object* v___x_1907_; 
v___x_1904_ = lean_st_ref_get(v___y_1902_);
v_env_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc_ref(v_env_1905_);
lean_dec(v___x_1904_);
v___x_1906_ = 0;
lean_inc(v_constName_1900_);
v___x_1907_ = l_Lean_Environment_find_x3f(v_env_1905_, v_constName_1900_, v___x_1906_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_1900_, v___y_1901_, v___y_1902_);
return v___x_1908_;
}
else
{
lean_object* v_val_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_constName_1900_);
v_val_1909_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1907_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_val_1909_);
lean_dec(v___x_1907_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 0);
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_val_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0___boxed(lean_object* v_constName_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(v_constName_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
return v_res_1921_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1922_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
return v___x_1924_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1925_ = lean_box(1);
v___x_1926_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1927_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1928_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_ctor_set(v___x_1928_, 1, v___x_1926_);
lean_ctor_set(v___x_1928_, 2, v___x_1925_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1932_ = lean_unsigned_to_nat(0u);
v___x_1933_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
lean_ctor_set(v___x_1933_, 2, v___x_1932_);
lean_ctor_set(v___x_1933_, 3, v___x_1932_);
lean_ctor_set(v___x_1933_, 4, v___x_1931_);
lean_ctor_set(v___x_1933_, 5, v___x_1931_);
lean_ctor_set(v___x_1933_, 6, v___x_1931_);
lean_ctor_set(v___x_1933_, 7, v___x_1931_);
lean_ctor_set(v___x_1933_, 8, v___x_1931_);
lean_ctor_set(v___x_1933_, 9, v___x_1931_);
return v___x_1933_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1935_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
lean_ctor_set(v___x_1935_, 2, v___x_1934_);
lean_ctor_set(v___x_1935_, 3, v___x_1934_);
lean_ctor_set(v___x_1935_, 4, v___x_1934_);
lean_ctor_set(v___x_1935_, 5, v___x_1934_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
lean_ctor_set(v___x_1937_, 2, v___x_1936_);
lean_ctor_set(v___x_1937_, 3, v___x_1936_);
lean_ctor_set(v___x_1937_, 4, v___x_1936_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1938_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6);
v___x_1939_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1940_ = lean_box(1);
v___x_1941_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5);
v___x_1942_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4);
v___x_1943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v___x_1941_);
lean_ctor_set(v___x_1943_, 2, v___x_1940_);
lean_ctor_set(v___x_1943_, 3, v___x_1939_);
lean_ctor_set(v___x_1943_, 4, v___x_1938_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(lean_object* v_constName_1952_, lean_object* v_ctx_1953_, uint8_t v_builtin_1954_, lean_object* v_catName_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
uint8_t v___y_1960_; uint8_t v___y_1961_; lean_object* v___y_1962_; lean_object* v___x_1997_; 
lean_inc(v_constName_1952_);
v___x_1997_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(v_constName_1952_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_1999_; uint8_t v___y_2001_; lean_object* v___y_2002_; uint8_t v___y_2003_; uint8_t v___y_2004_; lean_object* v___x_2007_; uint8_t v___y_2009_; uint8_t v___x_2059_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_1999_ = l_Lean_ConstantInfo_type(v_a_1998_);
lean_dec(v_a_1998_);
v___x_2007_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11));
v___x_2059_ = l_Lean_Expr_isConstOf(v___x_1999_, v___x_2007_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9));
v___x_2061_ = l_Lean_Expr_isConstOf(v___x_1999_, v___x_2060_);
lean_dec_ref(v___x_1999_);
v___y_2009_ = v___x_2061_;
goto v___jp_2008_;
}
else
{
lean_dec_ref(v___x_1999_);
v___y_2009_ = v___x_2059_;
goto v___jp_2008_;
}
v___jp_2000_:
{
if (v___y_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec_ref(v___y_2002_);
v___x_2005_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9));
v___x_2006_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v___x_2005_, v_constName_1952_, v___y_1956_, v___y_1957_);
v___y_1960_ = v___y_2001_;
v___y_1961_ = v___y_2003_;
v___y_1962_ = v___x_2006_;
goto v___jp_1959_;
}
else
{
lean_dec(v_constName_1952_);
v___y_1960_ = v___y_2001_;
v___y_1961_ = v___y_2003_;
v___y_1962_ = v___y_2002_;
goto v___jp_1959_;
}
}
v___jp_2008_:
{
uint8_t v___x_2010_; 
v___x_2010_ = 1;
if (v___y_2009_ == 0)
{
uint8_t v___x_2011_; uint8_t v___x_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; uint64_t v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2011_ = 1;
v___x_2012_ = 0;
v___x_2013_ = 2;
v___x_2014_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2014_, 0, v___y_2009_);
lean_ctor_set_uint8(v___x_2014_, 1, v___y_2009_);
lean_ctor_set_uint8(v___x_2014_, 2, v___y_2009_);
lean_ctor_set_uint8(v___x_2014_, 3, v___y_2009_);
lean_ctor_set_uint8(v___x_2014_, 4, v___y_2009_);
lean_ctor_set_uint8(v___x_2014_, 5, v___x_2010_);
lean_ctor_set_uint8(v___x_2014_, 6, v___x_2010_);
lean_ctor_set_uint8(v___x_2014_, 7, v___y_2009_);
lean_ctor_set_uint8(v___x_2014_, 8, v___x_2010_);
lean_ctor_set_uint8(v___x_2014_, 9, v___x_2011_);
lean_ctor_set_uint8(v___x_2014_, 10, v___x_2012_);
lean_ctor_set_uint8(v___x_2014_, 11, v___x_2010_);
lean_ctor_set_uint8(v___x_2014_, 12, v___x_2010_);
lean_ctor_set_uint8(v___x_2014_, 13, v___x_2010_);
lean_ctor_set_uint8(v___x_2014_, 14, v___x_2013_);
lean_ctor_set_uint8(v___x_2014_, 15, v___x_2010_);
lean_ctor_set_uint8(v___x_2014_, 16, v___x_2010_);
lean_ctor_set_uint8(v___x_2014_, 17, v___x_2010_);
lean_ctor_set_uint8(v___x_2014_, 18, v___x_2010_);
v___x_2015_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2014_);
v___x_2016_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set_uint64(v___x_2016_, sizeof(void*)*1, v___x_2015_);
v___x_2017_ = lean_box(1);
v___x_2018_ = lean_unsigned_to_nat(0u);
v___x_2019_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2);
v___x_2020_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3));
v___x_2021_ = lean_box(0);
v___x_2022_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2022_, 0, v___x_2016_);
lean_ctor_set(v___x_2022_, 1, v___x_2017_);
lean_ctor_set(v___x_2022_, 2, v___x_2019_);
lean_ctor_set(v___x_2022_, 3, v___x_2020_);
lean_ctor_set(v___x_2022_, 4, v___x_2021_);
lean_ctor_set(v___x_2022_, 5, v___x_2018_);
lean_ctor_set(v___x_2022_, 6, v___x_2021_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*7, v___y_2009_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*7 + 1, v___y_2009_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*7 + 2, v___y_2009_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*7 + 3, v___x_2010_);
v___x_2023_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7);
v___x_2024_ = lean_st_mk_ref(v___x_2023_);
v___x_2025_ = l_Lean_Name_isAnonymous(v_catName_1955_);
v___x_2026_ = lean_box(0);
v___x_2027_ = l_Lean_mkConst(v_constName_1952_, v___x_2026_);
v___x_2028_ = lean_box(0);
v___x_2029_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1953_, v_builtin_1954_, v___x_2025_, v___x_2027_, v___x_2022_, v___x_2024_, v___y_1956_, v___y_1957_);
lean_dec_ref_known(v___x_2022_, 7);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2037_; 
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v___x_2029_, 0);
lean_dec(v_unused_2038_);
v___x_2031_ = v___x_2029_;
v_isShared_2032_ = v_isSharedCheck_2037_;
goto v_resetjp_2030_;
}
else
{
lean_dec(v___x_2029_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2037_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2033_ = lean_st_ref_get(v___x_2024_);
lean_dec(v___x_2024_);
lean_dec(v___x_2033_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2028_);
v___x_2035_ = v___x_2031_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2028_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
else
{
lean_dec(v___x_2024_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v___x_2029_, 0);
lean_dec(v_unused_2046_);
v___x_2040_ = v___x_2029_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_dec(v___x_2029_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2028_);
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2028_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
v_a_2047_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2029_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2029_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
else
{
lean_object* v___x_2055_; 
lean_inc(v_constName_1952_);
v___x_2055_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v___x_2007_, v_constName_1952_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_dec(v_constName_1952_);
v___y_1960_ = v___y_2009_;
v___y_1961_ = v___x_2010_;
v___y_1962_ = v___x_2055_;
goto v___jp_1959_;
}
else
{
lean_object* v_a_2056_; uint8_t v___x_2057_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
v___x_2057_ = l_Lean_Exception_isInterrupt(v_a_2056_);
if (v___x_2057_ == 0)
{
uint8_t v___x_2058_; 
v___x_2058_ = l_Lean_Exception_isRuntime(v_a_2056_);
v___y_2001_ = v___y_2009_;
v___y_2002_ = v___x_2055_;
v___y_2003_ = v___x_2010_;
v___y_2004_ = v___x_2058_;
goto v___jp_2000_;
}
else
{
lean_dec(v_a_2056_);
v___y_2001_ = v___y_2009_;
v___y_2002_ = v___x_2055_;
v___y_2003_ = v___x_2010_;
v___y_2004_ = v___x_2057_;
goto v___jp_2000_;
}
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref(v_ctx_1953_);
lean_dec(v_constName_1952_);
v_a_2062_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_1997_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_1997_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
v___jp_1959_:
{
if (lean_obj_tag(v___y_1962_) == 0)
{
lean_object* v_a_1963_; uint8_t v___x_1964_; uint8_t v___x_1965_; uint8_t v___x_1966_; uint8_t v___x_1967_; lean_object* v___x_1968_; uint64_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_a_1963_ = lean_ctor_get(v___y_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___y_1962_, 1);
v___x_1964_ = 0;
v___x_1965_ = 1;
v___x_1966_ = 0;
v___x_1967_ = 2;
v___x_1968_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1968_, 0, v___x_1964_);
lean_ctor_set_uint8(v___x_1968_, 1, v___x_1964_);
lean_ctor_set_uint8(v___x_1968_, 2, v___x_1964_);
lean_ctor_set_uint8(v___x_1968_, 3, v___x_1964_);
lean_ctor_set_uint8(v___x_1968_, 4, v___x_1964_);
lean_ctor_set_uint8(v___x_1968_, 5, v___y_1960_);
lean_ctor_set_uint8(v___x_1968_, 6, v___y_1960_);
lean_ctor_set_uint8(v___x_1968_, 7, v___x_1964_);
lean_ctor_set_uint8(v___x_1968_, 8, v___y_1960_);
lean_ctor_set_uint8(v___x_1968_, 9, v___x_1965_);
lean_ctor_set_uint8(v___x_1968_, 10, v___x_1966_);
lean_ctor_set_uint8(v___x_1968_, 11, v___y_1960_);
lean_ctor_set_uint8(v___x_1968_, 12, v___y_1960_);
lean_ctor_set_uint8(v___x_1968_, 13, v___y_1960_);
lean_ctor_set_uint8(v___x_1968_, 14, v___x_1967_);
lean_ctor_set_uint8(v___x_1968_, 15, v___y_1960_);
lean_ctor_set_uint8(v___x_1968_, 16, v___y_1960_);
lean_ctor_set_uint8(v___x_1968_, 17, v___y_1960_);
lean_ctor_set_uint8(v___x_1968_, 18, v___y_1960_);
v___x_1969_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1968_);
v___x_1970_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1970_, 0, v___x_1968_);
lean_ctor_set_uint64(v___x_1970_, sizeof(void*)*1, v___x_1969_);
v___x_1971_ = lean_box(1);
v___x_1972_ = lean_unsigned_to_nat(0u);
v___x_1973_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2);
v___x_1974_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3));
v___x_1975_ = lean_box(0);
v___x_1976_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1976_, 0, v___x_1970_);
lean_ctor_set(v___x_1976_, 1, v___x_1971_);
lean_ctor_set(v___x_1976_, 2, v___x_1973_);
lean_ctor_set(v___x_1976_, 3, v___x_1974_);
lean_ctor_set(v___x_1976_, 4, v___x_1975_);
lean_ctor_set(v___x_1976_, 5, v___x_1972_);
lean_ctor_set(v___x_1976_, 6, v___x_1975_);
lean_ctor_set_uint8(v___x_1976_, sizeof(void*)*7, v___x_1964_);
lean_ctor_set_uint8(v___x_1976_, sizeof(void*)*7 + 1, v___x_1964_);
lean_ctor_set_uint8(v___x_1976_, sizeof(void*)*7 + 2, v___x_1964_);
lean_ctor_set_uint8(v___x_1976_, sizeof(void*)*7 + 3, v___y_1961_);
v___x_1977_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7);
v___x_1978_ = lean_st_mk_ref(v___x_1977_);
v___x_1979_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1953_, v_builtin_1954_, v_a_1963_, v___x_1976_, v___x_1978_, v___y_1956_, v___y_1957_);
lean_dec_ref_known(v___x_1976_, 7);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1988_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = lean_st_ref_get(v___x_1978_);
lean_dec(v___x_1978_);
lean_dec(v___x_1984_);
if (v_isShared_1983_ == 0)
{
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1980_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
else
{
lean_dec(v___x_1978_);
return v___x_1979_;
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec_ref(v_ctx_1953_);
v_a_1989_ = lean_ctor_get(v___y_1962_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___y_1962_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___y_1962_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___y_1962_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed(lean_object* v_constName_2070_, lean_object* v_ctx_2071_, lean_object* v_builtin_2072_, lean_object* v_catName_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
uint8_t v_builtin_boxed_2077_; lean_object* v_res_2078_; 
v_builtin_boxed_2077_ = lean_unbox(v_builtin_2072_);
v_res_2078_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(v_constName_2070_, v_ctx_2071_, v_builtin_boxed_2077_, v_catName_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v_catName_2073_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(lean_object* v___y_2079_, uint8_t v_isExporting_2080_, lean_object* v___x_2081_, lean_object* v_a_x3f_2082_){
_start:
{
lean_object* v___x_2084_; lean_object* v_env_2085_; lean_object* v_nextMacroScope_2086_; lean_object* v_ngen_2087_; lean_object* v_auxDeclNGen_2088_; lean_object* v_traceState_2089_; lean_object* v_messages_2090_; lean_object* v_infoState_2091_; lean_object* v_snapshotTasks_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2103_; 
v___x_2084_ = lean_st_ref_take(v___y_2079_);
v_env_2085_ = lean_ctor_get(v___x_2084_, 0);
v_nextMacroScope_2086_ = lean_ctor_get(v___x_2084_, 1);
v_ngen_2087_ = lean_ctor_get(v___x_2084_, 2);
v_auxDeclNGen_2088_ = lean_ctor_get(v___x_2084_, 3);
v_traceState_2089_ = lean_ctor_get(v___x_2084_, 4);
v_messages_2090_ = lean_ctor_get(v___x_2084_, 6);
v_infoState_2091_ = lean_ctor_get(v___x_2084_, 7);
v_snapshotTasks_2092_ = lean_ctor_get(v___x_2084_, 8);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v___x_2084_, 5);
lean_dec(v_unused_2104_);
v___x_2094_ = v___x_2084_;
v_isShared_2095_ = v_isSharedCheck_2103_;
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
v_isShared_2095_ = v_isSharedCheck_2103_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2096_ = l_Lean_Environment_setExporting(v_env_2085_, v_isExporting_2080_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 5, v___x_2081_);
lean_ctor_set(v___x_2094_, 0, v___x_2096_);
v___x_2098_ = v___x_2094_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_nextMacroScope_2086_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_ngen_2087_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v_auxDeclNGen_2088_);
lean_ctor_set(v_reuseFailAlloc_2102_, 4, v_traceState_2089_);
lean_ctor_set(v_reuseFailAlloc_2102_, 5, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2102_, 6, v_messages_2090_);
lean_ctor_set(v_reuseFailAlloc_2102_, 7, v_infoState_2091_);
lean_ctor_set(v_reuseFailAlloc_2102_, 8, v_snapshotTasks_2092_);
v___x_2098_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = lean_st_ref_set(v___y_2079_, v___x_2098_);
v___x_2100_ = lean_box(0);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v___y_2105_, lean_object* v_isExporting_2106_, lean_object* v___x_2107_, lean_object* v_a_x3f_2108_, lean_object* v___y_2109_){
_start:
{
uint8_t v_isExporting_boxed_2110_; lean_object* v_res_2111_; 
v_isExporting_boxed_2110_ = lean_unbox(v_isExporting_2106_);
v_res_2111_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2105_, v_isExporting_boxed_2110_, v___x_2107_, v_a_x3f_2108_);
lean_dec(v_a_x3f_2108_);
lean_dec(v___y_2105_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(lean_object* v_x_2112_, uint8_t v_isExporting_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; lean_object* v_env_2118_; uint8_t v_isExporting_2119_; uint8_t v___y_2171_; lean_object* v___x_2173_; uint8_t v_isModule_2174_; uint8_t v___x_2175_; 
v___x_2117_ = lean_st_ref_get(v___y_2115_);
v_env_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc_ref(v_env_2118_);
lean_dec(v___x_2117_);
v_isExporting_2119_ = lean_ctor_get_uint8(v_env_2118_, sizeof(void*)*8);
v___x_2173_ = l_Lean_Environment_header(v_env_2118_);
lean_dec_ref(v_env_2118_);
v_isModule_2174_ = lean_ctor_get_uint8(v___x_2173_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2173_);
v___x_2175_ = lean_bool_not(v_isModule_2174_);
if (v___x_2175_ == 0)
{
if (v_isExporting_2119_ == 0)
{
if (v_isExporting_2113_ == 0)
{
lean_object* v___x_2176_; 
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
v___x_2176_ = lean_apply_3(v_x_2112_, v___y_2114_, v___y_2115_, lean_box(0));
return v___x_2176_;
}
else
{
goto v___jp_2120_;
}
}
else
{
v___y_2171_ = v_isExporting_2113_;
goto v___jp_2170_;
}
}
else
{
v___y_2171_ = v___x_2175_;
goto v___jp_2170_;
}
v___jp_2120_:
{
lean_object* v___x_2121_; lean_object* v_env_2122_; lean_object* v_nextMacroScope_2123_; lean_object* v_ngen_2124_; lean_object* v_auxDeclNGen_2125_; lean_object* v_traceState_2126_; lean_object* v_messages_2127_; lean_object* v_infoState_2128_; lean_object* v_snapshotTasks_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2168_; 
v___x_2121_ = lean_st_ref_take(v___y_2115_);
v_env_2122_ = lean_ctor_get(v___x_2121_, 0);
v_nextMacroScope_2123_ = lean_ctor_get(v___x_2121_, 1);
v_ngen_2124_ = lean_ctor_get(v___x_2121_, 2);
v_auxDeclNGen_2125_ = lean_ctor_get(v___x_2121_, 3);
v_traceState_2126_ = lean_ctor_get(v___x_2121_, 4);
v_messages_2127_ = lean_ctor_get(v___x_2121_, 6);
v_infoState_2128_ = lean_ctor_get(v___x_2121_, 7);
v_snapshotTasks_2129_ = lean_ctor_get(v___x_2121_, 8);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v___x_2121_, 5);
lean_dec(v_unused_2169_);
v___x_2131_ = v___x_2121_;
v_isShared_2132_ = v_isSharedCheck_2168_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_snapshotTasks_2129_);
lean_inc(v_infoState_2128_);
lean_inc(v_messages_2127_);
lean_inc(v_traceState_2126_);
lean_inc(v_auxDeclNGen_2125_);
lean_inc(v_ngen_2124_);
lean_inc(v_nextMacroScope_2123_);
lean_inc(v_env_2122_);
lean_dec(v___x_2121_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2168_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2133_ = l_Lean_Environment_setExporting(v_env_2122_, v_isExporting_2113_);
v___x_2134_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 5, v___x_2134_);
lean_ctor_set(v___x_2131_, 0, v___x_2133_);
v___x_2136_ = v___x_2131_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_nextMacroScope_2123_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_ngen_2124_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_auxDeclNGen_2125_);
lean_ctor_set(v_reuseFailAlloc_2167_, 4, v_traceState_2126_);
lean_ctor_set(v_reuseFailAlloc_2167_, 5, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2167_, 6, v_messages_2127_);
lean_ctor_set(v_reuseFailAlloc_2167_, 7, v_infoState_2128_);
lean_ctor_set(v_reuseFailAlloc_2167_, 8, v_snapshotTasks_2129_);
v___x_2136_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2137_; lean_object* v_r_2138_; 
v___x_2137_ = lean_st_ref_set(v___y_2115_, v___x_2136_);
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
v_r_2138_ = lean_apply_3(v_x_2112_, v___y_2114_, v___y_2115_, lean_box(0));
if (lean_obj_tag(v_r_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2155_; 
v_a_2139_ = lean_ctor_get(v_r_2138_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_r_2138_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2141_ = v_r_2138_;
v_isShared_2142_ = v_isSharedCheck_2155_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v_r_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2155_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
lean_inc(v_a_2139_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set_tag(v___x_2141_, 1);
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
v___x_2145_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2115_, v_isExporting_2119_, v___x_2134_, v___x_2144_);
lean_dec_ref(v___x_2144_);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; 
v_unused_2153_ = lean_ctor_get(v___x_2145_, 0);
lean_dec(v_unused_2153_);
v___x_2147_ = v___x_2145_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_dec(v___x_2145_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v_a_2139_);
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2139_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
v_a_2156_ = lean_ctor_get(v_r_2138_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v_r_2138_, 1);
v___x_2157_ = lean_box(0);
v___x_2158_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2115_, v_isExporting_2119_, v___x_2134_, v___x_2157_);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v___x_2158_, 0);
lean_dec(v_unused_2166_);
v___x_2160_ = v___x_2158_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_dec(v___x_2158_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set_tag(v___x_2160_, 1);
lean_ctor_set(v___x_2160_, 0, v_a_2156_);
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2156_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
}
v___jp_2170_:
{
if (v___y_2171_ == 0)
{
goto v___jp_2120_;
}
else
{
lean_object* v___x_2172_; 
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
v___x_2172_ = lean_apply_3(v_x_2112_, v___y_2114_, v___y_2115_, lean_box(0));
return v___x_2172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___boxed(lean_object* v_x_2177_, lean_object* v_isExporting_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
uint8_t v_isExporting_boxed_2182_; lean_object* v_res_2183_; 
v_isExporting_boxed_2182_ = lean_unbox(v_isExporting_2178_);
v_res_2183_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2177_, v_isExporting_boxed_2182_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(lean_object* v_x_2184_, uint8_t v_when_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
if (v_when_2185_ == 0)
{
lean_object* v___x_2189_; 
lean_inc(v___y_2187_);
lean_inc_ref(v___y_2186_);
v___x_2189_ = lean_apply_3(v_x_2184_, v___y_2186_, v___y_2187_, lean_box(0));
return v___x_2189_;
}
else
{
uint8_t v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = 0;
v___x_2191_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2184_, v___x_2190_, v___y_2186_, v___y_2187_);
return v___x_2191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg___boxed(lean_object* v_x_2192_, lean_object* v_when_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
uint8_t v_when_boxed_2197_; lean_object* v_res_2198_; 
v_when_boxed_2197_ = lean_unbox(v_when_2193_);
v_res_2198_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v_x_2192_, v_when_boxed_2197_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(lean_object* v_ctx_2199_, lean_object* v_catName_2200_, lean_object* v_constName_2201_, uint8_t v_builtin_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; lean_object* v___f_2207_; uint8_t v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = lean_box(v_builtin_2202_);
v___f_2207_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_2207_, 0, v_constName_2201_);
lean_closure_set(v___f_2207_, 1, v_ctx_2199_);
lean_closure_set(v___f_2207_, 2, v___x_2206_);
lean_closure_set(v___f_2207_, 3, v_catName_2200_);
v___x_2208_ = 1;
v___x_2209_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v___f_2207_, v___x_2208_, v___y_2203_, v___y_2204_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed(lean_object* v_ctx_2210_, lean_object* v_catName_2211_, lean_object* v_constName_2212_, lean_object* v_builtin_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
uint8_t v_builtin_boxed_2217_; lean_object* v_res_2218_; 
v_builtin_boxed_2217_ = lean_unbox(v_builtin_2213_);
v_res_2218_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(v_ctx_2210_, v_catName_2211_, v_constName_2212_, v_builtin_boxed_2217_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg(lean_object* v_ctx_2219_){
_start:
{
lean_object* v___f_2221_; lean_object* v___x_2222_; 
v___f_2221_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed), 7, 1);
lean_closure_set(v___f_2221_, 0, v_ctx_2219_);
v___x_2222_ = l_Lean_Parser_registerParserAttributeHook(v___f_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___boxed(lean_object* v_ctx_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v_ctx_2223_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object* v_00_u03b1_2226_, lean_object* v_ctx_2227_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v_ctx_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___boxed(lean_object* v_00_u03b1_2230_, lean_object* v_ctx_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_ParserCompiler_registerParserCompiler(v_00_u03b1_2230_, v_ctx_2231_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(lean_object* v_00_u03b1_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(v_00_u03b1_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(lean_object* v_00_u03b1_2244_, lean_object* v_typeName_2245_, lean_object* v_constName_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v_typeName_2245_, v_constName_2246_, v___y_2247_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___boxed(lean_object* v_00_u03b1_2251_, lean_object* v_typeName_2252_, lean_object* v_constName_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(v_00_u03b1_2251_, v_typeName_2252_, v_constName_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(lean_object* v_00_u03b1_2258_, lean_object* v_x_2259_, uint8_t v_isExporting_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2259_, v_isExporting_2260_, v___y_2261_, v___y_2262_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2265_, lean_object* v_x_2266_, lean_object* v_isExporting_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
uint8_t v_isExporting_boxed_2271_; lean_object* v_res_2272_; 
v_isExporting_boxed_2271_ = lean_unbox(v_isExporting_2267_);
v_res_2272_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(v_00_u03b1_2265_, v_x_2266_, v_isExporting_boxed_2271_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(lean_object* v_00_u03b1_2273_, lean_object* v_x_2274_, uint8_t v_when_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v_x_2274_, v_when_2275_, v___y_2276_, v___y_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___boxed(lean_object* v_00_u03b1_2280_, lean_object* v_x_2281_, lean_object* v_when_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
uint8_t v_when_boxed_2286_; lean_object* v_res_2287_; 
v_when_boxed_2286_ = lean_unbox(v_when_2282_);
v_res_2287_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(v_00_u03b1_2280_, v_x_2281_, v_when_boxed_2286_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(lean_object* v_00_u03b1_2288_, lean_object* v_constName_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_2289_, v___y_2290_, v___y_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2294_, lean_object* v_constName_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(v_00_u03b1_2294_, v_constName_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(lean_object* v_00_u03b1_2300_, lean_object* v_x_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v_x_2301_, v___y_2302_, v___y_2303_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2306_, lean_object* v_x_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(v_00_u03b1_2306_, v_x_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2312_, lean_object* v_ref_2313_, lean_object* v_constName_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_2313_, v_constName_2314_, v___y_2315_, v___y_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2319_, lean_object* v_ref_2320_, lean_object* v_constName_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(v_00_u03b1_2319_, v_ref_2320_, v_constName_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v_ref_2320_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2326_, lean_object* v_msg_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_2327_, v___y_2328_, v___y_2329_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2332_, lean_object* v_msg_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(v_00_u03b1_2332_, v_msg_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b1_2338_, lean_object* v_ref_2339_, lean_object* v_msg_2340_, lean_object* v_declHint_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_2339_, v_msg_2340_, v_declHint_2341_, v___y_2342_, v___y_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b1_2346_, lean_object* v_ref_2347_, lean_object* v_msg_2348_, lean_object* v_declHint_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_2346_, v_ref_2347_, v_msg_2348_, v_declHint_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v_ref_2347_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(lean_object* v_msg_2354_, lean_object* v_declHint_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_2354_, v_declHint_2355_, v___y_2357_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___boxed(lean_object* v_msg_2360_, lean_object* v_declHint_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(v_msg_2360_, v_declHint_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_2366_, lean_object* v_ref_2367_, lean_object* v_msg_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_2367_, v_msg_2368_, v___y_2369_, v___y_2370_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2373_, lean_object* v_ref_2374_, lean_object* v_msg_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(v_00_u03b1_2373_, v_ref_2374_, v_msg_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v_ref_2374_);
return v_res_2379_;
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
