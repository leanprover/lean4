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
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, lean_object*, lean_object*);
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
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2;
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
static lean_object* _init_l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = ((lean_object*)(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1));
v___x_16_ = ((lean_object*)(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0));
v___x_17_ = l_Lean_Name_mkStr3(v___x_16_, v___x_15_, v___x_15_);
return v___x_17_;
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
v___x_22_ = lean_obj_once(&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2, &l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_once, _init_l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2);
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
v___x_177_ = 2ULL;
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
lean_dec_ref(v___x_183_);
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
v___x_272_ = lean_obj_once(&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2, &l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_once, _init_l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2);
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
lean_dec_ref(v___y_296_);
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
lean_dec_ref(v___y_296_);
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
lean_dec_ref(v_x_330_);
lean_dec_ref(v_params_329_);
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
lean_dec_ref(v___x_368_);
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
lean_dec_ref(v___x_408_);
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
lean_dec_ref(v___x_477_);
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
lean_dec_ref(v___x_477_);
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
lean_dec_ref(v___x_477_);
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
lean_dec_ref(v___x_533_);
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
v___x_581_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
lean_ctor_set(v___x_581_, 3, v___x_579_);
lean_ctor_set(v___x_581_, 4, v___x_579_);
lean_ctor_set(v___x_581_, 5, v___x_579_);
lean_ctor_set(v___x_581_, 6, v___x_579_);
lean_ctor_set(v___x_581_, 7, v___x_579_);
lean_ctor_set(v___x_581_, 8, v___x_579_);
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
lean_object* v___x_620_; lean_object* v_env_621_; uint8_t v___x_622_; 
v___x_620_ = lean_st_ref_get(v___y_618_);
v_env_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc_ref(v_env_621_);
lean_dec(v___x_620_);
v___x_622_ = l_Lean_Name_isAnonymous(v_declHint_617_);
if (v___x_622_ == 0)
{
uint8_t v_isExporting_623_; 
v_isExporting_623_ = lean_ctor_get_uint8(v_env_621_, sizeof(void*)*8);
if (v_isExporting_623_ == 0)
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
lean_object* v___x_625_; uint8_t v___x_626_; 
lean_inc_ref(v_env_621_);
v___x_625_ = l_Lean_Environment_setExporting(v_env_621_, v___x_622_);
lean_inc(v_declHint_617_);
lean_inc_ref(v___x_625_);
v___x_626_ = l_Lean_Environment_contains(v___x_625_, v_declHint_617_, v_isExporting_623_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
lean_dec_ref(v___x_625_);
lean_dec_ref(v_env_621_);
lean_dec(v_declHint_617_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_msg_616_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v_c_633_; lean_object* v___x_634_; 
v___x_628_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_629_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_630_ = l_Lean_Options_empty;
v___x_631_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_631_, 0, v___x_625_);
lean_ctor_set(v___x_631_, 1, v___x_628_);
lean_ctor_set(v___x_631_, 2, v___x_629_);
lean_ctor_set(v___x_631_, 3, v___x_630_);
lean_inc(v_declHint_617_);
v___x_632_ = l_Lean_MessageData_ofConstName(v_declHint_617_, v___x_622_);
v_c_633_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_633_, 0, v___x_631_);
lean_ctor_set(v_c_633_, 1, v___x_632_);
v___x_634_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_621_, v_declHint_617_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec_ref(v_env_621_);
lean_dec(v_declHint_617_);
v___x_635_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v_c_633_);
v___x_637_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = l_Lean_MessageData_note(v___x_638_);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v_msg_616_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
else
{
lean_object* v_val_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_677_; 
v_val_642_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_677_ == 0)
{
v___x_644_ = v___x_634_;
v_isShared_645_ = v_isSharedCheck_677_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_val_642_);
lean_dec(v___x_634_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_677_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_mod_649_; uint8_t v___x_650_; 
v___x_646_ = lean_box(0);
v___x_647_ = l_Lean_Environment_header(v_env_621_);
lean_dec_ref(v_env_621_);
v___x_648_ = l_Lean_EnvironmentHeader_moduleNames(v___x_647_);
v_mod_649_ = lean_array_get(v___x_646_, v___x_648_, v_val_642_);
lean_dec(v_val_642_);
lean_dec_ref(v___x_648_);
v___x_650_ = l_Lean_isPrivateName(v_declHint_617_);
lean_dec(v_declHint_617_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_651_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v_c_633_);
v___x_653_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_MessageData_ofName(v_mod_649_);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = l_Lean_MessageData_note(v___x_658_);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v_msg_616_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 0);
lean_ctor_set(v___x_644_, 0, v___x_660_);
v___x_662_ = v___x_644_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_664_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v_c_633_);
v___x_666_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Lean_MessageData_ofName(v_mod_649_);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_MessageData_note(v___x_671_);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v_msg_616_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 0);
lean_ctor_set(v___x_644_, 0, v___x_673_);
v___x_675_ = v___x_644_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_678_; 
lean_dec_ref(v_env_621_);
lean_dec(v_declHint_617_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v_msg_616_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_msg_679_, lean_object* v_declHint_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_679_, v_declHint_680_, v___y_681_);
lean_dec(v___y_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_684_, lean_object* v_declHint_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_701_; 
v___x_691_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_684_, v_declHint_685_, v___y_689_);
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_701_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_701_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_701_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_696_ = l_Lean_unknownIdentifierMessageTag;
v___x_697_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v_a_692_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_697_);
v___x_699_ = v___x_694_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_702_, lean_object* v_declHint_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_702_, v_declHint_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(lean_object* v_msgData_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; lean_object* v_env_717_; lean_object* v___x_718_; lean_object* v_mctx_719_; lean_object* v_lctx_720_; lean_object* v_options_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_716_ = lean_st_ref_get(v___y_714_);
v_env_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc_ref(v_env_717_);
lean_dec(v___x_716_);
v___x_718_ = lean_st_ref_get(v___y_712_);
v_mctx_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc_ref(v_mctx_719_);
lean_dec(v___x_718_);
v_lctx_720_ = lean_ctor_get(v___y_711_, 2);
v_options_721_ = lean_ctor_get(v___y_713_, 2);
lean_inc_ref(v_options_721_);
lean_inc_ref(v_lctx_720_);
v___x_722_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_722_, 0, v_env_717_);
lean_ctor_set(v___x_722_, 1, v_mctx_719_);
lean_ctor_set(v___x_722_, 2, v_lctx_720_);
lean_ctor_set(v___x_722_, 3, v_options_721_);
v___x_723_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v_msgData_710_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___boxed(lean_object* v_msgData_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(v_msgData_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(lean_object* v_msg_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_ref_738_; lean_object* v___x_739_; lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_748_; 
v_ref_738_ = lean_ctor_get(v___y_735_, 5);
v___x_739_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(v_msg_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_748_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_746_; 
lean_inc(v_ref_738_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v_ref_738_);
lean_ctor_set(v___x_744_, 1, v_a_740_);
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 1);
lean_ctor_set(v___x_742_, 0, v___x_744_);
v___x_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg___boxed(lean_object* v_msg_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v_msg_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_756_, lean_object* v_msg_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_fileName_763_; lean_object* v_fileMap_764_; lean_object* v_options_765_; lean_object* v_currRecDepth_766_; lean_object* v_maxRecDepth_767_; lean_object* v_ref_768_; lean_object* v_currNamespace_769_; lean_object* v_openDecls_770_; lean_object* v_initHeartbeats_771_; lean_object* v_maxHeartbeats_772_; lean_object* v_quotContext_773_; lean_object* v_currMacroScope_774_; uint8_t v_diag_775_; lean_object* v_cancelTk_x3f_776_; uint8_t v_suppressElabErrors_777_; lean_object* v_inheritedTraceOptions_778_; lean_object* v_ref_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_fileName_763_ = lean_ctor_get(v___y_760_, 0);
v_fileMap_764_ = lean_ctor_get(v___y_760_, 1);
v_options_765_ = lean_ctor_get(v___y_760_, 2);
v_currRecDepth_766_ = lean_ctor_get(v___y_760_, 3);
v_maxRecDepth_767_ = lean_ctor_get(v___y_760_, 4);
v_ref_768_ = lean_ctor_get(v___y_760_, 5);
v_currNamespace_769_ = lean_ctor_get(v___y_760_, 6);
v_openDecls_770_ = lean_ctor_get(v___y_760_, 7);
v_initHeartbeats_771_ = lean_ctor_get(v___y_760_, 8);
v_maxHeartbeats_772_ = lean_ctor_get(v___y_760_, 9);
v_quotContext_773_ = lean_ctor_get(v___y_760_, 10);
v_currMacroScope_774_ = lean_ctor_get(v___y_760_, 11);
v_diag_775_ = lean_ctor_get_uint8(v___y_760_, sizeof(void*)*14);
v_cancelTk_x3f_776_ = lean_ctor_get(v___y_760_, 12);
v_suppressElabErrors_777_ = lean_ctor_get_uint8(v___y_760_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_778_ = lean_ctor_get(v___y_760_, 13);
v_ref_779_ = l_Lean_replaceRef(v_ref_756_, v_ref_768_);
lean_inc_ref(v_inheritedTraceOptions_778_);
lean_inc(v_cancelTk_x3f_776_);
lean_inc(v_currMacroScope_774_);
lean_inc(v_quotContext_773_);
lean_inc(v_maxHeartbeats_772_);
lean_inc(v_initHeartbeats_771_);
lean_inc(v_openDecls_770_);
lean_inc(v_currNamespace_769_);
lean_inc(v_maxRecDepth_767_);
lean_inc(v_currRecDepth_766_);
lean_inc_ref(v_options_765_);
lean_inc_ref(v_fileMap_764_);
lean_inc_ref(v_fileName_763_);
v___x_780_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_780_, 0, v_fileName_763_);
lean_ctor_set(v___x_780_, 1, v_fileMap_764_);
lean_ctor_set(v___x_780_, 2, v_options_765_);
lean_ctor_set(v___x_780_, 3, v_currRecDepth_766_);
lean_ctor_set(v___x_780_, 4, v_maxRecDepth_767_);
lean_ctor_set(v___x_780_, 5, v_ref_779_);
lean_ctor_set(v___x_780_, 6, v_currNamespace_769_);
lean_ctor_set(v___x_780_, 7, v_openDecls_770_);
lean_ctor_set(v___x_780_, 8, v_initHeartbeats_771_);
lean_ctor_set(v___x_780_, 9, v_maxHeartbeats_772_);
lean_ctor_set(v___x_780_, 10, v_quotContext_773_);
lean_ctor_set(v___x_780_, 11, v_currMacroScope_774_);
lean_ctor_set(v___x_780_, 12, v_cancelTk_x3f_776_);
lean_ctor_set(v___x_780_, 13, v_inheritedTraceOptions_778_);
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*14, v_diag_775_);
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*14 + 1, v_suppressElabErrors_777_);
v___x_781_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v_msg_757_, v___y_758_, v___y_759_, v___x_780_, v___y_761_);
lean_dec_ref(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_782_, lean_object* v_msg_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_782_, v_msg_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v_ref_782_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(lean_object* v_ref_790_, lean_object* v_msg_791_, lean_object* v_declHint_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; lean_object* v_a_799_; lean_object* v___x_800_; 
v___x_798_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_791_, v_declHint_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref(v___x_798_);
v___x_800_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_790_, v_a_799_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_ref_801_, lean_object* v_msg_802_, lean_object* v_declHint_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_801_, v_msg_802_, v_declHint_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v_ref_801_);
return v_res_809_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__0));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__2));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_816_, lean_object* v_constName_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; uint8_t v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_823_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_824_ = 0;
lean_inc(v_constName_817_);
v___x_825_ = l_Lean_MessageData_ofConstName(v_constName_817_, v___x_824_);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_823_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_816_, v___x_828_, v_constName_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_830_, lean_object* v_constName_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_830_, v_constName_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v_ref_830_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(lean_object* v_constName_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_ref_844_; lean_object* v___x_845_; 
v_ref_844_ = lean_ctor_get(v___y_841_, 5);
v___x_845_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_844_, v_constName_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg___boxed(lean_object* v_constName_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(lean_object* v_constName_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; lean_object* v_env_860_; uint8_t v___x_861_; lean_object* v___x_862_; 
v___x_859_ = lean_st_ref_get(v___y_857_);
v_env_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc_ref(v_env_860_);
lean_dec(v___x_859_);
v___x_861_ = 0;
lean_inc(v_constName_853_);
v___x_862_ = l_Lean_Environment_find_x3f(v_env_860_, v_constName_853_, v___x_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
return v___x_863_;
}
else
{
lean_object* v_val_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v_constName_853_);
v_val_864_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_862_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_val_864_);
lean_dec(v___x_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 0);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_val_864_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3___boxed(lean_object* v_constName_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(v_constName_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(lean_object* v_b_879_, lean_object* v_arg_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = l_Lean_Expr_app___override(v_b_879_, v_arg_880_);
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1___boxed(lean_object* v_b_889_, lean_object* v_arg_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_889_, v_arg_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(lean_object* v_x_897_, lean_object* v_b_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v_b_898_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed(lean_object* v_x_905_, lean_object* v_b_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(v_x_905_, v_b_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec_ref(v_x_905_);
return v_res_912_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_913_; lean_object* v_dummy_914_; 
v___x_913_ = lean_box(0);
v_dummy_914_ = l_Lean_Expr_sort___override(v___x_913_);
return v_dummy_914_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(lean_object* v_upperBound_916_, lean_object* v_params_917_, lean_object* v___x_918_, lean_object* v_ctx_919_, uint8_t v_builtin_920_, uint8_t v_force_921_, lean_object* v_a_922_, lean_object* v_b_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___y_930_; uint8_t v___x_952_; 
v___x_952_ = lean_nat_dec_lt(v_a_922_, v_upperBound_916_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_dec(v_a_922_);
lean_dec_ref(v_ctx_919_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_b_923_);
return v___x_953_;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = l_Lean_instInhabitedExpr;
v___x_955_ = lean_array_get_borrowed(v___x_954_, v_params_917_, v_a_922_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___x_955_);
v___x_956_ = lean_infer_type(v___x_955_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___f_958_; uint8_t v___x_959_; lean_object* v___x_960_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref(v___x_956_);
v___f_958_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0));
v___x_959_ = 0;
v___x_960_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_957_, v___f_958_, v___x_959_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref(v___x_960_);
v___x_962_ = lean_array_get_borrowed(v___x_954_, v___x_918_, v_a_922_);
v___x_963_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_919_);
v___x_964_ = l_Lean_Expr_isConstOf(v_a_961_, v___x_963_);
lean_dec(v___x_963_);
lean_dec(v_a_961_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; 
lean_inc(v___x_962_);
v___x_965_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_923_, v___x_962_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
v___y_930_ = v___x_965_;
goto v___jp_929_;
}
else
{
lean_object* v___x_966_; 
lean_inc(v___x_962_);
lean_inc_ref(v_ctx_919_);
v___x_966_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_919_, v_builtin_920_, v_force_921_, v___x_962_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref(v___x_966_);
v___x_968_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_923_, v_a_967_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
v___y_930_ = v___x_968_;
goto v___jp_929_;
}
else
{
lean_dec_ref(v_b_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_ctx_919_);
return v___x_966_;
}
}
}
else
{
lean_dec_ref(v_b_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_ctx_919_);
return v___x_960_;
}
}
else
{
lean_dec_ref(v_b_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_ctx_919_);
return v___x_956_;
}
}
v___jp_929_:
{
if (lean_obj_tag(v___y_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_943_; 
v_a_931_ = lean_ctor_get(v___y_930_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___y_930_);
if (v_isSharedCheck_943_ == 0)
{
v___x_933_ = v___y_930_;
v_isShared_934_ = v_isSharedCheck_943_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___y_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_943_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
if (lean_obj_tag(v_a_931_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; 
lean_dec(v_a_922_);
lean_dec_ref(v_ctx_919_);
v_a_935_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_a_935_);
lean_dec_ref(v_a_931_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v_a_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
lean_del_object(v___x_933_);
v_a_939_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_a_939_);
lean_dec_ref(v_a_931_);
v___x_940_ = lean_unsigned_to_nat(1u);
v___x_941_ = lean_nat_add(v_a_922_, v___x_940_);
lean_dec(v_a_922_);
v_a_922_ = v___x_941_;
v_b_923_ = v_a_939_;
goto _start;
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec(v_a_922_);
lean_dec_ref(v_ctx_919_);
v_a_944_ = lean_ctor_get(v___y_930_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___y_930_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___y_930_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___y_930_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(lean_object* v_a_969_, lean_object* v_ctx_970_, uint8_t v_builtin_971_, uint8_t v_force_972_, lean_object* v___x_973_, lean_object* v_params_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_dummy_981_; lean_object* v_nargs_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___y_988_; lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v_dummy_981_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0, &l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0);
v_nargs_982_ = l_Lean_Expr_getAppNumArgs(v_a_969_);
lean_inc(v_nargs_982_);
v___x_983_ = lean_mk_array(v_nargs_982_, v_dummy_981_);
v___x_984_ = lean_unsigned_to_nat(1u);
v___x_985_ = lean_nat_sub(v_nargs_982_, v___x_984_);
lean_dec(v_nargs_982_);
v___x_986_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_969_, v___x_983_, v___x_985_);
v___x_991_ = lean_array_get_size(v_params_974_);
v___x_992_ = lean_array_get_size(v___x_986_);
v___x_993_ = lean_nat_dec_le(v___x_991_, v___x_992_);
if (v___x_993_ == 0)
{
v___y_988_ = v___x_992_;
goto v___jp_987_;
}
else
{
v___y_988_ = v___x_991_;
goto v___jp_987_;
}
v___jp_987_:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v___y_988_, v_params_974_, v___x_986_, v_ctx_970_, v_builtin_971_, v_force_972_, v___x_989_, v___x_973_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec_ref(v___x_986_);
lean_dec(v___y_988_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed(lean_object* v_a_994_, lean_object* v_ctx_995_, lean_object* v_builtin_996_, lean_object* v_force_997_, lean_object* v___x_998_, lean_object* v_params_999_, lean_object* v_x_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
uint8_t v_builtin_boxed_1006_; uint8_t v_force_boxed_1007_; lean_object* v_res_1008_; 
v_builtin_boxed_1006_ = lean_unbox(v_builtin_996_);
v_force_boxed_1007_ = lean_unbox(v_force_997_);
v_res_1008_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(v_a_994_, v_ctx_995_, v_builtin_boxed_1006_, v_force_boxed_1007_, v___x_998_, v_params_999_, v_x_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_x_1000_);
lean_dec_ref(v_params_999_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed(lean_object* v_ctx_1009_, lean_object* v_builtin_1010_, lean_object* v_force_1011_, lean_object* v_x_1012_, lean_object* v_b_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
uint8_t v_builtin_boxed_1019_; uint8_t v_force_boxed_1020_; lean_object* v_res_1021_; 
v_builtin_boxed_1019_ = lean_unbox(v_builtin_1010_);
v_force_boxed_1020_ = lean_unbox(v_force_1011_);
v_res_1021_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(v_ctx_1009_, v_builtin_boxed_1019_, v_force_boxed_1020_, v_x_1012_, v_b_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec_ref(v_x_1012_);
return v_res_1021_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6);
v___x_1038_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
lean_ctor_set(v___x_1038_, 2, v___x_1037_);
lean_ctor_set(v___x_1038_, 3, v___x_1037_);
lean_ctor_set(v___x_1038_, 4, v___x_1037_);
lean_ctor_set(v___x_1038_, 5, v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11));
v___x_1044_ = l_Lean_stringToMessageData(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13));
v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17));
v___x_1053_ = l_Lean_stringToMessageData(v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21));
v___x_1061_ = l_Lean_stringToMessageData(v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg(lean_object* v_ctx_1062_, uint8_t v_builtin_1063_, uint8_t v_force_1064_, lean_object* v_e_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Meta_whnfCore(v_e_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v_p_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
switch(lean_obj_tag(v_a_1072_))
{
case 6:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___f_1090_; uint8_t v___x_1091_; uint8_t v___x_1092_; lean_object* v___x_1093_; 
lean_dec_ref(v___x_1071_);
v___x_1088_ = lean_box(v_builtin_1063_);
v___x_1089_ = lean_box(v_force_1064_);
v___f_1090_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1090_, 0, v_ctx_1062_);
lean_closure_set(v___f_1090_, 1, v___x_1088_);
lean_closure_set(v___f_1090_, 2, v___x_1089_);
v___x_1091_ = 0;
v___x_1092_ = 1;
v___x_1093_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_a_1072_, v___f_1090_, v___x_1091_, v___x_1091_, v___x_1092_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
return v___x_1093_;
}
case 8:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___f_1096_; uint8_t v___x_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; 
lean_dec_ref(v___x_1071_);
v___x_1094_ = lean_box(v_builtin_1063_);
v___x_1095_ = lean_box(v_force_1064_);
v___f_1096_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1096_, 0, v_ctx_1062_);
lean_closure_set(v___f_1096_, 1, v___x_1094_);
lean_closure_set(v___f_1096_, 2, v___x_1095_);
v___x_1097_ = 0;
v___x_1098_ = 1;
v___x_1099_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_a_1072_, v___f_1096_, v___x_1097_, v___x_1097_, v___x_1098_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
return v___x_1099_;
}
case 1:
{
lean_dec_ref(v_a_1072_);
lean_dec_ref(v_ctx_1062_);
return v___x_1071_;
}
default: 
{
lean_object* v___x_1100_; 
lean_dec_ref(v___x_1071_);
v___x_1100_ = l_Lean_Expr_getAppFn(v_a_1072_);
if (lean_obj_tag(v___x_1100_) == 4)
{
lean_object* v_declName_1101_; lean_object* v___x_1102_; lean_object* v_env_1103_; lean_object* v_varName_1104_; lean_object* v_categoryAttr_1105_; lean_object* v_combinatorAttr_1106_; lean_object* v___x_1107_; 
v_declName_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_declName_1101_);
lean_dec_ref(v___x_1100_);
v___x_1102_ = lean_st_ref_get(v_a_1069_);
v_env_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc_ref(v_env_1103_);
lean_dec(v___x_1102_);
v_varName_1104_ = lean_ctor_get(v_ctx_1062_, 0);
v_categoryAttr_1105_ = lean_ctor_get(v_ctx_1062_, 1);
v_combinatorAttr_1106_ = lean_ctor_get(v_ctx_1062_, 2);
lean_inc_ref(v_env_1103_);
v___x_1107_ = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(v_combinatorAttr_1106_, v_env_1103_, v_declName_1101_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_inc(v_varName_1104_);
lean_inc(v_declName_1101_);
v___x_1108_ = l_Lean_Name_append(v_declName_1101_, v_varName_1104_);
lean_inc(v_declName_1101_);
v___x_1109_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(v_declName_1101_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref(v___x_1109_);
v___f_1111_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0));
v___x_1112_ = l_Lean_ConstantInfo_type(v_a_1110_);
v___x_1113_ = 0;
lean_inc_ref(v___x_1112_);
v___x_1114_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v___x_1112_, v___f_1111_, v___x_1113_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___f_1116_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1149_; uint8_t v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1218_; uint8_t v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; uint8_t v___y_1281_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref(v___x_1114_);
lean_inc_ref(v_ctx_1062_);
v___f_1116_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_1116_, 0, v_ctx_1062_);
v___x_1331_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20));
v___x_1332_ = l_Lean_Expr_isConstOf(v_a_1115_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = lean_obj_once(&l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2, &l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_once, _init_l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2);
v___x_1334_ = l_Lean_Expr_isConstOf(v_a_1115_, v___x_1333_);
lean_dec(v_a_1115_);
v___y_1281_ = v___x_1334_;
goto v___jp_1280_;
}
else
{
lean_dec(v_a_1115_);
v___y_1281_ = v___x_1332_;
goto v___jp_1280_;
}
v___jp_1117_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1124_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2));
lean_inc(v___y_1123_);
v___x_1125_ = lean_mk_syntax_ident(v___y_1123_);
v___x_1126_ = lean_mk_syntax_ident(v___y_1120_);
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_mk_empty_array_with_capacity(v___x_1127_);
v___x_1129_ = lean_array_push(v___x_1128_, v___x_1126_);
v___x_1130_ = ((lean_object*)(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__4));
v___x_1131_ = lean_box(2);
v___x_1132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v___x_1130_);
lean_ctor_set(v___x_1132_, 2, v___x_1129_);
v___x_1133_ = lean_unsigned_to_nat(2u);
v___x_1134_ = lean_mk_empty_array_with_capacity(v___x_1133_);
v___x_1135_ = lean_array_push(v___x_1134_, v___x_1125_);
v___x_1136_ = lean_array_push(v___x_1135_, v___x_1132_);
v___x_1137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1131_);
lean_ctor_set(v___x_1137_, 1, v___x_1124_);
lean_ctor_set(v___x_1137_, 2, v___x_1136_);
v___x_1138_ = 0;
lean_inc(v___x_1108_);
v___x_1139_ = l_Lean_Attribute_add(v___x_1108_, v___y_1123_, v___x_1137_, v___x_1138_, v___y_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_dec_ref(v___x_1139_);
v_p_1074_ = v___x_1108_;
v___y_1075_ = v___y_1118_;
v___y_1076_ = v___y_1119_;
v___y_1077_ = v___y_1121_;
v___y_1078_ = v___y_1122_;
goto v___jp_1073_;
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v___x_1108_);
lean_dec(v_a_1072_);
lean_dec_ref(v_ctx_1062_);
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
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
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
v___jp_1148_:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_addAndCompile(v___y_1149_, v___y_1150_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v___x_1156_; lean_object* v_env_1157_; lean_object* v_nextMacroScope_1158_; lean_object* v_ngen_1159_; lean_object* v_auxDeclNGen_1160_; lean_object* v_traceState_1161_; lean_object* v_messages_1162_; lean_object* v_infoState_1163_; lean_object* v_snapshotTasks_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v___x_1155_);
v___x_1156_ = lean_st_ref_take(v___y_1154_);
v_env_1157_ = lean_ctor_get(v___x_1156_, 0);
v_nextMacroScope_1158_ = lean_ctor_get(v___x_1156_, 1);
v_ngen_1159_ = lean_ctor_get(v___x_1156_, 2);
v_auxDeclNGen_1160_ = lean_ctor_get(v___x_1156_, 3);
v_traceState_1161_ = lean_ctor_get(v___x_1156_, 4);
v_messages_1162_ = lean_ctor_get(v___x_1156_, 6);
v_infoState_1163_ = lean_ctor_get(v___x_1156_, 7);
v_snapshotTasks_1164_ = lean_ctor_get(v___x_1156_, 8);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v___x_1156_, 5);
lean_dec(v_unused_1208_);
v___x_1166_ = v___x_1156_;
v_isShared_1167_ = v_isSharedCheck_1207_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_snapshotTasks_1164_);
lean_inc(v_infoState_1163_);
lean_inc(v_messages_1162_);
lean_inc(v_traceState_1161_);
lean_inc(v_auxDeclNGen_1160_);
lean_inc(v_ngen_1159_);
lean_inc(v_nextMacroScope_1158_);
lean_inc(v_env_1157_);
lean_dec(v___x_1156_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1207_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
lean_inc(v___x_1108_);
lean_inc_ref(v_combinatorAttr_1106_);
v___x_1168_ = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(v_combinatorAttr_1106_, v_env_1157_, v_declName_1101_, v___x_1108_);
v___x_1169_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 5, v___x_1169_);
lean_ctor_set(v___x_1166_, 0, v___x_1168_);
v___x_1171_ = v___x_1166_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_nextMacroScope_1158_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_ngen_1159_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_auxDeclNGen_1160_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_traceState_1161_);
lean_ctor_set(v_reuseFailAlloc_1206_, 5, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1206_, 6, v_messages_1162_);
lean_ctor_set(v_reuseFailAlloc_1206_, 7, v_infoState_1163_);
lean_ctor_set(v_reuseFailAlloc_1206_, 8, v_snapshotTasks_1164_);
v___x_1171_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_mctx_1174_; lean_object* v_zetaDeltaFVarIds_1175_; lean_object* v_postponed_1176_; lean_object* v_diag_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1204_; 
v___x_1172_ = lean_st_ref_set(v___y_1154_, v___x_1171_);
v___x_1173_ = lean_st_ref_take(v___y_1152_);
v_mctx_1174_ = lean_ctor_get(v___x_1173_, 0);
v_zetaDeltaFVarIds_1175_ = lean_ctor_get(v___x_1173_, 2);
v_postponed_1176_ = lean_ctor_get(v___x_1173_, 3);
v_diag_1177_ = lean_ctor_get(v___x_1173_, 4);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; 
v_unused_1205_ = lean_ctor_get(v___x_1173_, 1);
lean_dec(v_unused_1205_);
v___x_1179_ = v___x_1173_;
v_isShared_1180_ = v_isSharedCheck_1204_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_diag_1177_);
lean_inc(v_postponed_1176_);
lean_inc(v_zetaDeltaFVarIds_1175_);
lean_inc(v_mctx_1174_);
lean_dec(v___x_1173_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1204_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1181_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v___x_1181_);
v___x_1183_ = v___x_1179_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_mctx_1174_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_zetaDeltaFVarIds_1175_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_postponed_1176_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_diag_1177_);
v___x_1183_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = lean_st_ref_set(v___y_1152_, v___x_1183_);
v___x_1185_ = l_Lean_Expr_isConst(v___x_1112_);
lean_dec_ref(v___x_1112_);
if (v___x_1185_ == 0)
{
lean_dec(v_a_1110_);
v_p_1074_ = v___x_1108_;
v___y_1075_ = v___y_1151_;
v___y_1076_ = v___y_1152_;
v___y_1077_ = v___y_1153_;
v___y_1078_ = v___y_1154_;
goto v___jp_1073_;
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = l_Lean_ConstantInfo_value_x21(v_a_1110_, v___x_1113_);
lean_dec(v_a_1110_);
v___x_1187_ = l_Lean_ParserCompiler_parserNodeKind_x3f(v___x_1186_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref(v___x_1187_);
if (lean_obj_tag(v_a_1188_) == 1)
{
if (v_builtin_1063_ == 0)
{
lean_object* v_defn_1189_; lean_object* v_val_1190_; lean_object* v_name_1191_; 
v_defn_1189_ = lean_ctor_get(v_categoryAttr_1105_, 0);
v_val_1190_ = lean_ctor_get(v_a_1188_, 0);
lean_inc(v_val_1190_);
lean_dec_ref(v_a_1188_);
v_name_1191_ = lean_ctor_get(v_defn_1189_, 1);
lean_inc(v_name_1191_);
v___y_1118_ = v___y_1151_;
v___y_1119_ = v___y_1152_;
v___y_1120_ = v_val_1190_;
v___y_1121_ = v___y_1153_;
v___y_1122_ = v___y_1154_;
v___y_1123_ = v_name_1191_;
goto v___jp_1117_;
}
else
{
lean_object* v_defn_1192_; lean_object* v_val_1193_; lean_object* v_builtinName_1194_; 
v_defn_1192_ = lean_ctor_get(v_categoryAttr_1105_, 0);
v_val_1193_ = lean_ctor_get(v_a_1188_, 0);
lean_inc(v_val_1193_);
lean_dec_ref(v_a_1188_);
v_builtinName_1194_ = lean_ctor_get(v_defn_1192_, 0);
lean_inc(v_builtinName_1194_);
v___y_1118_ = v___y_1151_;
v___y_1119_ = v___y_1152_;
v___y_1120_ = v_val_1193_;
v___y_1121_ = v___y_1153_;
v___y_1122_ = v___y_1154_;
v___y_1123_ = v_builtinName_1194_;
goto v___jp_1117_;
}
}
else
{
lean_dec(v_a_1188_);
v_p_1074_ = v___x_1108_;
v___y_1075_ = v___y_1151_;
v___y_1076_ = v___y_1152_;
v___y_1077_ = v___y_1153_;
v___y_1078_ = v___y_1154_;
goto v___jp_1073_;
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec(v___x_1108_);
lean_dec(v_a_1072_);
lean_dec_ref(v_ctx_1062_);
v_a_1195_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1187_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1187_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
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
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v___x_1112_);
lean_dec(v_a_1110_);
lean_dec(v___x_1108_);
lean_dec(v_declName_1101_);
lean_dec(v_a_1072_);
lean_dec_ref(v_ctx_1062_);
v_a_1209_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1155_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1155_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
v___jp_1217_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_inc_ref(v_ctx_1062_);
v___x_1224_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_1062_, v___y_1218_);
lean_dec_ref(v___y_1218_);
lean_inc_ref(v_ctx_1062_);
v___x_1225_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1062_, v_builtin_1063_, v_force_1064_, v___x_1224_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1227_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref(v___x_1225_);
lean_inc_ref(v___x_1112_);
v___x_1227_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v___x_1112_, v___f_1116_, v___x_1113_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1279_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1279_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1279_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v_env_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1232_ = lean_st_ref_get(v___y_1223_);
v_env_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc_ref(v_env_1233_);
lean_dec(v___x_1232_);
v___x_1234_ = lean_box(0);
lean_inc(v___x_1108_);
v___x_1235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1108_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
lean_ctor_set(v___x_1235_, 2, v_a_1228_);
v___x_1236_ = lean_box(0);
v___x_1237_ = 1;
lean_inc(v___x_1108_);
v___x_1238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1108_);
lean_ctor_set(v___x_1238_, 1, v___x_1234_);
v___x_1239_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1239_, 0, v___x_1235_);
lean_ctor_set(v___x_1239_, 1, v_a_1226_);
lean_ctor_set(v___x_1239_, 2, v___x_1236_);
lean_ctor_set(v___x_1239_, 3, v___x_1238_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*4, v___x_1237_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 1);
lean_ctor_set(v___x_1230_, 0, v___x_1239_);
v___x_1241_ = v___x_1230_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
uint8_t v___x_1242_; 
lean_inc(v_declName_1101_);
v___x_1242_ = l_Lean_isMarkedMeta(v_env_1233_, v_declName_1101_);
if (v___x_1242_ == 0)
{
v___y_1149_ = v___x_1241_;
v___y_1150_ = v___y_1219_;
v___y_1151_ = v___y_1220_;
v___y_1152_ = v___y_1221_;
v___y_1153_ = v___y_1222_;
v___y_1154_ = v___y_1223_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1243_; lean_object* v_env_1244_; lean_object* v_nextMacroScope_1245_; lean_object* v_ngen_1246_; lean_object* v_auxDeclNGen_1247_; lean_object* v_traceState_1248_; lean_object* v_messages_1249_; lean_object* v_infoState_1250_; lean_object* v_snapshotTasks_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1276_; 
v___x_1243_ = lean_st_ref_take(v___y_1223_);
v_env_1244_ = lean_ctor_get(v___x_1243_, 0);
v_nextMacroScope_1245_ = lean_ctor_get(v___x_1243_, 1);
v_ngen_1246_ = lean_ctor_get(v___x_1243_, 2);
v_auxDeclNGen_1247_ = lean_ctor_get(v___x_1243_, 3);
v_traceState_1248_ = lean_ctor_get(v___x_1243_, 4);
v_messages_1249_ = lean_ctor_get(v___x_1243_, 6);
v_infoState_1250_ = lean_ctor_get(v___x_1243_, 7);
v_snapshotTasks_1251_ = lean_ctor_get(v___x_1243_, 8);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1276_ == 0)
{
lean_object* v_unused_1277_; 
v_unused_1277_ = lean_ctor_get(v___x_1243_, 5);
lean_dec(v_unused_1277_);
v___x_1253_ = v___x_1243_;
v_isShared_1254_ = v_isSharedCheck_1276_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_snapshotTasks_1251_);
lean_inc(v_infoState_1250_);
lean_inc(v_messages_1249_);
lean_inc(v_traceState_1248_);
lean_inc(v_auxDeclNGen_1247_);
lean_inc(v_ngen_1246_);
lean_inc(v_nextMacroScope_1245_);
lean_inc(v_env_1244_);
lean_dec(v___x_1243_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1276_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
lean_inc(v___x_1108_);
v___x_1255_ = l_Lean_markMeta(v_env_1244_, v___x_1108_);
v___x_1256_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 5, v___x_1256_);
lean_ctor_set(v___x_1253_, 0, v___x_1255_);
v___x_1258_ = v___x_1253_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_nextMacroScope_1245_);
lean_ctor_set(v_reuseFailAlloc_1275_, 2, v_ngen_1246_);
lean_ctor_set(v_reuseFailAlloc_1275_, 3, v_auxDeclNGen_1247_);
lean_ctor_set(v_reuseFailAlloc_1275_, 4, v_traceState_1248_);
lean_ctor_set(v_reuseFailAlloc_1275_, 5, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1275_, 6, v_messages_1249_);
lean_ctor_set(v_reuseFailAlloc_1275_, 7, v_infoState_1250_);
lean_ctor_set(v_reuseFailAlloc_1275_, 8, v_snapshotTasks_1251_);
v___x_1258_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v_mctx_1261_; lean_object* v_zetaDeltaFVarIds_1262_; lean_object* v_postponed_1263_; lean_object* v_diag_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1273_; 
v___x_1259_ = lean_st_ref_set(v___y_1223_, v___x_1258_);
v___x_1260_ = lean_st_ref_take(v___y_1221_);
v_mctx_1261_ = lean_ctor_get(v___x_1260_, 0);
v_zetaDeltaFVarIds_1262_ = lean_ctor_get(v___x_1260_, 2);
v_postponed_1263_ = lean_ctor_get(v___x_1260_, 3);
v_diag_1264_ = lean_ctor_get(v___x_1260_, 4);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v___x_1260_, 1);
lean_dec(v_unused_1274_);
v___x_1266_ = v___x_1260_;
v_isShared_1267_ = v_isSharedCheck_1273_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_diag_1264_);
lean_inc(v_postponed_1263_);
lean_inc(v_zetaDeltaFVarIds_1262_);
lean_inc(v_mctx_1261_);
lean_dec(v___x_1260_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1273_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1268_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_mctx_1261_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_zetaDeltaFVarIds_1262_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v_postponed_1263_);
lean_ctor_set(v_reuseFailAlloc_1272_, 4, v_diag_1264_);
v___x_1270_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_st_ref_set(v___y_1221_, v___x_1270_);
v___y_1149_ = v___x_1241_;
v___y_1150_ = v___y_1219_;
v___y_1151_ = v___y_1220_;
v___y_1152_ = v___y_1221_;
v___y_1153_ = v___y_1222_;
v___y_1154_ = v___y_1223_;
goto v___jp_1148_;
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
lean_dec(v_a_1226_);
lean_dec_ref(v___x_1112_);
lean_dec(v_a_1110_);
lean_dec(v___x_1108_);
lean_dec(v_declName_1101_);
lean_dec(v_a_1072_);
lean_dec_ref(v_ctx_1062_);
return v___x_1227_;
}
}
else
{
lean_dec_ref(v___f_1116_);
lean_dec_ref(v___x_1112_);
lean_dec(v_a_1110_);
lean_dec(v___x_1108_);
lean_dec(v_declName_1101_);
lean_dec(v_a_1072_);
lean_dec_ref(v_ctx_1062_);
return v___x_1225_;
}
}
v___jp_1280_:
{
if (v___y_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec_ref(v___f_1116_);
lean_dec_ref(v___x_1112_);
lean_dec(v_a_1110_);
lean_dec(v___x_1108_);
lean_dec_ref(v_env_1103_);
lean_dec(v_declName_1101_);
lean_inc(v_a_1072_);
v___x_1282_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_1072_, v___x_1113_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref(v___x_1282_);
if (lean_obj_tag(v_a_1283_) == 1)
{
lean_object* v_val_1284_; 
lean_dec(v_a_1072_);
v_val_1284_ = lean_ctor_get(v_a_1283_, 0);
lean_inc(v_val_1284_);
lean_dec_ref(v_a_1283_);
v_e_1065_ = v_val_1284_;
goto _start;
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_inc(v_varName_1104_);
lean_dec(v_a_1283_);
lean_dec_ref(v_ctx_1062_);
v___x_1286_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10);
v___x_1287_ = l_Lean_MessageData_ofName(v_varName_1104_);
v___x_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1286_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12);
v___x_1290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = l_Lean_MessageData_ofExpr(v_a_1072_);
v___x_1292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1294_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
return v___x_1295_;
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_a_1072_);
lean_dec_ref(v_ctx_1062_);
v_a_1296_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1282_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1282_);
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
lean_object* v___x_1304_; 
lean_inc(v_a_1110_);
v___x_1304_ = l_Lean_ConstantInfo_value_x3f(v_a_1110_, v___x_1113_);
if (lean_obj_tag(v___x_1304_) == 1)
{
lean_object* v_val_1305_; lean_object* v___x_1306_; 
v_val_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_val_1305_);
lean_dec_ref(v___x_1304_);
v___x_1306_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1103_, v_declName_1101_);
lean_dec_ref(v_env_1103_);
if (lean_obj_tag(v___x_1306_) == 0)
{
v___y_1218_ = v_val_1305_;
v___y_1219_ = v___y_1281_;
v___y_1220_ = v_a_1066_;
v___y_1221_ = v_a_1067_;
v___y_1222_ = v_a_1068_;
v___y_1223_ = v_a_1069_;
goto v___jp_1217_;
}
else
{
lean_dec_ref(v___x_1306_);
if (v_force_1064_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1307_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14);
lean_inc(v_declName_1101_);
v___x_1308_ = l_Lean_MessageData_ofName(v_declName_1101_);
v___x_1309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16);
v___x_1311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1309_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1311_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_dec_ref(v___x_1312_);
v___y_1218_ = v_val_1305_;
v___y_1219_ = v___y_1281_;
v___y_1220_ = v_a_1066_;
v___y_1221_ = v_a_1067_;
v___y_1222_ = v_a_1068_;
v___y_1223_ = v_a_1069_;
goto v___jp_1217_;
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v_val_1305_);
lean_dec_ref(v___f_1116_);
lean_dec_ref(v___x_1112_);
lean_dec(v_a_1110_);
lean_dec(v___x_1108_);
lean_dec(v_declName_1101_);
lean_dec(v_a_1072_);
lean_dec_ref(v_ctx_1062_);
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
v___y_1218_ = v_val_1305_;
v___y_1219_ = v___y_1281_;
v___y_1220_ = v_a_1066_;
v___y_1221_ = v_a_1067_;
v___y_1222_ = v_a_1068_;
v___y_1223_ = v_a_1069_;
goto v___jp_1217_;
}
}
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_inc(v_varName_1104_);
lean_dec(v___x_1304_);
lean_dec_ref(v___f_1116_);
lean_dec_ref(v___x_1112_);
lean_dec(v_a_1110_);
lean_dec(v___x_1108_);
lean_dec_ref(v_env_1103_);
lean_dec(v_declName_1101_);
lean_dec_ref(v_ctx_1062_);
v___x_1321_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10);
v___x_1322_ = l_Lean_MessageData_ofName(v_varName_1104_);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1321_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18);
v___x_1325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1323_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = l_Lean_MessageData_ofExpr(v_a_1072_);
v___x_1327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1325_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1329_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
return v___x_1330_;
}
}
}
}
else
{
lean_dec_ref(v___x_1112_);
lean_dec(v_a_1110_);
lean_dec(v___x_1108_);
lean_dec_ref(v_env_1103_);
lean_dec(v_declName_1101_);
lean_dec(v_a_1072_);
lean_dec_ref(v_ctx_1062_);
return v___x_1114_;
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec(v___x_1108_);
lean_dec_ref(v_env_1103_);
lean_dec(v_declName_1101_);
lean_dec(v_a_1072_);
lean_dec_ref(v_ctx_1062_);
v_a_1335_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1109_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1109_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_object* v_val_1343_; 
lean_dec_ref(v_env_1103_);
lean_dec(v_declName_1101_);
v_val_1343_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_val_1343_);
lean_dec_ref(v___x_1107_);
v_p_1074_ = v_val_1343_;
v___y_1075_ = v_a_1066_;
v___y_1076_ = v_a_1067_;
v___y_1077_ = v_a_1068_;
v___y_1078_ = v_a_1069_;
goto v___jp_1073_;
}
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_ctx_1062_);
v___x_1344_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22);
v___x_1345_ = l_Lean_MessageData_ofExpr(v_a_1072_);
v___x_1346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_1348_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
return v___x_1349_;
}
}
}
v___jp_1073_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = l_Lean_mkConst(v_p_1074_, v___x_1079_);
lean_inc(v___y_1078_);
lean_inc_ref(v___y_1077_);
lean_inc(v___y_1076_);
lean_inc_ref(v___y_1075_);
lean_inc_ref(v___x_1080_);
v___x_1081_ = lean_infer_type(v___x_1080_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___f_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref(v___x_1081_);
v___x_1083_ = lean_box(v_builtin_1063_);
v___x_1084_ = lean_box(v_force_1064_);
v___f_1085_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed), 12, 5);
lean_closure_set(v___f_1085_, 0, v_a_1072_);
lean_closure_set(v___f_1085_, 1, v_ctx_1062_);
lean_closure_set(v___f_1085_, 2, v___x_1083_);
lean_closure_set(v___f_1085_, 3, v___x_1084_);
lean_closure_set(v___f_1085_, 4, v___x_1080_);
v___x_1086_ = 0;
v___x_1087_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_1082_, v___f_1085_, v___x_1086_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
return v___x_1087_;
}
else
{
lean_dec_ref(v___x_1080_);
lean_dec(v_a_1072_);
lean_dec_ref(v_ctx_1062_);
return v___x_1081_;
}
}
}
else
{
lean_dec_ref(v_ctx_1062_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(lean_object* v_ctx_1350_, uint8_t v_builtin_1351_, uint8_t v_force_1352_, lean_object* v_x_1353_, lean_object* v_b_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1350_, v_builtin_1351_, v_force_1352_, v_b_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___boxed(lean_object* v_upperBound_1361_, lean_object* v_params_1362_, lean_object* v___x_1363_, lean_object* v_ctx_1364_, lean_object* v_builtin_1365_, lean_object* v_force_1366_, lean_object* v_a_1367_, lean_object* v_b_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
uint8_t v_builtin_boxed_1374_; uint8_t v_force_boxed_1375_; lean_object* v_res_1376_; 
v_builtin_boxed_1374_ = lean_unbox(v_builtin_1365_);
v_force_boxed_1375_ = lean_unbox(v_force_1366_);
v_res_1376_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v_upperBound_1361_, v_params_1362_, v___x_1363_, v_ctx_1364_, v_builtin_boxed_1374_, v_force_boxed_1375_, v_a_1367_, v_b_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec_ref(v___x_1363_);
lean_dec_ref(v_params_1362_);
lean_dec(v_upperBound_1361_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___redArg___boxed(lean_object* v_ctx_1377_, lean_object* v_builtin_1378_, lean_object* v_force_1379_, lean_object* v_e_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
uint8_t v_builtin_boxed_1386_; uint8_t v_force_boxed_1387_; lean_object* v_res_1388_; 
v_builtin_boxed_1386_ = lean_unbox(v_builtin_1378_);
v_force_boxed_1387_ = lean_unbox(v_force_1379_);
v_res_1388_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1377_, v_builtin_boxed_1386_, v_force_boxed_1387_, v_e_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr(lean_object* v_00_u03b1_1389_, lean_object* v_ctx_1390_, uint8_t v_builtin_1391_, uint8_t v_force_1392_, lean_object* v_e_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1390_, v_builtin_1391_, v_force_1392_, v_e_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileParserExpr___boxed(lean_object* v_00_u03b1_1400_, lean_object* v_ctx_1401_, lean_object* v_builtin_1402_, lean_object* v_force_1403_, lean_object* v_e_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
uint8_t v_builtin_boxed_1410_; uint8_t v_force_boxed_1411_; lean_object* v_res_1412_; 
v_builtin_boxed_1410_ = lean_unbox(v_builtin_1402_);
v_force_boxed_1411_ = lean_unbox(v_force_1403_);
v_res_1412_ = l_Lean_ParserCompiler_compileParserExpr(v_00_u03b1_1400_, v_ctx_1401_, v_builtin_boxed_1410_, v_force_boxed_1411_, v_e_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(lean_object* v_00_u03b1_1413_, lean_object* v_ctx_1414_, lean_object* v_as_1415_, size_t v_i_1416_, size_t v_stop_1417_, lean_object* v_b_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_1414_, v_as_1415_, v_i_1416_, v_stop_1417_, v_b_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___boxed(lean_object* v_00_u03b1_1425_, lean_object* v_ctx_1426_, lean_object* v_as_1427_, lean_object* v_i_1428_, lean_object* v_stop_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
size_t v_i_boxed_1436_; size_t v_stop_boxed_1437_; lean_object* v_res_1438_; 
v_i_boxed_1436_ = lean_unbox_usize(v_i_1428_);
lean_dec(v_i_1428_);
v_stop_boxed_1437_ = lean_unbox_usize(v_stop_1429_);
lean_dec(v_stop_1429_);
v_res_1438_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(v_00_u03b1_1425_, v_ctx_1426_, v_as_1427_, v_i_boxed_1436_, v_stop_boxed_1437_, v_b_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec_ref(v_as_1427_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(lean_object* v_upperBound_1439_, lean_object* v_params_1440_, lean_object* v___x_1441_, lean_object* v_00_u03b1_1442_, lean_object* v_ctx_1443_, uint8_t v_builtin_1444_, uint8_t v_force_1445_, lean_object* v_inst_1446_, lean_object* v_R_1447_, lean_object* v_a_1448_, lean_object* v_b_1449_, lean_object* v_c_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v_upperBound_1439_, v_params_1440_, v___x_1441_, v_ctx_1443_, v_builtin_1444_, v_force_1445_, v_a_1448_, v_b_1449_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1457_ = _args[0];
lean_object* v_params_1458_ = _args[1];
lean_object* v___x_1459_ = _args[2];
lean_object* v_00_u03b1_1460_ = _args[3];
lean_object* v_ctx_1461_ = _args[4];
lean_object* v_builtin_1462_ = _args[5];
lean_object* v_force_1463_ = _args[6];
lean_object* v_inst_1464_ = _args[7];
lean_object* v_R_1465_ = _args[8];
lean_object* v_a_1466_ = _args[9];
lean_object* v_b_1467_ = _args[10];
lean_object* v_c_1468_ = _args[11];
lean_object* v___y_1469_ = _args[12];
lean_object* v___y_1470_ = _args[13];
lean_object* v___y_1471_ = _args[14];
lean_object* v___y_1472_ = _args[15];
lean_object* v___y_1473_ = _args[16];
_start:
{
uint8_t v_builtin_boxed_1474_; uint8_t v_force_boxed_1475_; lean_object* v_res_1476_; 
v_builtin_boxed_1474_ = lean_unbox(v_builtin_1462_);
v_force_boxed_1475_ = lean_unbox(v_force_1463_);
v_res_1476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(v_upperBound_1457_, v_params_1458_, v___x_1459_, v_00_u03b1_1460_, v_ctx_1461_, v_builtin_boxed_1474_, v_force_boxed_1475_, v_inst_1464_, v_R_1465_, v_a_1466_, v_b_1467_, v_c_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec_ref(v___x_1459_);
lean_dec_ref(v_params_1458_);
lean_dec(v_upperBound_1457_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4(lean_object* v_00_u03b1_1477_, lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v_msg_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___boxed(lean_object* v_00_u03b1_1485_, lean_object* v_msg_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4(v_00_u03b1_1485_, v_msg_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(lean_object* v_00_u03b1_1493_, lean_object* v_constName_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1501_, lean_object* v_constName_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(v_00_u03b1_1501_, v_constName_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_1509_, lean_object* v_ref_1510_, lean_object* v_constName_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_1510_, v_constName_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1518_, lean_object* v_ref_1519_, lean_object* v_constName_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(v_00_u03b1_1518_, v_ref_1519_, v_constName_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v_ref_1519_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7(lean_object* v_00_u03b1_1527_, lean_object* v_ref_1528_, lean_object* v_msg_1529_, lean_object* v_declHint_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_1528_, v_msg_1529_, v_declHint_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_ref_1538_, lean_object* v_msg_1539_, lean_object* v_declHint_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7(v_00_u03b1_1537_, v_ref_1538_, v_msg_1539_, v_declHint_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_ref_1538_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* v_msg_1547_, lean_object* v_declHint_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_1547_, v_declHint_1548_, v___y_1552_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_1555_, lean_object* v_declHint_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_1555_, v_declHint_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_1563_, lean_object* v_ref_1564_, lean_object* v_msg_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_1564_, v_msg_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1572_, lean_object* v_ref_1573_, lean_object* v_msg_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_1572_, v_ref_1573_, v_msg_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v_ref_1573_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(lean_object* v_ctx_1581_, uint8_t v_builtin_1582_, lean_object* v_x_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_p_1590_; lean_object* v_psep_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; 
switch(lean_obj_tag(v_x_1583_))
{
case 1:
{
lean_object* v_p_1598_; 
v_p_1598_ = lean_ctor_get(v_x_1583_, 1);
lean_inc_ref(v_p_1598_);
lean_dec_ref(v_x_1583_);
v_x_1583_ = v_p_1598_;
goto _start;
}
case 2:
{
lean_object* v_p_u2081_1600_; lean_object* v_p_u2082_1601_; lean_object* v___x_1602_; 
v_p_u2081_1600_ = lean_ctor_get(v_x_1583_, 1);
lean_inc_ref(v_p_u2081_1600_);
v_p_u2082_1601_ = lean_ctor_get(v_x_1583_, 2);
lean_inc_ref(v_p_u2082_1601_);
lean_dec_ref(v_x_1583_);
lean_inc_ref(v_ctx_1581_);
v___x_1602_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1581_, v_builtin_1582_, v_p_u2081_1600_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_dec_ref(v___x_1602_);
v_x_1583_ = v_p_u2082_1601_;
goto _start;
}
else
{
lean_dec_ref(v_p_u2082_1601_);
lean_dec_ref(v_ctx_1581_);
return v___x_1602_;
}
}
case 3:
{
lean_object* v_p_1604_; 
v_p_1604_ = lean_ctor_get(v_x_1583_, 2);
lean_inc_ref(v_p_1604_);
lean_dec_ref(v_x_1583_);
v_x_1583_ = v_p_1604_;
goto _start;
}
case 4:
{
lean_object* v_p_1606_; 
v_p_1606_ = lean_ctor_get(v_x_1583_, 3);
lean_inc_ref(v_p_1606_);
lean_dec_ref(v_x_1583_);
v_x_1583_ = v_p_1606_;
goto _start;
}
case 8:
{
lean_object* v_declName_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_declName_1608_ = lean_ctor_get(v_x_1583_, 0);
lean_inc(v_declName_1608_);
lean_dec_ref(v_x_1583_);
v___x_1609_ = 0;
v___x_1610_ = lean_box(0);
v___x_1611_ = l_Lean_mkConst(v_declName_1608_, v___x_1610_);
v___x_1612_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1581_, v_builtin_1582_, v___x_1609_, v___x_1611_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1620_; 
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; 
v_unused_1621_ = lean_ctor_get(v___x_1612_, 0);
lean_dec(v_unused_1621_);
v___x_1614_ = v___x_1612_;
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
else
{
lean_dec(v___x_1612_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1616_ = lean_box(0);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1616_);
v___x_1618_ = v___x_1614_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1612_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1612_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
case 9:
{
lean_object* v_p_1630_; 
v_p_1630_ = lean_ctor_get(v_x_1583_, 2);
lean_inc_ref(v_p_1630_);
lean_dec_ref(v_x_1583_);
v_x_1583_ = v_p_1630_;
goto _start;
}
case 10:
{
lean_object* v_p_1632_; lean_object* v_psep_1633_; 
v_p_1632_ = lean_ctor_get(v_x_1583_, 0);
lean_inc_ref(v_p_1632_);
v_psep_1633_ = lean_ctor_get(v_x_1583_, 2);
lean_inc_ref(v_psep_1633_);
lean_dec_ref(v_x_1583_);
v_p_1590_ = v_p_1632_;
v_psep_1591_ = v_psep_1633_;
v___y_1592_ = v_a_1584_;
v___y_1593_ = v_a_1585_;
v___y_1594_ = v_a_1586_;
v___y_1595_ = v_a_1587_;
goto v___jp_1589_;
}
case 11:
{
lean_object* v_p_1634_; lean_object* v_psep_1635_; 
v_p_1634_ = lean_ctor_get(v_x_1583_, 0);
lean_inc_ref(v_p_1634_);
v_psep_1635_ = lean_ctor_get(v_x_1583_, 2);
lean_inc_ref(v_psep_1635_);
lean_dec_ref(v_x_1583_);
v_p_1590_ = v_p_1634_;
v_psep_1591_ = v_psep_1635_;
v___y_1592_ = v_a_1584_;
v___y_1593_ = v_a_1585_;
v___y_1594_ = v_a_1586_;
v___y_1595_ = v_a_1587_;
goto v___jp_1589_;
}
default: 
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec_ref(v_x_1583_);
lean_dec_ref(v_ctx_1581_);
v___x_1636_ = lean_box(0);
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
return v___x_1637_;
}
}
v___jp_1589_:
{
lean_object* v___x_1596_; 
lean_inc_ref(v_ctx_1581_);
v___x_1596_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1581_, v_builtin_1582_, v_p_1590_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_dec_ref(v___x_1596_);
v_x_1583_ = v_psep_1591_;
v_a_1584_ = v___y_1592_;
v_a_1585_ = v___y_1593_;
v_a_1586_ = v___y_1594_;
v_a_1587_ = v___y_1595_;
goto _start;
}
else
{
lean_dec_ref(v_psep_1591_);
lean_dec_ref(v_ctx_1581_);
return v___x_1596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___redArg___boxed(lean_object* v_ctx_1638_, lean_object* v_builtin_1639_, lean_object* v_x_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
uint8_t v_builtin_boxed_1646_; lean_object* v_res_1647_; 
v_builtin_boxed_1646_ = lean_unbox(v_builtin_1639_);
v_res_1647_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1638_, v_builtin_boxed_1646_, v_x_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers(lean_object* v_00_u03b1_1648_, lean_object* v_ctx_1649_, uint8_t v_builtin_1650_, lean_object* v_x_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1649_, v_builtin_1650_, v_x_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_compileEmbeddedParsers___boxed(lean_object* v_00_u03b1_1658_, lean_object* v_ctx_1659_, lean_object* v_builtin_1660_, lean_object* v_x_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
uint8_t v_builtin_boxed_1667_; lean_object* v_res_1668_; 
v_builtin_boxed_1667_ = lean_unbox(v_builtin_1660_);
v_res_1668_ = l_Lean_ParserCompiler_compileEmbeddedParsers(v_00_u03b1_1658_, v_ctx_1659_, v_builtin_boxed_1667_, v_x_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
return v_res_1668_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = l_Lean_Elab_abortCommandExceptionId;
v___x_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg(){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___boxed(lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(lean_object* v_msgData_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v_env_1682_; lean_object* v_options_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1681_ = lean_st_ref_get(v___y_1679_);
v_env_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc_ref(v_env_1682_);
lean_dec(v___x_1681_);
v_options_1683_ = lean_ctor_get(v___y_1678_, 2);
v___x_1684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1685_ = lean_unsigned_to_nat(32u);
v___x_1686_ = lean_mk_empty_array_with_capacity(v___x_1685_);
lean_dec_ref(v___x_1686_);
v___x_1687_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
lean_inc_ref(v_options_1683_);
v___x_1688_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1688_, 0, v_env_1682_);
lean_ctor_set(v___x_1688_, 1, v___x_1684_);
lean_ctor_set(v___x_1688_, 2, v___x_1687_);
lean_ctor_set(v___x_1688_, 3, v_options_1683_);
v___x_1689_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v_msgData_1677_);
v___x_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9___boxed(lean_object* v_msgData_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(v_msgData_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(lean_object* v_msg_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_ref_1700_; lean_object* v___x_1701_; lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1710_; 
v_ref_1700_ = lean_ctor_get(v___y_1697_, 5);
v___x_1701_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(v_msg_1696_, v___y_1697_, v___y_1698_);
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
lean_inc(v_ref_1700_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_ref_1700_);
lean_ctor_set(v___x_1706_, 1, v_a_1702_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set_tag(v___x_1704_, 1);
lean_ctor_set(v___x_1704_, 0, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msg_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(lean_object* v_x_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
if (lean_obj_tag(v_x_1716_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_a_1720_ = lean_ctor_get(v_x_1716_, 0);
lean_inc(v_a_1720_);
lean_dec_ref(v_x_1716_);
v___x_1721_ = l_Lean_stringToMessageData(v_a_1720_);
v___x_1722_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v___x_1721_, v___y_1717_, v___y_1718_);
return v___x_1722_;
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
v_a_1723_ = lean_ctor_get(v_x_1716_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_x_1716_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v_x_1716_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v_x_1716_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set_tag(v___x_1725_, 0);
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg___boxed(lean_object* v_x_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v_x_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(lean_object* v_typeName_1736_, lean_object* v_constName_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___x_1741_; lean_object* v_env_1742_; uint8_t v___x_1743_; 
v___x_1741_ = lean_st_ref_get(v___y_1739_);
v_env_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc_ref(v_env_1742_);
lean_dec(v___x_1741_);
lean_inc(v_constName_1737_);
v___x_1743_ = lean_has_compile_error(v_env_1742_, v_constName_1737_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v_env_1745_; lean_object* v_options_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1744_ = lean_st_ref_get(v___y_1739_);
v_env_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc_ref(v_env_1745_);
lean_dec(v___x_1744_);
v_options_1746_ = lean_ctor_get(v___y_1738_, 2);
v___x_1747_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1745_, v_options_1746_, v_typeName_1736_, v_constName_1737_);
v___x_1748_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v___x_1747_, v___y_1738_, v___y_1739_);
return v___x_1748_;
}
else
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v___x_1750_; lean_object* v_env_1751_; lean_object* v_options_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec_ref(v___x_1749_);
v___x_1750_ = lean_st_ref_get(v___y_1739_);
v_env_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc_ref(v_env_1751_);
lean_dec(v___x_1750_);
v_options_1752_ = lean_ctor_get(v___y_1738_, 2);
v___x_1753_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1751_, v_options_1752_, v_typeName_1736_, v_constName_1737_);
v___x_1754_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v___x_1753_, v___y_1738_, v___y_1739_);
return v___x_1754_;
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec(v_constName_1737_);
lean_dec(v_typeName_1736_);
v_a_1755_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1749_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1749_);
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
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg___boxed(lean_object* v_typeName_1763_, lean_object* v_constName_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v_typeName_1763_, v_constName_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(lean_object* v_ref_1769_, lean_object* v_msg_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_fileName_1774_; lean_object* v_fileMap_1775_; lean_object* v_options_1776_; lean_object* v_currRecDepth_1777_; lean_object* v_maxRecDepth_1778_; lean_object* v_ref_1779_; lean_object* v_currNamespace_1780_; lean_object* v_openDecls_1781_; lean_object* v_initHeartbeats_1782_; lean_object* v_maxHeartbeats_1783_; lean_object* v_quotContext_1784_; lean_object* v_currMacroScope_1785_; uint8_t v_diag_1786_; lean_object* v_cancelTk_x3f_1787_; uint8_t v_suppressElabErrors_1788_; lean_object* v_inheritedTraceOptions_1789_; lean_object* v_ref_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v_fileName_1774_ = lean_ctor_get(v___y_1771_, 0);
v_fileMap_1775_ = lean_ctor_get(v___y_1771_, 1);
v_options_1776_ = lean_ctor_get(v___y_1771_, 2);
v_currRecDepth_1777_ = lean_ctor_get(v___y_1771_, 3);
v_maxRecDepth_1778_ = lean_ctor_get(v___y_1771_, 4);
v_ref_1779_ = lean_ctor_get(v___y_1771_, 5);
v_currNamespace_1780_ = lean_ctor_get(v___y_1771_, 6);
v_openDecls_1781_ = lean_ctor_get(v___y_1771_, 7);
v_initHeartbeats_1782_ = lean_ctor_get(v___y_1771_, 8);
v_maxHeartbeats_1783_ = lean_ctor_get(v___y_1771_, 9);
v_quotContext_1784_ = lean_ctor_get(v___y_1771_, 10);
v_currMacroScope_1785_ = lean_ctor_get(v___y_1771_, 11);
v_diag_1786_ = lean_ctor_get_uint8(v___y_1771_, sizeof(void*)*14);
v_cancelTk_x3f_1787_ = lean_ctor_get(v___y_1771_, 12);
v_suppressElabErrors_1788_ = lean_ctor_get_uint8(v___y_1771_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1789_ = lean_ctor_get(v___y_1771_, 13);
v_ref_1790_ = l_Lean_replaceRef(v_ref_1769_, v_ref_1779_);
lean_inc_ref(v_inheritedTraceOptions_1789_);
lean_inc(v_cancelTk_x3f_1787_);
lean_inc(v_currMacroScope_1785_);
lean_inc(v_quotContext_1784_);
lean_inc(v_maxHeartbeats_1783_);
lean_inc(v_initHeartbeats_1782_);
lean_inc(v_openDecls_1781_);
lean_inc(v_currNamespace_1780_);
lean_inc(v_maxRecDepth_1778_);
lean_inc(v_currRecDepth_1777_);
lean_inc_ref(v_options_1776_);
lean_inc_ref(v_fileMap_1775_);
lean_inc_ref(v_fileName_1774_);
v___x_1791_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1791_, 0, v_fileName_1774_);
lean_ctor_set(v___x_1791_, 1, v_fileMap_1775_);
lean_ctor_set(v___x_1791_, 2, v_options_1776_);
lean_ctor_set(v___x_1791_, 3, v_currRecDepth_1777_);
lean_ctor_set(v___x_1791_, 4, v_maxRecDepth_1778_);
lean_ctor_set(v___x_1791_, 5, v_ref_1790_);
lean_ctor_set(v___x_1791_, 6, v_currNamespace_1780_);
lean_ctor_set(v___x_1791_, 7, v_openDecls_1781_);
lean_ctor_set(v___x_1791_, 8, v_initHeartbeats_1782_);
lean_ctor_set(v___x_1791_, 9, v_maxHeartbeats_1783_);
lean_ctor_set(v___x_1791_, 10, v_quotContext_1784_);
lean_ctor_set(v___x_1791_, 11, v_currMacroScope_1785_);
lean_ctor_set(v___x_1791_, 12, v_cancelTk_x3f_1787_);
lean_ctor_set(v___x_1791_, 13, v_inheritedTraceOptions_1789_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*14, v_diag_1786_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*14 + 1, v_suppressElabErrors_1788_);
v___x_1792_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_1770_, v___x_1791_, v___y_1772_);
lean_dec_ref(v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg___boxed(lean_object* v_ref_1793_, lean_object* v_msg_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_1793_, v_msg_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v_ref_1793_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(lean_object* v_msg_1799_, lean_object* v_declHint_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; lean_object* v_env_1804_; uint8_t v___x_1805_; 
v___x_1803_ = lean_st_ref_get(v___y_1801_);
v_env_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc_ref(v_env_1804_);
lean_dec(v___x_1803_);
v___x_1805_ = l_Lean_Name_isAnonymous(v_declHint_1800_);
if (v___x_1805_ == 0)
{
uint8_t v_isExporting_1806_; 
v_isExporting_1806_ = lean_ctor_get_uint8(v_env_1804_, sizeof(void*)*8);
if (v_isExporting_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v_env_1804_);
lean_dec(v_declHint_1800_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_msg_1799_);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
lean_inc_ref(v_env_1804_);
v___x_1808_ = l_Lean_Environment_setExporting(v_env_1804_, v___x_1805_);
lean_inc(v_declHint_1800_);
lean_inc_ref(v___x_1808_);
v___x_1809_ = l_Lean_Environment_contains(v___x_1808_, v_declHint_1800_, v_isExporting_1806_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; 
lean_dec_ref(v___x_1808_);
lean_dec_ref(v_env_1804_);
lean_dec(v_declHint_1800_);
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_msg_1799_);
return v___x_1810_;
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v_c_1818_; lean_object* v___x_1819_; 
v___x_1811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
v___x_1812_ = lean_unsigned_to_nat(32u);
v___x_1813_ = lean_mk_empty_array_with_capacity(v___x_1812_);
lean_dec_ref(v___x_1813_);
v___x_1814_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
v___x_1815_ = l_Lean_Options_empty;
v___x_1816_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1808_);
lean_ctor_set(v___x_1816_, 1, v___x_1811_);
lean_ctor_set(v___x_1816_, 2, v___x_1814_);
lean_ctor_set(v___x_1816_, 3, v___x_1815_);
lean_inc(v_declHint_1800_);
v___x_1817_ = l_Lean_MessageData_ofConstName(v_declHint_1800_, v___x_1805_);
v_c_1818_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1818_, 0, v___x_1816_);
lean_ctor_set(v_c_1818_, 1, v___x_1817_);
v___x_1819_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1804_, v_declHint_1800_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_dec_ref(v_env_1804_);
lean_dec(v_declHint_1800_);
v___x_1820_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
lean_ctor_set(v___x_1821_, 1, v_c_1818_);
v___x_1822_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = l_Lean_MessageData_note(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_msg_1799_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
else
{
lean_object* v_val_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1862_; 
v_val_1827_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1829_ = v___x_1819_;
v_isShared_1830_ = v_isSharedCheck_1862_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_val_1827_);
lean_dec(v___x_1819_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1862_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v_mod_1834_; uint8_t v___x_1835_; 
v___x_1831_ = lean_box(0);
v___x_1832_ = l_Lean_Environment_header(v_env_1804_);
lean_dec_ref(v_env_1804_);
v___x_1833_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1832_);
v_mod_1834_ = lean_array_get(v___x_1831_, v___x_1833_, v_val_1827_);
lean_dec(v_val_1827_);
lean_dec_ref(v___x_1833_);
v___x_1835_ = l_Lean_isPrivateName(v_declHint_1800_);
lean_dec(v_declHint_1800_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1836_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
lean_ctor_set(v___x_1837_, 1, v_c_1818_);
v___x_1838_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_MessageData_ofName(v_mod_1834_);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = l_Lean_MessageData_note(v___x_1843_);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_msg_1799_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set_tag(v___x_1829_, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1845_);
v___x_1847_ = v___x_1829_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1849_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v_c_1818_);
v___x_1851_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Lean_MessageData_ofName(v_mod_1834_);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19);
v___x_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = l_Lean_MessageData_note(v___x_1856_);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v_msg_1799_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set_tag(v___x_1829_, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1858_);
v___x_1860_ = v___x_1829_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1863_; 
lean_dec_ref(v_env_1804_);
lean_dec(v_declHint_1800_);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_msg_1799_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg___boxed(lean_object* v_msg_1864_, lean_object* v_declHint_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_1864_, v_declHint_1865_, v___y_1866_);
lean_dec(v___y_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(lean_object* v_msg_1869_, lean_object* v_declHint_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1884_; 
v___x_1874_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_1869_, v_declHint_1870_, v___y_1872_);
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1884_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1884_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1879_ = l_Lean_unknownIdentifierMessageTag;
v___x_1880_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set(v___x_1880_, 1, v_a_1875_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1880_);
v___x_1882_ = v___x_1877_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8___boxed(lean_object* v_msg_1885_, lean_object* v_declHint_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_1885_, v_declHint_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_ref_1891_, lean_object* v_msg_1892_, lean_object* v_declHint_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; lean_object* v_a_1898_; lean_object* v___x_1899_; 
v___x_1897_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_1892_, v_declHint_1893_, v___y_1894_, v___y_1895_);
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref(v___x_1897_);
v___x_1899_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_1891_, v_a_1898_, v___y_1894_, v___y_1895_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_ref_1900_, lean_object* v_msg_1901_, lean_object* v_declHint_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1900_, v_msg_1901_, v_declHint_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v_ref_1900_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1907_, lean_object* v_constName_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; uint8_t v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1912_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1);
v___x_1913_ = 0;
lean_inc(v_constName_1908_);
v___x_1914_ = l_Lean_MessageData_ofConstName(v_constName_1908_, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1912_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1907_, v___x_1917_, v_constName_1908_, v___y_1909_, v___y_1910_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1919_, lean_object* v_constName_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_1919_, v_constName_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v_ref_1919_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(lean_object* v_constName_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_ref_1929_; lean_object* v___x_1930_; 
v_ref_1929_ = lean_ctor_get(v___y_1926_, 5);
v___x_1930_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_1929_, v_constName_1925_, v___y_1926_, v___y_1927_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(lean_object* v_constName_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; lean_object* v_env_1941_; uint8_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1940_ = lean_st_ref_get(v___y_1938_);
v_env_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc_ref(v_env_1941_);
lean_dec(v___x_1940_);
v___x_1942_ = 0;
lean_inc(v_constName_1936_);
v___x_1943_ = l_Lean_Environment_find_x3f(v_env_1941_, v_constName_1936_, v___x_1942_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_1936_, v___y_1937_, v___y_1938_);
return v___x_1944_;
}
else
{
lean_object* v_val_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v_constName_1936_);
v_val_1945_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1943_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_val_1945_);
lean_dec(v___x_1943_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set_tag(v___x_1947_, 0);
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_val_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0___boxed(lean_object* v_constName_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(v_constName_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1957_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1958_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0);
v___x_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1961_ = lean_box(1);
v___x_1962_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1963_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
lean_ctor_set(v___x_1964_, 1, v___x_1962_);
lean_ctor_set(v___x_1964_, 2, v___x_1961_);
return v___x_1964_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1968_ = lean_unsigned_to_nat(0u);
v___x_1969_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
lean_ctor_set(v___x_1969_, 2, v___x_1968_);
lean_ctor_set(v___x_1969_, 3, v___x_1967_);
lean_ctor_set(v___x_1969_, 4, v___x_1967_);
lean_ctor_set(v___x_1969_, 5, v___x_1967_);
lean_ctor_set(v___x_1969_, 6, v___x_1967_);
lean_ctor_set(v___x_1969_, 7, v___x_1967_);
lean_ctor_set(v___x_1969_, 8, v___x_1967_);
return v___x_1969_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1971_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
lean_ctor_set(v___x_1971_, 2, v___x_1970_);
lean_ctor_set(v___x_1971_, 3, v___x_1970_);
lean_ctor_set(v___x_1971_, 4, v___x_1970_);
lean_ctor_set(v___x_1971_, 5, v___x_1970_);
return v___x_1971_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1);
v___x_1973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
lean_ctor_set(v___x_1973_, 2, v___x_1972_);
lean_ctor_set(v___x_1973_, 3, v___x_1972_);
lean_ctor_set(v___x_1973_, 4, v___x_1972_);
return v___x_1973_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1974_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6);
v___x_1975_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
v___x_1976_ = lean_box(1);
v___x_1977_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5);
v___x_1978_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4);
v___x_1979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v___x_1977_);
lean_ctor_set(v___x_1979_, 2, v___x_1976_);
lean_ctor_set(v___x_1979_, 3, v___x_1975_);
lean_ctor_set(v___x_1979_, 4, v___x_1974_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(lean_object* v_constName_1988_, lean_object* v_ctx_1989_, uint8_t v_builtin_1990_, lean_object* v_catName_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
uint8_t v___y_1996_; uint8_t v___y_1997_; lean_object* v___y_1998_; lean_object* v___x_2033_; 
lean_inc(v_constName_1988_);
v___x_2033_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(v_constName_1988_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; lean_object* v___y_2037_; uint8_t v___y_2038_; uint8_t v___y_2039_; uint8_t v___y_2040_; lean_object* v___x_2043_; uint8_t v___y_2045_; uint8_t v___x_2095_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v___x_2035_ = l_Lean_ConstantInfo_type(v_a_2034_);
lean_dec(v_a_2034_);
v___x_2043_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11));
v___x_2095_ = l_Lean_Expr_isConstOf(v___x_2035_, v___x_2043_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9));
v___x_2097_ = l_Lean_Expr_isConstOf(v___x_2035_, v___x_2096_);
lean_dec_ref(v___x_2035_);
v___y_2045_ = v___x_2097_;
goto v___jp_2044_;
}
else
{
lean_dec_ref(v___x_2035_);
v___y_2045_ = v___x_2095_;
goto v___jp_2044_;
}
v___jp_2036_:
{
if (v___y_2040_ == 0)
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
lean_dec_ref(v___y_2037_);
v___x_2041_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9));
v___x_2042_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v___x_2041_, v_constName_1988_, v___y_1992_, v___y_1993_);
v___y_1996_ = v___y_2038_;
v___y_1997_ = v___y_2039_;
v___y_1998_ = v___x_2042_;
goto v___jp_1995_;
}
else
{
lean_dec(v_constName_1988_);
v___y_1996_ = v___y_2038_;
v___y_1997_ = v___y_2039_;
v___y_1998_ = v___y_2037_;
goto v___jp_1995_;
}
}
v___jp_2044_:
{
uint8_t v___x_2046_; 
v___x_2046_ = 1;
if (v___y_2045_ == 0)
{
uint8_t v___x_2047_; uint8_t v___x_2048_; uint8_t v___x_2049_; lean_object* v___x_2050_; uint64_t v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2047_ = 1;
v___x_2048_ = 0;
v___x_2049_ = 2;
v___x_2050_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2050_, 0, v___y_2045_);
lean_ctor_set_uint8(v___x_2050_, 1, v___y_2045_);
lean_ctor_set_uint8(v___x_2050_, 2, v___y_2045_);
lean_ctor_set_uint8(v___x_2050_, 3, v___y_2045_);
lean_ctor_set_uint8(v___x_2050_, 4, v___y_2045_);
lean_ctor_set_uint8(v___x_2050_, 5, v___x_2046_);
lean_ctor_set_uint8(v___x_2050_, 6, v___x_2046_);
lean_ctor_set_uint8(v___x_2050_, 7, v___y_2045_);
lean_ctor_set_uint8(v___x_2050_, 8, v___x_2046_);
lean_ctor_set_uint8(v___x_2050_, 9, v___x_2047_);
lean_ctor_set_uint8(v___x_2050_, 10, v___x_2048_);
lean_ctor_set_uint8(v___x_2050_, 11, v___x_2046_);
lean_ctor_set_uint8(v___x_2050_, 12, v___x_2046_);
lean_ctor_set_uint8(v___x_2050_, 13, v___x_2046_);
lean_ctor_set_uint8(v___x_2050_, 14, v___x_2049_);
lean_ctor_set_uint8(v___x_2050_, 15, v___x_2046_);
lean_ctor_set_uint8(v___x_2050_, 16, v___x_2046_);
lean_ctor_set_uint8(v___x_2050_, 17, v___x_2046_);
lean_ctor_set_uint8(v___x_2050_, 18, v___x_2046_);
v___x_2051_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2050_);
v___x_2052_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
lean_ctor_set_uint64(v___x_2052_, sizeof(void*)*1, v___x_2051_);
v___x_2053_ = lean_box(1);
v___x_2054_ = lean_unsigned_to_nat(0u);
v___x_2055_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2);
v___x_2056_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3));
v___x_2057_ = lean_box(0);
v___x_2058_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2058_, 0, v___x_2052_);
lean_ctor_set(v___x_2058_, 1, v___x_2053_);
lean_ctor_set(v___x_2058_, 2, v___x_2055_);
lean_ctor_set(v___x_2058_, 3, v___x_2056_);
lean_ctor_set(v___x_2058_, 4, v___x_2057_);
lean_ctor_set(v___x_2058_, 5, v___x_2054_);
lean_ctor_set(v___x_2058_, 6, v___x_2057_);
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*7, v___y_2045_);
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*7 + 1, v___y_2045_);
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*7 + 2, v___y_2045_);
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*7 + 3, v___x_2046_);
v___x_2059_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7);
v___x_2060_ = lean_st_mk_ref(v___x_2059_);
v___x_2061_ = l_Lean_Name_isAnonymous(v_catName_1991_);
v___x_2062_ = lean_box(0);
v___x_2063_ = l_Lean_mkConst(v_constName_1988_, v___x_2062_);
v___x_2064_ = lean_box(0);
v___x_2065_ = l_Lean_ParserCompiler_compileParserExpr___redArg(v_ctx_1989_, v_builtin_1990_, v___x_2061_, v___x_2063_, v___x_2058_, v___x_2060_, v___y_1992_, v___y_1993_);
lean_dec_ref(v___x_2058_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2073_; 
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v___x_2065_, 0);
lean_dec(v_unused_2074_);
v___x_2067_ = v___x_2065_;
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
else
{
lean_dec(v___x_2065_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2073_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2069_ = lean_st_ref_get(v___x_2060_);
lean_dec(v___x_2060_);
lean_dec(v___x_2069_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2064_);
v___x_2071_ = v___x_2067_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2064_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
lean_dec(v___x_2060_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v___x_2065_, 0);
lean_dec(v_unused_2082_);
v___x_2076_ = v___x_2065_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_dec(v___x_2065_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set_tag(v___x_2076_, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2064_);
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2064_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
v_a_2083_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2065_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2065_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
else
{
lean_object* v___x_2091_; 
lean_inc(v_constName_1988_);
v___x_2091_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v___x_2043_, v_constName_1988_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_dec(v_constName_1988_);
v___y_1996_ = v___y_2045_;
v___y_1997_ = v___x_2046_;
v___y_1998_ = v___x_2091_;
goto v___jp_1995_;
}
else
{
lean_object* v_a_2092_; uint8_t v___x_2093_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
v___x_2093_ = l_Lean_Exception_isInterrupt(v_a_2092_);
if (v___x_2093_ == 0)
{
uint8_t v___x_2094_; 
v___x_2094_ = l_Lean_Exception_isRuntime(v_a_2092_);
v___y_2037_ = v___x_2091_;
v___y_2038_ = v___y_2045_;
v___y_2039_ = v___x_2046_;
v___y_2040_ = v___x_2094_;
goto v___jp_2036_;
}
else
{
lean_dec(v_a_2092_);
v___y_2037_ = v___x_2091_;
v___y_2038_ = v___y_2045_;
v___y_2039_ = v___x_2046_;
v___y_2040_ = v___x_2093_;
goto v___jp_2036_;
}
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec_ref(v_ctx_1989_);
lean_dec(v_constName_1988_);
v_a_2098_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2033_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2033_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
v___jp_1995_:
{
if (lean_obj_tag(v___y_1998_) == 0)
{
lean_object* v_a_1999_; uint8_t v___x_2000_; uint8_t v___x_2001_; uint8_t v___x_2002_; uint8_t v___x_2003_; lean_object* v___x_2004_; uint64_t v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v_a_1999_ = lean_ctor_get(v___y_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref(v___y_1998_);
v___x_2000_ = 0;
v___x_2001_ = 1;
v___x_2002_ = 0;
v___x_2003_ = 2;
v___x_2004_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_2004_, 0, v___x_2000_);
lean_ctor_set_uint8(v___x_2004_, 1, v___x_2000_);
lean_ctor_set_uint8(v___x_2004_, 2, v___x_2000_);
lean_ctor_set_uint8(v___x_2004_, 3, v___x_2000_);
lean_ctor_set_uint8(v___x_2004_, 4, v___x_2000_);
lean_ctor_set_uint8(v___x_2004_, 5, v___y_1996_);
lean_ctor_set_uint8(v___x_2004_, 6, v___y_1996_);
lean_ctor_set_uint8(v___x_2004_, 7, v___x_2000_);
lean_ctor_set_uint8(v___x_2004_, 8, v___y_1996_);
lean_ctor_set_uint8(v___x_2004_, 9, v___x_2001_);
lean_ctor_set_uint8(v___x_2004_, 10, v___x_2002_);
lean_ctor_set_uint8(v___x_2004_, 11, v___y_1996_);
lean_ctor_set_uint8(v___x_2004_, 12, v___y_1996_);
lean_ctor_set_uint8(v___x_2004_, 13, v___y_1996_);
lean_ctor_set_uint8(v___x_2004_, 14, v___x_2003_);
lean_ctor_set_uint8(v___x_2004_, 15, v___y_1996_);
lean_ctor_set_uint8(v___x_2004_, 16, v___y_1996_);
lean_ctor_set_uint8(v___x_2004_, 17, v___y_1996_);
lean_ctor_set_uint8(v___x_2004_, 18, v___y_1996_);
v___x_2005_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2004_);
v___x_2006_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2006_, 0, v___x_2004_);
lean_ctor_set_uint64(v___x_2006_, sizeof(void*)*1, v___x_2005_);
v___x_2007_ = lean_box(1);
v___x_2008_ = lean_unsigned_to_nat(0u);
v___x_2009_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2);
v___x_2010_ = ((lean_object*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3));
v___x_2011_ = lean_box(0);
v___x_2012_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2012_, 0, v___x_2006_);
lean_ctor_set(v___x_2012_, 1, v___x_2007_);
lean_ctor_set(v___x_2012_, 2, v___x_2009_);
lean_ctor_set(v___x_2012_, 3, v___x_2010_);
lean_ctor_set(v___x_2012_, 4, v___x_2011_);
lean_ctor_set(v___x_2012_, 5, v___x_2008_);
lean_ctor_set(v___x_2012_, 6, v___x_2011_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*7, v___x_2000_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*7 + 1, v___x_2000_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*7 + 2, v___x_2000_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*7 + 3, v___y_1997_);
v___x_2013_ = lean_obj_once(&l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7, &l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once, _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7);
v___x_2014_ = lean_st_mk_ref(v___x_2013_);
v___x_2015_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(v_ctx_1989_, v_builtin_1990_, v_a_1999_, v___x_2012_, v___x_2014_, v___y_1992_, v___y_1993_);
lean_dec_ref(v___x_2012_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2024_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = lean_st_ref_get(v___x_2014_);
lean_dec(v___x_2014_);
lean_dec(v___x_2020_);
if (v_isShared_2019_ == 0)
{
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2016_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
else
{
lean_dec(v___x_2014_);
return v___x_2015_;
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec_ref(v_ctx_1989_);
v_a_2025_ = lean_ctor_get(v___y_1998_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___y_1998_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___y_1998_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___y_1998_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed(lean_object* v_constName_2106_, lean_object* v_ctx_2107_, lean_object* v_builtin_2108_, lean_object* v_catName_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
uint8_t v_builtin_boxed_2113_; lean_object* v_res_2114_; 
v_builtin_boxed_2113_ = lean_unbox(v_builtin_2108_);
v_res_2114_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(v_constName_2106_, v_ctx_2107_, v_builtin_boxed_2113_, v_catName_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v_catName_2109_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(lean_object* v___y_2115_, uint8_t v_isExporting_2116_, lean_object* v___x_2117_, lean_object* v_a_x3f_2118_){
_start:
{
lean_object* v___x_2120_; lean_object* v_env_2121_; lean_object* v_nextMacroScope_2122_; lean_object* v_ngen_2123_; lean_object* v_auxDeclNGen_2124_; lean_object* v_traceState_2125_; lean_object* v_messages_2126_; lean_object* v_infoState_2127_; lean_object* v_snapshotTasks_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2139_; 
v___x_2120_ = lean_st_ref_take(v___y_2115_);
v_env_2121_ = lean_ctor_get(v___x_2120_, 0);
v_nextMacroScope_2122_ = lean_ctor_get(v___x_2120_, 1);
v_ngen_2123_ = lean_ctor_get(v___x_2120_, 2);
v_auxDeclNGen_2124_ = lean_ctor_get(v___x_2120_, 3);
v_traceState_2125_ = lean_ctor_get(v___x_2120_, 4);
v_messages_2126_ = lean_ctor_get(v___x_2120_, 6);
v_infoState_2127_ = lean_ctor_get(v___x_2120_, 7);
v_snapshotTasks_2128_ = lean_ctor_get(v___x_2120_, 8);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2139_ == 0)
{
lean_object* v_unused_2140_; 
v_unused_2140_ = lean_ctor_get(v___x_2120_, 5);
lean_dec(v_unused_2140_);
v___x_2130_ = v___x_2120_;
v_isShared_2131_ = v_isSharedCheck_2139_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_snapshotTasks_2128_);
lean_inc(v_infoState_2127_);
lean_inc(v_messages_2126_);
lean_inc(v_traceState_2125_);
lean_inc(v_auxDeclNGen_2124_);
lean_inc(v_ngen_2123_);
lean_inc(v_nextMacroScope_2122_);
lean_inc(v_env_2121_);
lean_dec(v___x_2120_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2139_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = l_Lean_Environment_setExporting(v_env_2121_, v_isExporting_2116_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 5, v___x_2117_);
lean_ctor_set(v___x_2130_, 0, v___x_2132_);
v___x_2134_ = v___x_2130_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_nextMacroScope_2122_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_ngen_2123_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v_auxDeclNGen_2124_);
lean_ctor_set(v_reuseFailAlloc_2138_, 4, v_traceState_2125_);
lean_ctor_set(v_reuseFailAlloc_2138_, 5, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2138_, 6, v_messages_2126_);
lean_ctor_set(v_reuseFailAlloc_2138_, 7, v_infoState_2127_);
lean_ctor_set(v_reuseFailAlloc_2138_, 8, v_snapshotTasks_2128_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = lean_st_ref_set(v___y_2115_, v___x_2134_);
v___x_2136_ = lean_box(0);
v___x_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
return v___x_2137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v___y_2141_, lean_object* v_isExporting_2142_, lean_object* v___x_2143_, lean_object* v_a_x3f_2144_, lean_object* v___y_2145_){
_start:
{
uint8_t v_isExporting_boxed_2146_; lean_object* v_res_2147_; 
v_isExporting_boxed_2146_ = lean_unbox(v_isExporting_2142_);
v_res_2147_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2141_, v_isExporting_boxed_2146_, v___x_2143_, v_a_x3f_2144_);
lean_dec(v_a_x3f_2144_);
lean_dec(v___y_2141_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(lean_object* v_x_2148_, uint8_t v_isExporting_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; lean_object* v_env_2154_; uint8_t v_isExporting_2155_; lean_object* v___x_2156_; lean_object* v_env_2157_; lean_object* v_nextMacroScope_2158_; lean_object* v_ngen_2159_; lean_object* v_auxDeclNGen_2160_; lean_object* v_traceState_2161_; lean_object* v_messages_2162_; lean_object* v_infoState_2163_; lean_object* v_snapshotTasks_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2203_; 
v___x_2153_ = lean_st_ref_get(v___y_2151_);
v_env_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc_ref(v_env_2154_);
lean_dec(v___x_2153_);
v_isExporting_2155_ = lean_ctor_get_uint8(v_env_2154_, sizeof(void*)*8);
lean_dec_ref(v_env_2154_);
v___x_2156_ = lean_st_ref_take(v___y_2151_);
v_env_2157_ = lean_ctor_get(v___x_2156_, 0);
v_nextMacroScope_2158_ = lean_ctor_get(v___x_2156_, 1);
v_ngen_2159_ = lean_ctor_get(v___x_2156_, 2);
v_auxDeclNGen_2160_ = lean_ctor_get(v___x_2156_, 3);
v_traceState_2161_ = lean_ctor_get(v___x_2156_, 4);
v_messages_2162_ = lean_ctor_get(v___x_2156_, 6);
v_infoState_2163_ = lean_ctor_get(v___x_2156_, 7);
v_snapshotTasks_2164_ = lean_ctor_get(v___x_2156_, 8);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; 
v_unused_2204_ = lean_ctor_get(v___x_2156_, 5);
lean_dec(v_unused_2204_);
v___x_2166_ = v___x_2156_;
v_isShared_2167_ = v_isSharedCheck_2203_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_snapshotTasks_2164_);
lean_inc(v_infoState_2163_);
lean_inc(v_messages_2162_);
lean_inc(v_traceState_2161_);
lean_inc(v_auxDeclNGen_2160_);
lean_inc(v_ngen_2159_);
lean_inc(v_nextMacroScope_2158_);
lean_inc(v_env_2157_);
lean_dec(v___x_2156_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2203_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2168_ = l_Lean_Environment_setExporting(v_env_2157_, v_isExporting_2149_);
v___x_2169_ = lean_obj_once(&l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7, &l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once, _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 5, v___x_2169_);
lean_ctor_set(v___x_2166_, 0, v___x_2168_);
v___x_2171_ = v___x_2166_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_nextMacroScope_2158_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_ngen_2159_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_auxDeclNGen_2160_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v_traceState_2161_);
lean_ctor_set(v_reuseFailAlloc_2202_, 5, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2202_, 6, v_messages_2162_);
lean_ctor_set(v_reuseFailAlloc_2202_, 7, v_infoState_2163_);
lean_ctor_set(v_reuseFailAlloc_2202_, 8, v_snapshotTasks_2164_);
v___x_2171_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2172_; lean_object* v_r_2173_; 
v___x_2172_ = lean_st_ref_set(v___y_2151_, v___x_2171_);
lean_inc(v___y_2151_);
lean_inc_ref(v___y_2150_);
v_r_2173_ = lean_apply_3(v_x_2148_, v___y_2150_, v___y_2151_, lean_box(0));
if (lean_obj_tag(v_r_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2190_; 
v_a_2174_ = lean_ctor_get(v_r_2173_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_r_2173_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2176_ = v_r_2173_;
v_isShared_2177_ = v_isSharedCheck_2190_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v_r_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2190_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
lean_inc(v_a_2174_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set_tag(v___x_2176_, 1);
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
v___x_2180_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2151_, v_isExporting_2155_, v___x_2169_, v___x_2179_);
lean_dec_ref(v___x_2179_);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; 
v_unused_2188_ = lean_ctor_get(v___x_2180_, 0);
lean_dec(v_unused_2188_);
v___x_2182_ = v___x_2180_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_dec(v___x_2180_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v_a_2174_);
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2174_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
v_a_2191_ = lean_ctor_get(v_r_2173_, 0);
lean_inc(v_a_2191_);
lean_dec_ref(v_r_2173_);
v___x_2192_ = lean_box(0);
v___x_2193_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_2151_, v_isExporting_2155_, v___x_2169_, v___x_2192_);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; 
v_unused_2201_ = lean_ctor_get(v___x_2193_, 0);
lean_dec(v_unused_2201_);
v___x_2195_ = v___x_2193_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_dec(v___x_2193_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set_tag(v___x_2195_, 1);
lean_ctor_set(v___x_2195_, 0, v_a_2191_);
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2191_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___boxed(lean_object* v_x_2205_, lean_object* v_isExporting_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
uint8_t v_isExporting_boxed_2210_; lean_object* v_res_2211_; 
v_isExporting_boxed_2210_ = lean_unbox(v_isExporting_2206_);
v_res_2211_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2205_, v_isExporting_boxed_2210_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(lean_object* v_x_2212_, uint8_t v_when_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
if (v_when_2213_ == 0)
{
lean_object* v___x_2217_; 
lean_inc(v___y_2215_);
lean_inc_ref(v___y_2214_);
v___x_2217_ = lean_apply_3(v_x_2212_, v___y_2214_, v___y_2215_, lean_box(0));
return v___x_2217_;
}
else
{
uint8_t v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = 0;
v___x_2219_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2212_, v___x_2218_, v___y_2214_, v___y_2215_);
return v___x_2219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg___boxed(lean_object* v_x_2220_, lean_object* v_when_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
uint8_t v_when_boxed_2225_; lean_object* v_res_2226_; 
v_when_boxed_2225_ = lean_unbox(v_when_2221_);
v_res_2226_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v_x_2220_, v_when_boxed_2225_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(lean_object* v_ctx_2227_, lean_object* v_catName_2228_, lean_object* v_constName_2229_, uint8_t v_builtin_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2234_; lean_object* v___f_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; 
v___x_2234_ = lean_box(v_builtin_2230_);
v___f_2235_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_2235_, 0, v_constName_2229_);
lean_closure_set(v___f_2235_, 1, v_ctx_2227_);
lean_closure_set(v___f_2235_, 2, v___x_2234_);
lean_closure_set(v___f_2235_, 3, v_catName_2228_);
v___x_2236_ = 1;
v___x_2237_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v___f_2235_, v___x_2236_, v___y_2231_, v___y_2232_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed(lean_object* v_ctx_2238_, lean_object* v_catName_2239_, lean_object* v_constName_2240_, lean_object* v_builtin_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
uint8_t v_builtin_boxed_2245_; lean_object* v_res_2246_; 
v_builtin_boxed_2245_ = lean_unbox(v_builtin_2241_);
v_res_2246_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(v_ctx_2238_, v_catName_2239_, v_constName_2240_, v_builtin_boxed_2245_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg(lean_object* v_ctx_2247_){
_start:
{
lean_object* v___f_2249_; lean_object* v___x_2250_; 
v___f_2249_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed), 7, 1);
lean_closure_set(v___f_2249_, 0, v_ctx_2247_);
v___x_2250_ = l_Lean_Parser_registerParserAttributeHook(v___f_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg___boxed(lean_object* v_ctx_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v_ctx_2251_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler(lean_object* v_00_u03b1_2254_, lean_object* v_ctx_2255_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v_ctx_2255_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerParserCompiler___boxed(lean_object* v_00_u03b1_2258_, lean_object* v_ctx_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_ParserCompiler_registerParserCompiler(v_00_u03b1_2258_, v_ctx_2259_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(lean_object* v_00_u03b1_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(v_00_u03b1_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(lean_object* v_00_u03b1_2272_, lean_object* v_typeName_2273_, lean_object* v_constName_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v_typeName_2273_, v_constName_2274_, v___y_2275_, v___y_2276_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___boxed(lean_object* v_00_u03b1_2279_, lean_object* v_typeName_2280_, lean_object* v_constName_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(v_00_u03b1_2279_, v_typeName_2280_, v_constName_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(lean_object* v_00_u03b1_2286_, lean_object* v_x_2287_, uint8_t v_isExporting_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_2287_, v_isExporting_2288_, v___y_2289_, v___y_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2293_, lean_object* v_x_2294_, lean_object* v_isExporting_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
uint8_t v_isExporting_boxed_2299_; lean_object* v_res_2300_; 
v_isExporting_boxed_2299_ = lean_unbox(v_isExporting_2295_);
v_res_2300_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(v_00_u03b1_2293_, v_x_2294_, v_isExporting_boxed_2299_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(lean_object* v_00_u03b1_2301_, lean_object* v_x_2302_, uint8_t v_when_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v_x_2302_, v_when_2303_, v___y_2304_, v___y_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___boxed(lean_object* v_00_u03b1_2308_, lean_object* v_x_2309_, lean_object* v_when_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
uint8_t v_when_boxed_2314_; lean_object* v_res_2315_; 
v_when_boxed_2314_ = lean_unbox(v_when_2310_);
v_res_2315_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(v_00_u03b1_2308_, v_x_2309_, v_when_boxed_2314_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(lean_object* v_00_u03b1_2316_, lean_object* v_constName_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_2317_, v___y_2318_, v___y_2319_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2322_, lean_object* v_constName_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(v_00_u03b1_2322_, v_constName_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(lean_object* v_00_u03b1_2328_, lean_object* v_x_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v_x_2329_, v___y_2330_, v___y_2331_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2334_, lean_object* v_x_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(v_00_u03b1_2334_, v_x_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2340_, lean_object* v_ref_2341_, lean_object* v_constName_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_2341_, v_constName_2342_, v___y_2343_, v___y_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2347_, lean_object* v_ref_2348_, lean_object* v_constName_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(v_00_u03b1_2347_, v_ref_2348_, v_constName_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v_ref_2348_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2354_, lean_object* v_msg_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_2355_, v___y_2356_, v___y_2357_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2360_, lean_object* v_msg_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(v_00_u03b1_2360_, v_msg_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b1_2366_, lean_object* v_ref_2367_, lean_object* v_msg_2368_, lean_object* v_declHint_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_2367_, v_msg_2368_, v_declHint_2369_, v___y_2370_, v___y_2371_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b1_2374_, lean_object* v_ref_2375_, lean_object* v_msg_2376_, lean_object* v_declHint_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_2374_, v_ref_2375_, v_msg_2376_, v_declHint_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v_ref_2375_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(lean_object* v_msg_2382_, lean_object* v_declHint_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_2382_, v_declHint_2383_, v___y_2385_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___boxed(lean_object* v_msg_2388_, lean_object* v_declHint_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(v_msg_2388_, v_declHint_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_2394_, lean_object* v_ref_2395_, lean_object* v_msg_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_2395_, v_msg_2396_, v___y_2397_, v___y_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2401_, lean_object* v_ref_2402_, lean_object* v_msg_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(v_00_u03b1_2401_, v_ref_2402_, v_msg_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v_ref_2402_);
return v_res_2407_;
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
