// Lean compiler output
// Module: Lean.Parser.Extension
// Imports: public import Lean.Parser.Basic public import Lean.ScopedEnvExtension import Lean.BuiltinDocAttr
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
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Data_Trie_find_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_List_eraseDupsBy___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_leadingNode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_trailingNode(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_nonReservedSymbol(lean_object*, uint8_t);
lean_object* l_Lean_Parser_categoryParser(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_unicodeSymbol___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_unsafeBaseIO___redArg(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_registerAttributeImplBuilder(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_prattParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltinDocStringAndRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_initializing();
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Parser_categoryParserFnRef;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
uint8_t lean_internal_is_stage0(lean_object*);
extern lean_object* l_Lean_Parser_SyntaxStack_empty;
lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerAttributeOfBuilder(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_builtinTokenTable;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_builtinSyntaxNodeKindSetRef;
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinNodeKind___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_builtinParserCategoriesRef;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "parser category `"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` has already been defined"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0 = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0_value)}};
static const lean_object* l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__1 = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_ParserExtension_instInhabitedEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0_value)}};
static const lean_object* l_Lean_Parser_ParserExtension_instInhabitedEntry_default___closed__0 = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_ParserExtension_instInhabitedEntry_default = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_ParserExtension_instInhabitedEntry = (const lean_object*)&l_Lean_Parser_ParserExtension_instInhabitedEntry_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object*);
static lean_once_cell_t l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_instInhabitedState;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid empty symbol"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__0_value)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unknown parser category `"};
static const lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0_value;
static const lean_string_object l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_getCategory___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_getCategory___closed__0 = (const lean_object*)&l_Lean_Parser_getCategory___closed__0_value;
static const lean_closure_object l_Lean_Parser_getCategory___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_getCategory___closed__1 = (const lean_object*)&l_Lean_Parser_getCategory___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory___boxed(lean_object*, lean_object*);
static const lean_closure_object l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0 = (const lean_object*)&l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid builtin parser `"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`, "};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(lean_object*);
static const lean_string_object l_Lean_Parser_ParserExtension_addEntryImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Parser.Extension"};
static const lean_object* l_Lean_Parser_ParserExtension_addEntryImpl___closed__0 = (const lean_object*)&l_Lean_Parser_ParserExtension_addEntryImpl___closed__0_value;
static const lean_string_object l_Lean_Parser_ParserExtension_addEntryImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Parser.ParserExtension.addEntryImpl"};
static const lean_object* l_Lean_Parser_ParserExtension_addEntryImpl___closed__1 = (const lean_object*)&l_Lean_Parser_ParserExtension_addEntryImpl___closed__1_value;
static const lean_string_object l_Lean_Parser_ParserExtension_addEntryImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ParserExtension.addEntryImpl: "};
static const lean_object* l_Lean_Parser_ParserExtension_addEntryImpl___closed__2 = (const lean_object*)&l_Lean_Parser_ParserExtension_addEntryImpl___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_registerAliasCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "aliases can only be registered during initialization"};
static const lean_object* l_Lean_Parser_registerAliasCore___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_registerAliasCore___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Parser_registerAliasCore___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerAliasCore___redArg___closed__1;
static const lean_string_object l_Lean_Parser_registerAliasCore___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "alias `"};
static const lean_object* l_Lean_Parser_registerAliasCore___redArg___closed__2 = (const lean_object*)&l_Lean_Parser_registerAliasCore___redArg___closed__2_value;
static const lean_string_object l_Lean_Parser_registerAliasCore___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l_Lean_Parser_registerAliasCore___redArg___closed__3 = (const lean_object*)&l_Lean_Parser_registerAliasCore___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_getConstAlias___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "parser `"};
static const lean_object* l_Lean_Parser_getConstAlias___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_getConstAlias___redArg___closed__0_value;
static const lean_string_object l_Lean_Parser_getConstAlias___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` was not found"};
static const lean_object* l_Lean_Parser_getConstAlias___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_getConstAlias___redArg___closed__1_value;
static const lean_string_object l_Lean_Parser_getConstAlias___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` is not a constant, it takes one argument"};
static const lean_object* l_Lean_Parser_getConstAlias___redArg___closed__2 = (const lean_object*)&l_Lean_Parser_getConstAlias___redArg___closed__2_value;
static const lean_string_object l_Lean_Parser_getConstAlias___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "` is not a constant, it takes two arguments"};
static const lean_object* l_Lean_Parser_getConstAlias___redArg___closed__3 = (const lean_object*)&l_Lean_Parser_getConstAlias___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_getUnaryAlias___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` does not take one argument"};
static const lean_object* l_Lean_Parser_getUnaryAlias___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_getUnaryAlias___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_getBinaryAlias___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` does not take two arguments"};
static const lean_object* l_Lean_Parser_getBinaryAlias___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_getBinaryAlias___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserAliasesRef;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserAlias2kindRef;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserAliases2infoRef;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_getParserAliasInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_getParserAliasInfo___closed__0 = (const lean_object*)&l_Lean_Parser_getParserAliasInfo___closed__0_value;
static const lean_ctor_object l_Lean_Parser_getParserAliasInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_getParserAliasInfo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_getParserAliasInfo___closed__1 = (const lean_object*)&l_Lean_Parser_getParserAliasInfo___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_Parser_instCoeParserParserAliasValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instCoeParserParserAliasValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instCoeParserParserAliasValue___closed__0 = (const lean_object*)&l_Lean_Parser_instCoeParserParserAliasValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instCoeParserParserAliasValue = (const lean_object*)&l_Lean_Parser_instCoeParserParserAliasValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_Parser_instCoeForallParserParserAliasValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___closed__0 = (const lean_object*)&l_Lean_Parser_instCoeForallParserParserAliasValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue = (const lean_object*)&l_Lean_Parser_instCoeForallParserParserAliasValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0(lean_object*);
static const lean_closure_object l_Lean_Parser_instCoeForallParserForallParserAliasValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___closed__0 = (const lean_object*)&l_Lean_Parser_instCoeForallParserForallParserAliasValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue = (const lean_object*)&l_Lean_Parser_instCoeForallParserForallParserAliasValue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unexpected parser type at `"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__0 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__0_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "` (`ParserDescr`, `TrailingParserDescr`, `Parser` or `TrailingParser` expected)"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__1 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__1_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__2 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__2_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__3 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__4 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "TrailingParser"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__5 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__5_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ParserDescr"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__6 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__6_value;
static const lean_string_object l_Lean_Parser_mkParserOfConstantUnsafe___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "TrailingParserDescr"};
static const lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___closed__7 = (const lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserAttributeHooks;
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 58, 155, 4, 51, 160, 88)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Extension"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(137, 52, 234, 177, 21, 192, 22, 198)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(76, 45, 242, 72, 67, 202, 5, 30)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(205, 229, 28, 218, 19, 105, 170, 35)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 61, 201, 18, 105, 219, 240, 138)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 138, 216, 176, 146, 185, 210, 47)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(144, 125, 145, 169, 32, 215, 69, 54)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(105, 155, 228, 215, 194, 242, 73, 58)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(244, 229, 229, 196, 152, 62, 92, 225)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(154, 168, 69, 111, 155, 198, 82, 16)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "run_builtin_parser_attribute_hooks"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 253, 249, 46, 168, 175, 6, 195)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "explicitly run hooks normally activated by builtin parser attributes"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "run_parser_attribute_hooks"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 66, 27, 152, 146, 188, 80, 181)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "explicitly run hooks normally activated by parser attributes"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "parserExtension"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 242, 71, 245, 68, 132, 173, 111)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ParserExtension_Entry_toOLeanEntry, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ParserExtension_addEntryImpl, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserExtension;
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "internal"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "parseQuotWithCurrentStage"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(177, 49, 45, 44, 152, 148, 209, 41)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 253, 75, 217, 201, 67, 21, 43)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "(Lean bootstrapping) use parsers from the current stage inside quotations"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(197, 200, 93, 246, 219, 188, 139, 219)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(180, 175, 65, 251, 248, 238, 117, 156)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_internal_parseQuotWithCurrentStage;
static const lean_string_object l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_evalInsideQuot___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "interpreter"};
static const lean_object* l_Lean_Parser_evalInsideQuot___lam__0___closed__0 = (const lean_object*)&l_Lean_Parser_evalInsideQuot___lam__0___closed__0_value;
static const lean_string_object l_Lean_Parser_evalInsideQuot___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "prefer_native"};
static const lean_object* l_Lean_Parser_evalInsideQuot___lam__0___closed__1 = (const lean_object*)&l_Lean_Parser_evalInsideQuot___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Parser_evalInsideQuot___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_evalInsideQuot___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 89, 165, 10, 241, 76, 182, 215)}};
static const lean_ctor_object l_Lean_Parser_evalInsideQuot___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_evalInsideQuot___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_evalInsideQuot___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(9, 111, 178, 130, 77, 52, 174, 36)}};
static const lean_object* l_Lean_Parser_evalInsideQuot___lam__0___closed__2 = (const lean_object*)&l_Lean_Parser_evalInsideQuot___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_evalInsideQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_evalInsideQuot___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_evalInsideQuot___closed__0 = (const lean_object*)&l_Lean_Parser_evalInsideQuot___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_categoryParserFnImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Parser_categoryParserFnImpl___closed__0 = (const lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__0_value;
static const lean_ctor_object l_Lean_Parser_categoryParserFnImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 107, 139, 89, 122, 253, 8, 100)}};
static const lean_object* l_Lean_Parser_categoryParserFnImpl___closed__1 = (const lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__1_value;
static const lean_string_object l_Lean_Parser_categoryParserFnImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unknown parser category '"};
static const lean_object* l_Lean_Parser_categoryParserFnImpl___closed__2 = (const lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__2_value;
static const lean_string_object l_Lean_Parser_categoryParserFnImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Parser_categoryParserFnImpl___closed__3 = (const lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__3_value;
static const lean_string_object l_Lean_Parser_categoryParserFnImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "stx"};
static const lean_object* l_Lean_Parser_categoryParserFnImpl___closed__4 = (const lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__4_value;
static const lean_ctor_object l_Lean_Parser_categoryParserFnImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(89, 124, 230, 186, 154, 11, 21, 78)}};
static const lean_object* l_Lean_Parser_categoryParserFnImpl___closed__5 = (const lean_object*)&l_Lean_Parser_categoryParserFnImpl___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_categoryParserFnImpl, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Parser_isValidSyntaxNodeKind___closed__0;
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_getSyntaxNodeKinds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_getSyntaxNodeKinds___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_getSyntaxNodeKinds___closed__0 = (const lean_object*)&l_Lean_Parser_getSyntaxNodeKinds___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object*);
static const lean_string_object l_Lean_Parser_mkInputContext___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__0 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__0_value;
static const lean_string_object l_Lean_Parser_mkInputContext___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__1 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__1_value;
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__2 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__2_value;
static const lean_array_object l_Lean_Parser_mkInputContext___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__3 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__3_value;
static const lean_string_object l_Lean_Parser_mkInputContext___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__4 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__4_value;
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__5_value_aux_1),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__5 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__5_value;
static const lean_string_object l_Lean_Parser_mkInputContext___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__6 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__7 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__7_value;
static const lean_string_object l_Lean_Parser_mkInputContext___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__8 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__9_value_aux_2),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__9 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__9_value;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__10;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__11;
static const lean_string_object l_Lean_Parser_mkInputContext___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__12 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__12_value;
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__13_value_aux_1),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__13_value_aux_2),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__13 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__13_value;
static const lean_ctor_object l_Lean_Parser_mkInputContext___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__7_value),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__3_value)}};
static const lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__14 = (const lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__14_value;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__15;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__16;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__17;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__18;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__19;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__20;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__21;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__22;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__23;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__24;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__25;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__26;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__27;
static lean_once_cell_t l_Lean_Parser_mkInputContext___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_mkInputContext___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___auto__1;
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Parser_mkParserState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_mkParserState___closed__0 = (const lean_object*)&l_Lean_Parser_mkParserState___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_runParserCategory___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_whitespace, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_runParserCategory___closed__0 = (const lean_object*)&l_Lean_Parser_runParserCategory___closed__0_value;
static const lean_string_object l_Lean_Parser_runParserCategory___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "end of input"};
static const lean_object* l_Lean_Parser_runParserCategory___closed__1 = (const lean_object*)&l_Lean_Parser_runParserCategory___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_declareLeadingBuiltinParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "addBuiltinLeadingParser"};
static const lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__0 = (const lean_object*)&l_Lean_Parser_declareLeadingBuiltinParser___closed__0_value;
static const lean_ctor_object l_Lean_Parser_declareLeadingBuiltinParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_declareLeadingBuiltinParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_declareLeadingBuiltinParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_declareLeadingBuiltinParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_declareLeadingBuiltinParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_declareLeadingBuiltinParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 143, 237, 9, 185, 72, 31, 190)}};
static const lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1 = (const lean_object*)&l_Lean_Parser_declareLeadingBuiltinParser___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_declareTrailingBuiltinParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "addBuiltinTrailingParser"};
static const lean_object* l_Lean_Parser_declareTrailingBuiltinParser___closed__0 = (const lean_object*)&l_Lean_Parser_declareTrailingBuiltinParser___closed__0_value;
static const lean_ctor_object l_Lean_Parser_declareTrailingBuiltinParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_declareTrailingBuiltinParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_declareTrailingBuiltinParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_declareTrailingBuiltinParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_declareTrailingBuiltinParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_declareTrailingBuiltinParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 81, 8, 5, 195, 158, 30, 32)}};
static const lean_object* l_Lean_Parser_declareTrailingBuiltinParser___closed__1 = (const lean_object*)&l_Lean_Parser_declareTrailingBuiltinParser___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_getParserPriority___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "Invalid parser attribute: No argument or numeral expected"};
static const lean_object* l_Lean_Parser_getParserPriority___closed__0 = (const lean_object*)&l_Lean_Parser_getParserPriority___closed__0_value;
static const lean_ctor_object l_Lean_Parser_getParserPriority___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_getParserPriority___closed__0_value)}};
static const lean_object* l_Lean_Parser_getParserPriority___closed__1 = (const lean_object*)&l_Lean_Parser_getParserPriority___closed__1_value;
static const lean_string_object l_Lean_Parser_getParserPriority___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "Invalid parser attribute: Numeral expected, but found `"};
static const lean_object* l_Lean_Parser_getParserPriority___closed__2 = (const lean_object*)&l_Lean_Parser_getParserPriority___closed__2_value;
static const lean_ctor_object l_Lean_Parser_getParserPriority___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_getParserPriority___closed__3 = (const lean_object*)&l_Lean_Parser_getParserPriority___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "Unexpected type for parser declaration: Parsers must have type `Parser` or `TrailingParser`, but `"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0_value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2_value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_mkInputContext___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1_value;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3;
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__4 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__4_value;
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__5 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__5_value;
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6_value;
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7_value;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18;
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___auto__1;
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`declName` should be in Lean.Parser.Category"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___closed__0 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___closed__0_value;
static lean_once_cell_t l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_registerBuiltinParserAttribute___closed__1;
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Category"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___closed__2 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___closed__2_value;
static const lean_string_object l_Lean_Parser_registerBuiltinParserAttribute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Builtin parser"};
static const lean_object* l_Lean_Parser_registerBuiltinParserAttribute___closed__3 = (const lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invalid parser `"};
static const lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0 = (const lean_object*)&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0_value;
static lean_once_cell_t l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1;
static lean_once_cell_t l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2;
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___auto__1;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_mkParserAttributeImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parser"};
static const lean_object* l_Lean_Parser_mkParserAttributeImpl___closed__0 = (const lean_object*)&l_Lean_Parser_mkParserAttributeImpl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1;
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "invalid parser attribute implementation builder arguments"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "parserAttr"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 245, 154, 169, 111, 55, 1, 167)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___auto__1;
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "builtin_term_parser"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 207, 87, 145, 239, 20, 239, 169)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___closed__2_value),LEAN_SCALAR_PTR_LITERAL(36, 45, 52, 71, 90, 26, 52, 161)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(208, 211, 65, 28, 248, 161, 130, 58)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),((lean_object*)(((size_t)(346849000) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(211, 245, 159, 105, 210, 84, 228, 140)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(136, 27, 163, 230, 210, 150, 171, 72)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 94, 18, 83, 183, 97, 76, 247)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(53, 114, 123, 211, 41, 25, 101, 118)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term_parser"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 63, 227, 232, 74, 240, 13, 112)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "builtin_command_parser"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 82, 248, 24, 98, 200, 69, 241)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Parser_registerBuiltinParserAttribute___closed__2_value),LEAN_SCALAR_PTR_LITERAL(36, 45, 52, 71, 90, 26, 52, 161)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 37, 169, 7, 189, 210, 168, 21)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "command_parser"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 48, 168, 200, 51, 243, 130, 78)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_withOpenDeclFnCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__0 = (const lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__0_value;
static const lean_string_object l_Lean_Parser_withOpenDeclFnCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openSimple"};
static const lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__1 = (const lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__1_value;
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(171, 238, 134, 92, 162, 110, 43, 67)}};
static const lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__2 = (const lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__2_value;
static const lean_string_object l_Lean_Parser_withOpenDeclFnCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openScoped"};
static const lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__3 = (const lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__3_value;
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_withOpenDeclFnCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(55, 166, 237, 23, 37, 47, 5, 133)}};
static const lean_object* l_Lean_Parser_withOpenDeclFnCore___closed__4 = (const lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_withOpenFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "open"};
static const lean_object* l_Lean_Parser_withOpenFn___closed__0 = (const lean_object*)&l_Lean_Parser_withOpenFn___closed__0_value;
static const lean_ctor_object l_Lean_Parser_withOpenFn___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withOpenFn___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenFn___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withOpenFn___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenFn___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_withOpenFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withOpenFn___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_withOpenFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 8, 226, 43, 107, 167, 95, 157)}};
static const lean_object* l_Lean_Parser_withOpenFn___closed__1 = (const lean_object*)&l_Lean_Parser_withOpenFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object*);
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__1_value)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_withSetOptionFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "set_option"};
static const lean_object* l_Lean_Parser_withSetOptionFn___closed__0 = (const lean_object*)&l_Lean_Parser_withSetOptionFn___closed__0_value;
static const lean_ctor_object l_Lean_Parser_withSetOptionFn___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withSetOptionFn___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withSetOptionFn___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withSetOptionFn___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withSetOptionFn___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_withOpenDeclFnCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_withSetOptionFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withSetOptionFn___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_withSetOptionFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 223, 149, 245, 150, 86, 134, 198)}};
static const lean_object* l_Lean_Parser_withSetOptionFn___closed__1 = (const lean_object*)&l_Lean_Parser_withSetOptionFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_aliasExtension;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ambiguous parser name "};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__0 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__0_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "unknown parser "};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__1 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__1_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "expected parser to return exactly one syntax object"};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__2 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__2_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parser alias "};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__3 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__3_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = ", must not take parameters"};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__4 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__4_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 103, .m_capacity = 103, .m_length = 102, .m_data = "failed to determine parser using syntax stack, the specified element on the stack is not an identifier"};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__5 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__5_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "failed to determine parser using syntax stack, stack is too small"};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__6 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_parserOfStack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_parserOfStack___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_parserOfStack___closed__0 = (const lean_object*)&l_Lean_Parser_parserOfStack___closed__0_value;
static const lean_closure_object l_Lean_Parser_parserOfStack___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_parserOfStack___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_parserOfStack___closed__1 = (const lean_object*)&l_Lean_Parser_parserOfStack___closed__1_value;
static const lean_ctor_object l_Lean_Parser_parserOfStack___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_parserOfStack___closed__0_value),((lean_object*)&l_Lean_Parser_parserOfStack___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_parserOfStack___closed__2 = (const lean_object*)&l_Lean_Parser_parserOfStack___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Data_Trie_empty(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_4_ = lean_st_mk_ref(v___x_3_);
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2____boxed(lean_object* v_a_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_();
return v_res_7_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_8_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_13_ = lean_st_mk_ref(v___x_12_);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2____boxed(lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_();
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object* v_k_17_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_19_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_20_ = lean_st_ref_take(v___x_19_);
v___x_21_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v___x_20_, v_k_17_);
v___x_22_ = lean_st_ref_put(v___x_19_, v___x_21_);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinNodeKind___boxed(lean_object* v_k_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Parser_registerBuiltinNodeKind(v_k_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_49_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_));
v___x_50_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_49_);
lean_dec_ref(v___x_50_);
v___x_51_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_));
v___x_52_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_51_);
lean_dec_ref(v___x_52_);
v___x_53_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_));
v___x_54_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_53_);
lean_dec_ref(v___x_54_);
v___x_55_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_));
v___x_56_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_55_);
lean_dec_ref(v___x_56_);
v___x_57_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_));
v___x_58_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_57_);
lean_dec_ref(v___x_58_);
v___x_59_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_));
v___x_60_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_59_);
lean_dec_ref(v___x_60_);
v___x_61_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_));
v___x_62_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2____boxed(lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_();
return v_res_64_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_65_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_);
v___x_70_ = lean_st_mk_ref(v___x_69_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2____boxed(lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(lean_object* v_catName_76_){
_start:
{
lean_object* v___x_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0));
v___x_78_ = 1;
v___x_79_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_76_, v___x_78_);
v___x_80_ = lean_string_append(v___x_77_, v___x_79_);
lean_dec_ref(v___x_79_);
v___x_81_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1));
v___x_82_ = lean_string_append(v___x_80_, v___x_81_);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined(lean_object* v_00_u03b1_84_, lean_object* v_catName_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_87_, lean_object* v_x_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
lean_object* v_ks_91_; lean_object* v_vs_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_116_; 
v_ks_91_ = lean_ctor_get(v_x_87_, 0);
v_vs_92_ = lean_ctor_get(v_x_87_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_116_ == 0)
{
v___x_94_ = v_x_87_;
v_isShared_95_ = v_isSharedCheck_116_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_vs_92_);
lean_inc(v_ks_91_);
lean_dec(v_x_87_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_116_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_96_ = lean_array_get_size(v_ks_91_);
v___x_97_ = lean_nat_dec_lt(v_x_88_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_101_; 
lean_dec(v_x_88_);
v___x_98_ = lean_array_push(v_ks_91_, v_x_89_);
v___x_99_ = lean_array_push(v_vs_92_, v_x_90_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v___x_99_);
lean_ctor_set(v___x_94_, 0, v___x_98_);
v___x_101_ = v___x_94_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
else
{
lean_object* v_k_x27_103_; uint8_t v___x_104_; 
v_k_x27_103_ = lean_array_fget_borrowed(v_ks_91_, v_x_88_);
v___x_104_ = lean_name_eq(v_x_89_, v_k_x27_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_106_; 
if (v_isShared_95_ == 0)
{
v___x_106_ = v___x_94_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_ks_91_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_vs_92_);
v___x_106_ = v_reuseFailAlloc_110_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(1u);
v___x_108_ = lean_nat_add(v_x_88_, v___x_107_);
lean_dec(v_x_88_);
v_x_87_ = v___x_106_;
v_x_88_ = v___x_108_;
goto _start;
}
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_111_ = lean_array_fset(v_ks_91_, v_x_88_, v_x_89_);
v___x_112_ = lean_array_fset(v_vs_92_, v_x_88_, v_x_90_);
lean_dec(v_x_88_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v___x_112_);
lean_ctor_set(v___x_94_, 0, v___x_111_);
v___x_114_ = v___x_94_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_111_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(lean_object* v_n_117_, lean_object* v_k_118_, lean_object* v_v_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_n_117_, v___x_120_, v_k_118_, v_v_119_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(lean_object* v_x_123_, size_t v_x_124_, size_t v_x_125_, lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_123_) == 0)
{
lean_object* v_es_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v_j_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_es_128_ = lean_ctor_get(v_x_123_, 0);
v___x_129_ = ((size_t)31ULL);
v___x_130_ = lean_usize_land(v_x_124_, v___x_129_);
v_j_131_ = lean_usize_to_nat(v___x_130_);
v___x_132_ = lean_array_get_size(v_es_128_);
v___x_133_ = lean_nat_dec_lt(v_j_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_dec(v_j_131_);
lean_dec(v_x_127_);
lean_dec(v_x_126_);
return v_x_123_;
}
else
{
lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_172_; 
lean_inc_ref(v_es_128_);
v_isSharedCheck_172_ = !lean_is_exclusive(v_x_123_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; 
v_unused_173_ = lean_ctor_get(v_x_123_, 0);
lean_dec(v_unused_173_);
v___x_135_ = v_x_123_;
v_isShared_136_ = v_isSharedCheck_172_;
goto v_resetjp_134_;
}
else
{
lean_dec(v_x_123_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_172_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v_v_137_; lean_object* v___x_138_; lean_object* v_xs_x27_139_; lean_object* v___y_141_; 
v_v_137_ = lean_array_fget(v_es_128_, v_j_131_);
v___x_138_ = lean_box(0);
v_xs_x27_139_ = lean_array_fset(v_es_128_, v_j_131_, v___x_138_);
switch(lean_obj_tag(v_v_137_))
{
case 0:
{
lean_object* v_key_146_; lean_object* v_val_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_157_; 
v_key_146_ = lean_ctor_get(v_v_137_, 0);
v_val_147_ = lean_ctor_get(v_v_137_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_v_137_);
if (v_isSharedCheck_157_ == 0)
{
v___x_149_ = v_v_137_;
v_isShared_150_ = v_isSharedCheck_157_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_val_147_);
lean_inc(v_key_146_);
lean_dec(v_v_137_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_157_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
uint8_t v___x_151_; 
v___x_151_ = lean_name_eq(v_x_126_, v_key_146_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_del_object(v___x_149_);
v___x_152_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_146_, v_val_147_, v_x_126_, v_x_127_);
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
v___y_141_ = v___x_153_;
goto v___jp_140_;
}
else
{
lean_object* v___x_155_; 
lean_dec(v_val_147_);
lean_dec(v_key_146_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v_x_127_);
lean_ctor_set(v___x_149_, 0, v_x_126_);
v___x_155_ = v___x_149_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_x_126_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_x_127_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
v___y_141_ = v___x_155_;
goto v___jp_140_;
}
}
}
}
case 1:
{
lean_object* v_node_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_170_; 
v_node_158_ = lean_ctor_get(v_v_137_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v_v_137_);
if (v_isSharedCheck_170_ == 0)
{
v___x_160_ = v_v_137_;
v_isShared_161_ = v_isSharedCheck_170_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_node_158_);
lean_dec(v_v_137_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_170_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_162_ = ((size_t)5ULL);
v___x_163_ = lean_usize_shift_right(v_x_124_, v___x_162_);
v___x_164_ = ((size_t)1ULL);
v___x_165_ = lean_usize_add(v_x_125_, v___x_164_);
v___x_166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_node_158_, v___x_163_, v___x_165_, v_x_126_, v_x_127_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v___x_166_);
v___x_168_ = v___x_160_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
v___y_141_ = v___x_168_;
goto v___jp_140_;
}
}
}
default: 
{
lean_object* v___x_171_; 
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v_x_126_);
lean_ctor_set(v___x_171_, 1, v_x_127_);
v___y_141_ = v___x_171_;
goto v___jp_140_;
}
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_array_fset(v_xs_x27_139_, v_j_131_, v___y_141_);
lean_dec(v_j_131_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_142_);
v___x_144_ = v___x_135_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
else
{
lean_object* v_ks_174_; lean_object* v_vs_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_195_; 
v_ks_174_ = lean_ctor_get(v_x_123_, 0);
v_vs_175_ = lean_ctor_get(v_x_123_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_123_);
if (v_isSharedCheck_195_ == 0)
{
v___x_177_ = v_x_123_;
v_isShared_178_ = v_isSharedCheck_195_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_vs_175_);
lean_inc(v_ks_174_);
lean_dec(v_x_123_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_195_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_ks_174_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_vs_175_);
v___x_180_ = v_reuseFailAlloc_194_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v_newNode_181_; uint8_t v___y_183_; size_t v___x_189_; uint8_t v___x_190_; 
v_newNode_181_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v___x_180_, v_x_126_, v_x_127_);
v___x_189_ = ((size_t)7ULL);
v___x_190_ = lean_usize_dec_le(v___x_189_, v_x_125_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_191_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_181_);
v___x_192_ = lean_unsigned_to_nat(4u);
v___x_193_ = lean_nat_dec_lt(v___x_191_, v___x_192_);
lean_dec(v___x_191_);
v___y_183_ = v___x_193_;
goto v___jp_182_;
}
else
{
v___y_183_ = v___x_190_;
goto v___jp_182_;
}
v___jp_182_:
{
if (v___y_183_ == 0)
{
lean_object* v_ks_184_; lean_object* v_vs_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_ks_184_ = lean_ctor_get(v_newNode_181_, 0);
lean_inc_ref(v_ks_184_);
v_vs_185_ = lean_ctor_get(v_newNode_181_, 1);
lean_inc_ref(v_vs_185_);
lean_dec_ref(v_newNode_181_);
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0);
v___x_188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_x_125_, v_ks_184_, v_vs_185_, v___x_186_, v___x_187_);
lean_dec_ref(v_vs_185_);
lean_dec_ref(v_ks_184_);
return v___x_188_;
}
else
{
return v_newNode_181_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(size_t v_depth_196_, lean_object* v_keys_197_, lean_object* v_vals_198_, lean_object* v_i_199_, lean_object* v_entries_200_){
_start:
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = lean_array_get_size(v_keys_197_);
v___x_202_ = lean_nat_dec_lt(v_i_199_, v___x_201_);
if (v___x_202_ == 0)
{
lean_dec(v_i_199_);
return v_entries_200_;
}
else
{
lean_object* v_k_203_; lean_object* v_v_204_; uint64_t v___y_206_; 
v_k_203_ = lean_array_fget_borrowed(v_keys_197_, v_i_199_);
v_v_204_ = lean_array_fget_borrowed(v_vals_198_, v_i_199_);
if (lean_obj_tag(v_k_203_) == 0)
{
uint64_t v___x_217_; 
v___x_217_ = 1723ULL;
v___y_206_ = v___x_217_;
goto v___jp_205_;
}
else
{
uint64_t v_hash_218_; 
v_hash_218_ = lean_ctor_get_uint64(v_k_203_, sizeof(void*)*2);
v___y_206_ = v_hash_218_;
goto v___jp_205_;
}
v___jp_205_:
{
size_t v_h_207_; size_t v___x_208_; lean_object* v___x_209_; size_t v___x_210_; size_t v___x_211_; size_t v___x_212_; size_t v_h_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_h_207_ = lean_uint64_to_usize(v___y_206_);
v___x_208_ = ((size_t)5ULL);
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = ((size_t)1ULL);
v___x_211_ = lean_usize_sub(v_depth_196_, v___x_210_);
v___x_212_ = lean_usize_mul(v___x_208_, v___x_211_);
v_h_213_ = lean_usize_shift_right(v_h_207_, v___x_212_);
v___x_214_ = lean_nat_add(v_i_199_, v___x_209_);
lean_dec(v_i_199_);
lean_inc(v_v_204_);
lean_inc(v_k_203_);
v___x_215_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_entries_200_, v_h_213_, v_depth_196_, v_k_203_, v_v_204_);
v_i_199_ = v___x_214_;
v_entries_200_ = v___x_215_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_219_, lean_object* v_keys_220_, lean_object* v_vals_221_, lean_object* v_i_222_, lean_object* v_entries_223_){
_start:
{
size_t v_depth_boxed_224_; lean_object* v_res_225_; 
v_depth_boxed_224_ = lean_unbox_usize(v_depth_219_);
lean_dec(v_depth_219_);
v_res_225_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_boxed_224_, v_keys_220_, v_vals_221_, v_i_222_, v_entries_223_);
lean_dec_ref(v_vals_221_);
lean_dec_ref(v_keys_220_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
size_t v_x_533__boxed_231_; size_t v_x_534__boxed_232_; lean_object* v_res_233_; 
v_x_533__boxed_231_ = lean_unbox_usize(v_x_227_);
lean_dec(v_x_227_);
v_x_534__boxed_232_ = lean_unbox_usize(v_x_228_);
lean_dec(v_x_228_);
v_res_233_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_226_, v_x_533__boxed_231_, v_x_534__boxed_232_, v_x_229_, v_x_230_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_x_236_){
_start:
{
uint64_t v___y_238_; 
if (lean_obj_tag(v_x_235_) == 0)
{
uint64_t v___x_242_; 
v___x_242_ = 1723ULL;
v___y_238_ = v___x_242_;
goto v___jp_237_;
}
else
{
uint64_t v_hash_243_; 
v_hash_243_ = lean_ctor_get_uint64(v_x_235_, sizeof(void*)*2);
v___y_238_ = v_hash_243_;
goto v___jp_237_;
}
v___jp_237_:
{
size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_uint64_to_usize(v___y_238_);
v___x_240_ = ((size_t)1ULL);
v___x_241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_234_, v___x_239_, v___x_240_, v_x_235_, v_x_236_);
return v___x_241_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_244_, lean_object* v_i_245_, lean_object* v_k_246_){
_start:
{
lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_247_ = lean_array_get_size(v_keys_244_);
v___x_248_ = lean_nat_dec_lt(v_i_245_, v___x_247_);
if (v___x_248_ == 0)
{
lean_dec(v_i_245_);
return v___x_248_;
}
else
{
lean_object* v_k_x27_249_; uint8_t v___x_250_; 
v_k_x27_249_ = lean_array_fget_borrowed(v_keys_244_, v_i_245_);
v___x_250_ = lean_name_eq(v_k_246_, v_k_x27_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(1u);
v___x_252_ = lean_nat_add(v_i_245_, v___x_251_);
lean_dec(v_i_245_);
v_i_245_ = v___x_252_;
goto _start;
}
else
{
lean_dec(v_i_245_);
return v___x_250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_254_, lean_object* v_i_255_, lean_object* v_k_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_254_, v_i_255_, v_k_256_);
lean_dec(v_k_256_);
lean_dec_ref(v_keys_254_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(lean_object* v_x_259_, size_t v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v_es_262_; lean_object* v___x_263_; size_t v___x_264_; size_t v___x_265_; lean_object* v_j_266_; lean_object* v___x_267_; 
v_es_262_ = lean_ctor_get(v_x_259_, 0);
v___x_263_ = lean_box(2);
v___x_264_ = ((size_t)31ULL);
v___x_265_ = lean_usize_land(v_x_260_, v___x_264_);
v_j_266_ = lean_usize_to_nat(v___x_265_);
v___x_267_ = lean_array_get_borrowed(v___x_263_, v_es_262_, v_j_266_);
lean_dec(v_j_266_);
switch(lean_obj_tag(v___x_267_))
{
case 0:
{
lean_object* v_key_268_; uint8_t v___x_269_; 
v_key_268_ = lean_ctor_get(v___x_267_, 0);
v___x_269_ = lean_name_eq(v_x_261_, v_key_268_);
return v___x_269_;
}
case 1:
{
lean_object* v_node_270_; size_t v___x_271_; size_t v___x_272_; 
v_node_270_ = lean_ctor_get(v___x_267_, 0);
v___x_271_ = ((size_t)5ULL);
v___x_272_ = lean_usize_shift_right(v_x_260_, v___x_271_);
v_x_259_ = v_node_270_;
v_x_260_ = v___x_272_;
goto _start;
}
default: 
{
uint8_t v___x_274_; 
v___x_274_ = 0;
return v___x_274_;
}
}
}
else
{
lean_object* v_ks_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_ks_275_ = lean_ctor_get(v_x_259_, 0);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_ks_275_, v___x_276_, v_x_261_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
size_t v_x_721__boxed_281_; uint8_t v_res_282_; lean_object* v_r_283_; 
v_x_721__boxed_281_ = lean_unbox_usize(v_x_279_);
lean_dec(v_x_279_);
v_res_282_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_278_, v_x_721__boxed_281_, v_x_280_);
lean_dec(v_x_280_);
lean_dec_ref(v_x_278_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
uint64_t v___y_287_; 
if (lean_obj_tag(v_x_285_) == 0)
{
uint64_t v___x_290_; 
v___x_290_ = 1723ULL;
v___y_287_ = v___x_290_;
goto v___jp_286_;
}
else
{
uint64_t v_hash_291_; 
v_hash_291_ = lean_ctor_get_uint64(v_x_285_, sizeof(void*)*2);
v___y_287_ = v_hash_291_;
goto v___jp_286_;
}
v___jp_286_:
{
size_t v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_uint64_to_usize(v___y_287_);
v___x_289_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_284_, v___x_288_, v_x_285_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg___boxed(lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
uint8_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_292_, v_x_293_);
lean_dec(v_x_293_);
lean_dec_ref(v_x_292_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object* v_categories_296_, lean_object* v_catName_297_, lean_object* v_initial_298_){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_296_, v_catName_297_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_296_, v_catName_297_, v_initial_298_);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
lean_dec_ref(v_initial_298_);
lean_dec_ref(v_categories_296_);
v___x_302_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_297_);
return v___x_302_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(lean_object* v_00_u03b2_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
uint8_t v___x_306_; 
v___x_306_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_304_, v_x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___boxed(lean_object* v_00_u03b2_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(v_00_u03b2_307_, v_x_308_, v_x_309_);
lean_dec(v_x_309_);
lean_dec_ref(v_x_308_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1(lean_object* v_00_u03b2_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_x_313_, v_x_314_, v_x_315_);
return v___x_316_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(lean_object* v_00_u03b2_317_, lean_object* v_x_318_, size_t v_x_319_, lean_object* v_x_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_318_, v_x_319_, v_x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_322_, lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
size_t v_x_802__boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v_x_802__boxed_326_ = lean_unbox_usize(v_x_324_);
lean_dec(v_x_324_);
v_res_327_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(v_00_u03b2_322_, v_x_323_, v_x_802__boxed_326_, v_x_325_);
lean_dec(v_x_325_);
lean_dec_ref(v_x_323_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(lean_object* v_00_u03b2_329_, lean_object* v_x_330_, size_t v_x_331_, size_t v_x_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_330_, v_x_331_, v_x_332_, v_x_333_, v_x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_336_, lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
size_t v_x_813__boxed_342_; size_t v_x_814__boxed_343_; lean_object* v_res_344_; 
v_x_813__boxed_342_ = lean_unbox_usize(v_x_338_);
lean_dec(v_x_338_);
v_x_814__boxed_343_ = lean_unbox_usize(v_x_339_);
lean_dec(v_x_339_);
v_res_344_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(v_00_u03b2_336_, v_x_337_, v_x_813__boxed_342_, v_x_814__boxed_343_, v_x_340_, v_x_341_);
return v_res_344_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_345_, lean_object* v_keys_346_, lean_object* v_vals_347_, lean_object* v_heq_348_, lean_object* v_i_349_, lean_object* v_k_350_){
_start:
{
uint8_t v___x_351_; 
v___x_351_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_346_, v_i_349_, v_k_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_352_, lean_object* v_keys_353_, lean_object* v_vals_354_, lean_object* v_heq_355_, lean_object* v_i_356_, lean_object* v_k_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(v_00_u03b2_352_, v_keys_353_, v_vals_354_, v_heq_355_, v_i_356_, v_k_357_);
lean_dec(v_k_357_);
lean_dec_ref(v_vals_354_);
lean_dec_ref(v_keys_353_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_360_, lean_object* v_n_361_, lean_object* v_k_362_, lean_object* v_v_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v_n_361_, v_k_362_, v_v_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_365_, size_t v_depth_366_, lean_object* v_keys_367_, lean_object* v_vals_368_, lean_object* v_heq_369_, lean_object* v_i_370_, lean_object* v_entries_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_366_, v_keys_367_, v_vals_368_, v_i_370_, v_entries_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_373_, lean_object* v_depth_374_, lean_object* v_keys_375_, lean_object* v_vals_376_, lean_object* v_heq_377_, lean_object* v_i_378_, lean_object* v_entries_379_){
_start:
{
size_t v_depth_boxed_380_; lean_object* v_res_381_; 
v_depth_boxed_380_ = lean_unbox_usize(v_depth_374_);
lean_dec(v_depth_374_);
v_res_381_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(v_00_u03b2_373_, v_depth_boxed_380_, v_keys_375_, v_vals_376_, v_heq_377_, v_i_378_, v_entries_379_);
lean_dec_ref(v_vals_376_);
lean_dec_ref(v_keys_375_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_x_383_, v_x_384_, v_x_385_, v_x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(lean_object* v_e_388_){
_start:
{
if (lean_obj_tag(v_e_388_) == 0)
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_398_; 
v_a_390_ = lean_ctor_get(v_e_388_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_e_388_);
if (v_isSharedCheck_398_ == 0)
{
v___x_392_ = v_e_388_;
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v_e_388_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_mk_io_user_error(v_a_390_);
if (v_isShared_393_ == 0)
{
lean_ctor_set_tag(v___x_392_, 1);
lean_ctor_set(v___x_392_, 0, v___x_394_);
v___x_396_ = v___x_392_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_399_ = lean_ctor_get(v_e_388_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_e_388_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v_e_388_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v_e_388_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 0);
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg___boxed(lean_object* v_e_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(lean_object* v_00_u03b1_410_, lean_object* v_e_411_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___boxed(lean_object* v_00_u03b1_414_, lean_object* v_e_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(v_00_u03b1_414_, v_e_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object* v_catName_421_, lean_object* v_declName_422_, uint8_t v_behavior_423_){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_425_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_426_ = lean_st_ref_get(v___x_425_);
v___x_427_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_428_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_429_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_429_, 0, v_declName_422_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
lean_ctor_set(v___x_429_, 2, v___x_428_);
lean_ctor_set_uint8(v___x_429_, sizeof(void*)*3, v_behavior_423_);
v___x_430_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(v___x_426_, v_catName_421_, v___x_429_);
v___x_431_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_430_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_441_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_441_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_436_ = lean_st_ref_swap(v___x_425_, v_a_432_);
lean_dec(v___x_436_);
v___x_437_ = lean_box(0);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_437_);
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_a_442_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_431_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_431_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object* v_catName_450_, lean_object* v_declName_451_, lean_object* v_behavior_452_, lean_object* v_a_453_){
_start:
{
uint8_t v_behavior_boxed_454_; lean_object* v_res_455_; 
v_behavior_boxed_454_ = lean_unbox(v_behavior_452_);
v_res_455_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_450_, v_declName_451_, v_behavior_boxed_454_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(lean_object* v_x_456_){
_start:
{
switch(lean_obj_tag(v_x_456_))
{
case 0:
{
lean_object* v___x_457_; 
v___x_457_ = lean_unsigned_to_nat(0u);
return v___x_457_;
}
case 1:
{
lean_object* v___x_458_; 
v___x_458_ = lean_unsigned_to_nat(1u);
return v___x_458_;
}
case 2:
{
lean_object* v___x_459_; 
v___x_459_ = lean_unsigned_to_nat(2u);
return v___x_459_;
}
default: 
{
lean_object* v___x_460_; 
v___x_460_ = lean_unsigned_to_nat(3u);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___boxed(lean_object* v_x_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(v_x_461_);
lean_dec_ref(v_x_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(lean_object* v_t_463_, lean_object* v_k_464_){
_start:
{
switch(lean_obj_tag(v_t_463_))
{
case 0:
{
lean_object* v_val_465_; lean_object* v___x_466_; 
v_val_465_ = lean_ctor_get(v_t_463_, 0);
lean_inc_ref(v_val_465_);
lean_dec_ref_known(v_t_463_, 1);
v___x_466_ = lean_apply_1(v_k_464_, v_val_465_);
return v___x_466_;
}
case 1:
{
lean_object* v_val_467_; lean_object* v___x_468_; 
v_val_467_ = lean_ctor_get(v_t_463_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v_t_463_, 1);
v___x_468_ = lean_apply_1(v_k_464_, v_val_467_);
return v___x_468_;
}
case 2:
{
lean_object* v_catName_469_; lean_object* v_declName_470_; uint8_t v_behavior_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_catName_469_ = lean_ctor_get(v_t_463_, 0);
lean_inc(v_catName_469_);
v_declName_470_ = lean_ctor_get(v_t_463_, 1);
lean_inc(v_declName_470_);
v_behavior_471_ = lean_ctor_get_uint8(v_t_463_, sizeof(void*)*2);
lean_dec_ref_known(v_t_463_, 2);
v___x_472_ = lean_box(v_behavior_471_);
v___x_473_ = lean_apply_3(v_k_464_, v_catName_469_, v_declName_470_, v___x_472_);
return v___x_473_;
}
default: 
{
lean_object* v_catName_474_; lean_object* v_declName_475_; lean_object* v_prio_476_; lean_object* v___x_477_; 
v_catName_474_ = lean_ctor_get(v_t_463_, 0);
lean_inc(v_catName_474_);
v_declName_475_ = lean_ctor_get(v_t_463_, 1);
lean_inc(v_declName_475_);
v_prio_476_ = lean_ctor_get(v_t_463_, 2);
lean_inc(v_prio_476_);
lean_dec_ref_known(v_t_463_, 3);
v___x_477_ = lean_apply_3(v_k_464_, v_catName_474_, v_declName_475_, v_prio_476_);
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(lean_object* v_motive_478_, lean_object* v_ctorIdx_479_, lean_object* v_t_480_, lean_object* v_h_481_, lean_object* v_k_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_480_, v_k_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___boxed(lean_object* v_motive_484_, lean_object* v_ctorIdx_485_, lean_object* v_t_486_, lean_object* v_h_487_, lean_object* v_k_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(v_motive_484_, v_ctorIdx_485_, v_t_486_, v_h_487_, v_k_488_);
lean_dec(v_ctorIdx_485_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim___redArg(lean_object* v_t_490_, lean_object* v_token_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_490_, v_token_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim(lean_object* v_motive_493_, lean_object* v_t_494_, lean_object* v_h_495_, lean_object* v_token_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_494_, v_token_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim___redArg(lean_object* v_t_498_, lean_object* v_kind_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_498_, v_kind_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim(lean_object* v_motive_501_, lean_object* v_t_502_, lean_object* v_h_503_, lean_object* v_kind_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_502_, v_kind_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim___redArg(lean_object* v_t_506_, lean_object* v_category_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_506_, v_category_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim(lean_object* v_motive_509_, lean_object* v_t_510_, lean_object* v_h_511_, lean_object* v_category_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_510_, v_category_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim___redArg(lean_object* v_t_514_, lean_object* v_parser_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_514_, v_parser_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim(lean_object* v_motive_517_, lean_object* v_t_518_, lean_object* v_h_519_, lean_object* v_parser_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_518_, v_parser_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx(lean_object* v_x_527_){
_start:
{
switch(lean_obj_tag(v_x_527_))
{
case 0:
{
lean_object* v___x_528_; 
v___x_528_ = lean_unsigned_to_nat(0u);
return v___x_528_;
}
case 1:
{
lean_object* v___x_529_; 
v___x_529_ = lean_unsigned_to_nat(1u);
return v___x_529_;
}
case 2:
{
lean_object* v___x_530_; 
v___x_530_ = lean_unsigned_to_nat(2u);
return v___x_530_;
}
default: 
{
lean_object* v___x_531_; 
v___x_531_ = lean_unsigned_to_nat(3u);
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___boxed(lean_object* v_x_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Parser_ParserExtension_Entry_ctorIdx(v_x_532_);
lean_dec_ref(v_x_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(lean_object* v_t_534_, lean_object* v_k_535_){
_start:
{
switch(lean_obj_tag(v_t_534_))
{
case 0:
{
lean_object* v_val_536_; lean_object* v___x_537_; 
v_val_536_ = lean_ctor_get(v_t_534_, 0);
lean_inc_ref(v_val_536_);
lean_dec_ref_known(v_t_534_, 1);
v___x_537_ = lean_apply_1(v_k_535_, v_val_536_);
return v___x_537_;
}
case 1:
{
lean_object* v_val_538_; lean_object* v___x_539_; 
v_val_538_ = lean_ctor_get(v_t_534_, 0);
lean_inc(v_val_538_);
lean_dec_ref_known(v_t_534_, 1);
v___x_539_ = lean_apply_1(v_k_535_, v_val_538_);
return v___x_539_;
}
case 2:
{
lean_object* v_catName_540_; lean_object* v_declName_541_; uint8_t v_behavior_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_catName_540_ = lean_ctor_get(v_t_534_, 0);
lean_inc(v_catName_540_);
v_declName_541_ = lean_ctor_get(v_t_534_, 1);
lean_inc(v_declName_541_);
v_behavior_542_ = lean_ctor_get_uint8(v_t_534_, sizeof(void*)*2);
lean_dec_ref_known(v_t_534_, 2);
v___x_543_ = lean_box(v_behavior_542_);
v___x_544_ = lean_apply_3(v_k_535_, v_catName_540_, v_declName_541_, v___x_543_);
return v___x_544_;
}
default: 
{
lean_object* v_catName_545_; lean_object* v_declName_546_; uint8_t v_leading_547_; lean_object* v_p_548_; lean_object* v_prio_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_catName_545_ = lean_ctor_get(v_t_534_, 0);
lean_inc(v_catName_545_);
v_declName_546_ = lean_ctor_get(v_t_534_, 1);
lean_inc(v_declName_546_);
v_leading_547_ = lean_ctor_get_uint8(v_t_534_, sizeof(void*)*4);
v_p_548_ = lean_ctor_get(v_t_534_, 2);
lean_inc_ref(v_p_548_);
v_prio_549_ = lean_ctor_get(v_t_534_, 3);
lean_inc(v_prio_549_);
lean_dec_ref_known(v_t_534_, 4);
v___x_550_ = lean_box(v_leading_547_);
v___x_551_ = lean_apply_5(v_k_535_, v_catName_545_, v_declName_546_, v___x_550_, v_p_548_, v_prio_549_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim(lean_object* v_motive_552_, lean_object* v_ctorIdx_553_, lean_object* v_t_554_, lean_object* v_h_555_, lean_object* v_k_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_554_, v_k_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___boxed(lean_object* v_motive_558_, lean_object* v_ctorIdx_559_, lean_object* v_t_560_, lean_object* v_h_561_, lean_object* v_k_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Parser_ParserExtension_Entry_ctorElim(v_motive_558_, v_ctorIdx_559_, v_t_560_, v_h_561_, v_k_562_);
lean_dec(v_ctorIdx_559_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim___redArg(lean_object* v_t_564_, lean_object* v_token_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_564_, v_token_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim(lean_object* v_motive_567_, lean_object* v_t_568_, lean_object* v_h_569_, lean_object* v_token_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_568_, v_token_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim___redArg(lean_object* v_t_572_, lean_object* v_kind_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_572_, v_kind_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim(lean_object* v_motive_575_, lean_object* v_t_576_, lean_object* v_h_577_, lean_object* v_kind_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_576_, v_kind_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim___redArg(lean_object* v_t_580_, lean_object* v_category_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_580_, v_category_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim(lean_object* v_motive_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_category_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_584_, v_category_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim___redArg(lean_object* v_t_588_, lean_object* v_parser_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_588_, v_parser_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim(lean_object* v_motive_591_, lean_object* v_t_592_, lean_object* v_h_593_, lean_object* v_parser_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_592_, v_parser_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object* v_x_600_){
_start:
{
switch(lean_obj_tag(v_x_600_))
{
case 0:
{
lean_object* v_val_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
v_val_601_ = lean_ctor_get(v_x_600_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v_x_600_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v_x_600_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_val_601_);
lean_dec(v_x_600_);
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
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_val_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
case 1:
{
lean_object* v_val_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_val_609_ = lean_ctor_get(v_x_600_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v_x_600_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v_x_600_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_val_609_);
lean_dec(v_x_600_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_val_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
case 2:
{
lean_object* v_catName_617_; lean_object* v_declName_618_; uint8_t v_behavior_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
v_catName_617_ = lean_ctor_get(v_x_600_, 0);
v_declName_618_ = lean_ctor_get(v_x_600_, 1);
v_behavior_619_ = lean_ctor_get_uint8(v_x_600_, sizeof(void*)*2);
v_isSharedCheck_626_ = !lean_is_exclusive(v_x_600_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v_x_600_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_declName_618_);
lean_inc(v_catName_617_);
lean_dec(v_x_600_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_catName_617_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_declName_618_);
lean_ctor_set_uint8(v_reuseFailAlloc_625_, sizeof(void*)*2, v_behavior_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
default: 
{
lean_object* v_catName_627_; lean_object* v_declName_628_; lean_object* v_prio_629_; lean_object* v___x_630_; 
v_catName_627_ = lean_ctor_get(v_x_600_, 0);
lean_inc(v_catName_627_);
v_declName_628_ = lean_ctor_get(v_x_600_, 1);
lean_inc(v_declName_628_);
v_prio_629_ = lean_ctor_get(v_x_600_, 3);
lean_inc(v_prio_629_);
lean_dec_ref_known(v_x_600_, 4);
v___x_630_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_630_, 0, v_catName_627_);
lean_ctor_set(v___x_630_, 1, v_declName_628_);
lean_ctor_set(v___x_630_, 2, v_prio_629_);
return v___x_630_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_632_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
lean_ctor_set(v___x_633_, 2, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default(void){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_once(&l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0, &l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0_once, _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState(void){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_637_ = l_Lean_Parser_builtinTokenTable;
v___x_638_ = lean_st_ref_get(v___x_637_);
v___x_639_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_640_ = lean_st_ref_get(v___x_639_);
v___x_641_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_642_ = lean_st_ref_get(v___x_641_);
v___x_643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_643_, 0, v___x_638_);
lean_ctor_set(v___x_643_, 1, v___x_640_);
lean_ctor_set(v___x_643_, 2, v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object* v_tokens_650_, lean_object* v_tk_651_){
_start:
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = ((lean_object*)(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0));
v___x_653_ = lean_string_dec_eq(v_tk_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Data_Trie_find_x3f___redArg(v_tokens_650_, v_tk_651_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; 
lean_inc_ref(v_tk_651_);
v___x_655_ = l_Lean_Data_Trie_insert___redArg(v_tokens_650_, v_tk_651_, v_tk_651_);
lean_dec_ref(v_tk_651_);
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
else
{
lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec_ref(v_tk_651_);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v___x_654_, 0);
lean_dec(v_unused_664_);
v___x_658_ = v___x_654_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_dec(v___x_654_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v_tokens_650_);
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_tokens_650_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_object* v___x_665_; 
lean_dec_ref(v_tk_651_);
lean_dec_ref(v_tokens_650_);
v___x_665_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1));
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg(lean_object* v_catName_668_){
_start:
{
lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_669_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0));
v___x_670_ = 1;
v___x_671_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_668_, v___x_670_);
v___x_672_ = lean_string_append(v___x_669_, v___x_671_);
lean_dec_ref(v___x_671_);
v___x_673_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_674_ = lean_string_append(v___x_672_, v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object* v_00_u03b1_676_, lean_object* v_catName_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object* v_categories_681_, lean_object* v_catName_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__0));
v___x_684_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__1));
v___x_685_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_683_, v___x_684_, v_categories_681_, v_catName_682_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory___boxed(lean_object* v_categories_686_, lean_object* v_catName_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Parser_getCategory(v_categories_686_, v_catName_687_);
lean_dec_ref(v_categories_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(lean_object* v_as_690_){
_start:
{
lean_object* v___f_691_; lean_object* v___x_692_; 
v___f_691_ = ((lean_object*)(l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0));
v___x_692_ = l_List_eraseDupsBy___redArg(v___f_691_, v_as_690_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(lean_object* v_p_693_, lean_object* v_prio_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
if (lean_obj_tag(v_x_696_) == 0)
{
lean_dec(v_prio_694_);
lean_dec_ref(v_p_693_);
return v_x_695_;
}
else
{
lean_object* v_head_697_; lean_object* v_tail_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_718_; 
v_head_697_ = lean_ctor_get(v_x_696_, 0);
v_tail_698_ = lean_ctor_get(v_x_696_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_x_696_);
if (v_isSharedCheck_718_ == 0)
{
v___x_700_ = v_x_696_;
v_isShared_701_ = v_isSharedCheck_718_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_tail_698_);
lean_inc(v_head_697_);
lean_dec(v_x_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_718_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v_leadingTable_702_; lean_object* v_leadingParsers_703_; lean_object* v_trailingTable_704_; lean_object* v_trailingParsers_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_717_; 
v_leadingTable_702_ = lean_ctor_get(v_x_695_, 0);
v_leadingParsers_703_ = lean_ctor_get(v_x_695_, 1);
v_trailingTable_704_ = lean_ctor_get(v_x_695_, 2);
v_trailingParsers_705_ = lean_ctor_get(v_x_695_, 3);
v_isSharedCheck_717_ = !lean_is_exclusive(v_x_695_);
if (v_isSharedCheck_717_ == 0)
{
v___x_707_ = v_x_695_;
v_isShared_708_ = v_isSharedCheck_717_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_trailingParsers_705_);
lean_inc(v_trailingTable_704_);
lean_inc(v_leadingParsers_703_);
lean_inc(v_leadingTable_702_);
lean_dec(v_x_695_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_717_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
lean_inc(v_prio_694_);
lean_inc_ref(v_p_693_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 0);
lean_ctor_set(v___x_700_, 1, v_prio_694_);
lean_ctor_set(v___x_700_, 0, v_p_693_);
v___x_710_ = v___x_700_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_p_693_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_prio_694_);
v___x_710_ = v_reuseFailAlloc_716_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = l_Lean_Parser_TokenMap_insert___redArg(v_leadingTable_702_, v_head_697_, v___x_710_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_711_);
v___x_713_ = v___x_707_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_leadingParsers_703_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_trailingTable_704_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_trailingParsers_705_);
v___x_713_ = v_reuseFailAlloc_715_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
v_x_695_ = v___x_713_;
v_x_696_ = v_tail_698_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_719_, lean_object* v_vals_720_, lean_object* v_i_721_, lean_object* v_k_722_){
_start:
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = lean_array_get_size(v_keys_719_);
v___x_724_ = lean_nat_dec_lt(v_i_721_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
lean_dec(v_i_721_);
v___x_725_ = lean_box(0);
return v___x_725_;
}
else
{
lean_object* v_k_x27_726_; uint8_t v___x_727_; 
v_k_x27_726_ = lean_array_fget_borrowed(v_keys_719_, v_i_721_);
v___x_727_ = lean_name_eq(v_k_722_, v_k_x27_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_nat_add(v_i_721_, v___x_728_);
lean_dec(v_i_721_);
v_i_721_ = v___x_729_;
goto _start;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_array_fget_borrowed(v_vals_720_, v_i_721_);
lean_dec(v_i_721_);
lean_inc(v___x_731_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_733_, lean_object* v_vals_734_, lean_object* v_i_735_, lean_object* v_k_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_733_, v_vals_734_, v_i_735_, v_k_736_);
lean_dec(v_k_736_);
lean_dec_ref(v_vals_734_);
lean_dec_ref(v_keys_733_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(lean_object* v_x_738_, size_t v_x_739_, lean_object* v_x_740_){
_start:
{
if (lean_obj_tag(v_x_738_) == 0)
{
lean_object* v_es_741_; lean_object* v___x_742_; size_t v___x_743_; size_t v___x_744_; lean_object* v_j_745_; lean_object* v___x_746_; 
v_es_741_ = lean_ctor_get(v_x_738_, 0);
v___x_742_ = lean_box(2);
v___x_743_ = ((size_t)31ULL);
v___x_744_ = lean_usize_land(v_x_739_, v___x_743_);
v_j_745_ = lean_usize_to_nat(v___x_744_);
v___x_746_ = lean_array_get_borrowed(v___x_742_, v_es_741_, v_j_745_);
lean_dec(v_j_745_);
switch(lean_obj_tag(v___x_746_))
{
case 0:
{
lean_object* v_key_747_; lean_object* v_val_748_; uint8_t v___x_749_; 
v_key_747_ = lean_ctor_get(v___x_746_, 0);
v_val_748_ = lean_ctor_get(v___x_746_, 1);
v___x_749_ = lean_name_eq(v_x_740_, v_key_747_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
v___x_750_ = lean_box(0);
return v___x_750_;
}
else
{
lean_object* v___x_751_; 
lean_inc(v_val_748_);
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v_val_748_);
return v___x_751_;
}
}
case 1:
{
lean_object* v_node_752_; size_t v___x_753_; size_t v___x_754_; 
v_node_752_ = lean_ctor_get(v___x_746_, 0);
v___x_753_ = ((size_t)5ULL);
v___x_754_ = lean_usize_shift_right(v_x_739_, v___x_753_);
v_x_738_ = v_node_752_;
v_x_739_ = v___x_754_;
goto _start;
}
default: 
{
lean_object* v___x_756_; 
v___x_756_ = lean_box(0);
return v___x_756_;
}
}
}
else
{
lean_object* v_ks_757_; lean_object* v_vs_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_ks_757_ = lean_ctor_get(v_x_738_, 0);
v_vs_758_ = lean_ctor_get(v_x_738_, 1);
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_ks_757_, v_vs_758_, v___x_759_, v_x_740_);
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg___boxed(lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
size_t v_x_492__boxed_764_; lean_object* v_res_765_; 
v_x_492__boxed_764_ = lean_unbox_usize(v_x_762_);
lean_dec(v_x_762_);
v_res_765_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_761_, v_x_492__boxed_764_, v_x_763_);
lean_dec(v_x_763_);
lean_dec_ref(v_x_761_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
uint64_t v___y_769_; 
if (lean_obj_tag(v_x_767_) == 0)
{
uint64_t v___x_772_; 
v___x_772_ = 1723ULL;
v___y_769_ = v___x_772_;
goto v___jp_768_;
}
else
{
uint64_t v_hash_773_; 
v_hash_773_ = lean_ctor_get_uint64(v_x_767_, sizeof(void*)*2);
v___y_769_ = v_hash_773_;
goto v___jp_768_;
}
v___jp_768_:
{
size_t v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_uint64_to_usize(v___y_769_);
v___x_771_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_766_, v___x_770_, v_x_767_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg___boxed(lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_774_, v_x_775_);
lean_dec(v_x_775_);
lean_dec_ref(v_x_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
if (lean_obj_tag(v_a_777_) == 0)
{
lean_object* v___x_779_; 
v___x_779_ = l_List_reverse___redArg(v_a_778_);
return v___x_779_;
}
else
{
lean_object* v_head_780_; lean_object* v_tail_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_791_; 
v_head_780_ = lean_ctor_get(v_a_777_, 0);
v_tail_781_ = lean_ctor_get(v_a_777_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_a_777_);
if (v_isSharedCheck_791_ == 0)
{
v___x_783_ = v_a_777_;
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_tail_781_);
lean_inc(v_head_780_);
lean_dec(v_a_777_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = lean_box(0);
v___x_786_ = l_Lean_Name_str___override(v___x_785_, v_head_780_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v_a_778_);
lean_ctor_set(v___x_783_, 0, v___x_786_);
v___x_788_ = v___x_783_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_a_778_);
v___x_788_ = v_reuseFailAlloc_790_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
v_a_777_ = v_tail_781_;
v_a_778_ = v___x_788_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object* v_categories_792_, lean_object* v_catName_793_, lean_object* v_declName_794_, lean_object* v_p_795_, lean_object* v_prio_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_792_, v_catName_793_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v___x_798_; 
lean_dec(v_prio_796_);
lean_dec_ref(v_p_795_);
lean_dec(v_declName_794_);
lean_dec_ref(v_categories_792_);
v___x_798_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_793_);
return v___x_798_;
}
else
{
lean_object* v_val_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_845_; 
v_val_799_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_845_ == 0)
{
v___x_801_ = v___x_797_;
v_isShared_802_ = v_isSharedCheck_845_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_val_799_);
lean_dec(v___x_797_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_845_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_info_803_; lean_object* v_declName_804_; lean_object* v_kinds_805_; lean_object* v_tables_806_; uint8_t v_behavior_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_844_; 
v_info_803_ = lean_ctor_get(v_p_795_, 0);
v_declName_804_ = lean_ctor_get(v_val_799_, 0);
v_kinds_805_ = lean_ctor_get(v_val_799_, 1);
v_tables_806_ = lean_ctor_get(v_val_799_, 2);
v_behavior_807_ = lean_ctor_get_uint8(v_val_799_, sizeof(void*)*3);
v_isSharedCheck_844_ = !lean_is_exclusive(v_val_799_);
if (v_isSharedCheck_844_ == 0)
{
v___x_809_ = v_val_799_;
v_isShared_810_ = v_isSharedCheck_844_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_tables_806_);
lean_inc(v_kinds_805_);
lean_inc(v_declName_804_);
lean_dec(v_val_799_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_844_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_firstTokens_811_; lean_object* v_kinds_812_; lean_object* v_tks_814_; 
v_firstTokens_811_ = lean_ctor_get(v_info_803_, 2);
v_kinds_812_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_805_, v_declName_794_);
switch(lean_obj_tag(v_firstTokens_811_))
{
case 2:
{
lean_object* v_a_826_; 
v_a_826_ = lean_ctor_get(v_firstTokens_811_, 0);
lean_inc(v_a_826_);
v_tks_814_ = v_a_826_;
goto v___jp_813_;
}
case 3:
{
lean_object* v_a_827_; 
v_a_827_ = lean_ctor_get(v_firstTokens_811_, 0);
lean_inc(v_a_827_);
v_tks_814_ = v_a_827_;
goto v___jp_813_;
}
default: 
{
lean_object* v_leadingTable_828_; lean_object* v_leadingParsers_829_; lean_object* v_trailingTable_830_; lean_object* v_trailingParsers_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_843_; 
lean_del_object(v___x_809_);
lean_del_object(v___x_801_);
v_leadingTable_828_ = lean_ctor_get(v_tables_806_, 0);
v_leadingParsers_829_ = lean_ctor_get(v_tables_806_, 1);
v_trailingTable_830_ = lean_ctor_get(v_tables_806_, 2);
v_trailingParsers_831_ = lean_ctor_get(v_tables_806_, 3);
v_isSharedCheck_843_ = !lean_is_exclusive(v_tables_806_);
if (v_isSharedCheck_843_ == 0)
{
v___x_833_ = v_tables_806_;
v_isShared_834_ = v_isSharedCheck_843_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_trailingParsers_831_);
lean_inc(v_trailingTable_830_);
lean_inc(v_leadingParsers_829_);
lean_inc(v_leadingTable_828_);
lean_dec(v_tables_806_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_843_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v_tables_838_; 
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_p_795_);
lean_ctor_set(v___x_835_, 1, v_prio_796_);
v___x_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_leadingParsers_829_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v___x_836_);
v_tables_838_ = v___x_833_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_leadingTable_828_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_trailingTable_830_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_trailingParsers_831_);
v_tables_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_839_, 0, v_declName_804_);
lean_ctor_set(v___x_839_, 1, v_kinds_812_);
lean_ctor_set(v___x_839_, 2, v_tables_838_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*3, v_behavior_807_);
v___x_840_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_792_, v_catName_793_, v___x_839_);
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
}
v___jp_813_:
{
lean_object* v___x_815_; lean_object* v_tks_816_; lean_object* v___x_817_; lean_object* v_tables_818_; lean_object* v___x_820_; 
v___x_815_ = lean_box(0);
v_tks_816_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_814_, v___x_815_);
v___x_817_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_816_);
v_tables_818_ = l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(v_p_795_, v_prio_796_, v_tables_806_, v___x_817_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 2, v_tables_818_);
lean_ctor_set(v___x_809_, 1, v_kinds_812_);
v___x_820_ = v___x_809_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_declName_804_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_kinds_812_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_tables_818_);
lean_ctor_set_uint8(v_reuseFailAlloc_825_, sizeof(void*)*3, v_behavior_807_);
v___x_820_ = v_reuseFailAlloc_825_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_792_, v_catName_793_, v___x_820_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_821_);
v___x_823_ = v___x_801_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(lean_object* v_00_u03b2_846_, lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_847_, v_x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___boxed(lean_object* v_00_u03b2_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(v_00_u03b2_850_, v_x_851_, v_x_852_);
lean_dec(v_x_852_);
lean_dec_ref(v_x_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_object* v_00_u03b2_854_, lean_object* v_x_855_, size_t v_x_856_, lean_object* v_x_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_855_, v_x_856_, v_x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___boxed(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
size_t v_x_661__boxed_863_; lean_object* v_res_864_; 
v_x_661__boxed_863_ = lean_unbox_usize(v_x_861_);
lean_dec(v_x_861_);
v_res_864_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(v_00_u03b2_859_, v_x_860_, v_x_661__boxed_863_, v_x_862_);
lean_dec(v_x_862_);
lean_dec_ref(v_x_860_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_865_, lean_object* v_keys_866_, lean_object* v_vals_867_, lean_object* v_heq_868_, lean_object* v_i_869_, lean_object* v_k_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_866_, v_vals_867_, v_i_869_, v_k_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_872_, lean_object* v_keys_873_, lean_object* v_vals_874_, lean_object* v_heq_875_, lean_object* v_i_876_, lean_object* v_k_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(v_00_u03b2_872_, v_keys_873_, v_vals_874_, v_heq_875_, v_i_876_, v_k_877_);
lean_dec(v_k_877_);
lean_dec_ref(v_vals_874_);
lean_dec_ref(v_keys_873_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(lean_object* v_p_879_, lean_object* v_prio_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
lean_dec(v_prio_880_);
lean_dec_ref(v_p_879_);
return v_x_881_;
}
else
{
lean_object* v_head_883_; lean_object* v_tail_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_904_; 
v_head_883_ = lean_ctor_get(v_x_882_, 0);
v_tail_884_ = lean_ctor_get(v_x_882_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_x_882_);
if (v_isSharedCheck_904_ == 0)
{
v___x_886_ = v_x_882_;
v_isShared_887_ = v_isSharedCheck_904_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_tail_884_);
lean_inc(v_head_883_);
lean_dec(v_x_882_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_904_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_leadingTable_888_; lean_object* v_leadingParsers_889_; lean_object* v_trailingTable_890_; lean_object* v_trailingParsers_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_903_; 
v_leadingTable_888_ = lean_ctor_get(v_x_881_, 0);
v_leadingParsers_889_ = lean_ctor_get(v_x_881_, 1);
v_trailingTable_890_ = lean_ctor_get(v_x_881_, 2);
v_trailingParsers_891_ = lean_ctor_get(v_x_881_, 3);
v_isSharedCheck_903_ = !lean_is_exclusive(v_x_881_);
if (v_isSharedCheck_903_ == 0)
{
v___x_893_ = v_x_881_;
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_trailingParsers_891_);
lean_inc(v_trailingTable_890_);
lean_inc(v_leadingParsers_889_);
lean_inc(v_leadingTable_888_);
lean_dec(v_x_881_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
lean_inc(v_prio_880_);
lean_inc_ref(v_p_879_);
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 0);
lean_ctor_set(v___x_886_, 1, v_prio_880_);
lean_ctor_set(v___x_886_, 0, v_p_879_);
v___x_896_ = v___x_886_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_p_879_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_prio_880_);
v___x_896_ = v_reuseFailAlloc_902_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = l_Lean_Parser_TokenMap_insert___redArg(v_trailingTable_890_, v_head_883_, v___x_896_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 2, v___x_897_);
v___x_899_ = v___x_893_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_leadingTable_888_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_leadingParsers_889_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v_trailingParsers_891_);
v___x_899_ = v_reuseFailAlloc_901_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
v_x_881_ = v___x_899_;
v_x_882_ = v_tail_884_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object* v_tables_905_, lean_object* v_p_906_, lean_object* v_prio_907_){
_start:
{
lean_object* v_tks_909_; lean_object* v_info_914_; lean_object* v_firstTokens_915_; 
v_info_914_ = lean_ctor_get(v_p_906_, 0);
v_firstTokens_915_ = lean_ctor_get(v_info_914_, 2);
switch(lean_obj_tag(v_firstTokens_915_))
{
case 2:
{
lean_object* v_a_916_; 
v_a_916_ = lean_ctor_get(v_firstTokens_915_, 0);
lean_inc(v_a_916_);
v_tks_909_ = v_a_916_;
goto v___jp_908_;
}
case 3:
{
lean_object* v_a_917_; 
v_a_917_ = lean_ctor_get(v_firstTokens_915_, 0);
lean_inc(v_a_917_);
v_tks_909_ = v_a_917_;
goto v___jp_908_;
}
default: 
{
lean_object* v_leadingTable_918_; lean_object* v_leadingParsers_919_; lean_object* v_trailingTable_920_; lean_object* v_trailingParsers_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_930_; 
v_leadingTable_918_ = lean_ctor_get(v_tables_905_, 0);
v_leadingParsers_919_ = lean_ctor_get(v_tables_905_, 1);
v_trailingTable_920_ = lean_ctor_get(v_tables_905_, 2);
v_trailingParsers_921_ = lean_ctor_get(v_tables_905_, 3);
v_isSharedCheck_930_ = !lean_is_exclusive(v_tables_905_);
if (v_isSharedCheck_930_ == 0)
{
v___x_923_ = v_tables_905_;
v_isShared_924_ = v_isSharedCheck_930_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_trailingParsers_921_);
lean_inc(v_trailingTable_920_);
lean_inc(v_leadingParsers_919_);
lean_inc(v_leadingTable_918_);
lean_dec(v_tables_905_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_930_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v_p_906_);
lean_ctor_set(v___x_925_, 1, v_prio_907_);
v___x_926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v_trailingParsers_921_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 3, v___x_926_);
v___x_928_ = v___x_923_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_leadingTable_918_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_leadingParsers_919_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_trailingTable_920_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
v___jp_908_:
{
lean_object* v___x_910_; lean_object* v_tks_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_910_ = lean_box(0);
v_tks_911_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_909_, v___x_910_);
v___x_912_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_911_);
v___x_913_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(v_p_906_, v_prio_907_, v_tables_905_, v___x_912_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object* v_categories_931_, lean_object* v_catName_932_, lean_object* v_declName_933_, lean_object* v_p_934_, lean_object* v_prio_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_931_, v_catName_932_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v___x_937_; 
lean_dec(v_prio_935_);
lean_dec_ref(v_p_934_);
lean_dec(v_declName_933_);
lean_dec_ref(v_categories_931_);
v___x_937_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_932_);
return v___x_937_;
}
else
{
lean_object* v_val_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_959_; 
v_val_938_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_959_ == 0)
{
v___x_940_ = v___x_936_;
v_isShared_941_ = v_isSharedCheck_959_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_val_938_);
lean_dec(v___x_936_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_959_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_declName_942_; lean_object* v_kinds_943_; lean_object* v_tables_944_; uint8_t v_behavior_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_958_; 
v_declName_942_ = lean_ctor_get(v_val_938_, 0);
v_kinds_943_ = lean_ctor_get(v_val_938_, 1);
v_tables_944_ = lean_ctor_get(v_val_938_, 2);
v_behavior_945_ = lean_ctor_get_uint8(v_val_938_, sizeof(void*)*3);
v_isSharedCheck_958_ = !lean_is_exclusive(v_val_938_);
if (v_isSharedCheck_958_ == 0)
{
v___x_947_ = v_val_938_;
v_isShared_948_ = v_isSharedCheck_958_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_tables_944_);
lean_inc(v_kinds_943_);
lean_inc(v_declName_942_);
lean_dec(v_val_938_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_958_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_kinds_949_; lean_object* v_tables_950_; lean_object* v___x_952_; 
v_kinds_949_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_943_, v_declName_933_);
v_tables_950_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(v_tables_944_, v_p_934_, v_prio_935_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 2, v_tables_950_);
lean_ctor_set(v___x_947_, 1, v_kinds_949_);
v___x_952_ = v___x_947_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_declName_942_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_kinds_949_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_tables_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_957_, sizeof(void*)*3, v_behavior_945_);
v___x_952_ = v_reuseFailAlloc_957_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_953_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_931_, v_catName_932_, v___x_952_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_953_);
v___x_955_ = v___x_940_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object* v_categories_960_, lean_object* v_catName_961_, lean_object* v_declName_962_, uint8_t v_leading_963_, lean_object* v_p_964_, lean_object* v_prio_965_){
_start:
{
if (v_leading_963_ == 0)
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Parser_addTrailingParser(v_categories_960_, v_catName_961_, v_declName_962_, v_p_964_, v_prio_965_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Parser_addLeadingParser(v_categories_960_, v_catName_961_, v_declName_962_, v_p_964_, v_prio_965_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object* v_categories_968_, lean_object* v_catName_969_, lean_object* v_declName_970_, lean_object* v_leading_971_, lean_object* v_p_972_, lean_object* v_prio_973_){
_start:
{
uint8_t v_leading_boxed_974_; lean_object* v_res_975_; 
v_leading_boxed_974_ = lean_unbox(v_leading_971_);
v_res_975_ = l_Lean_Parser_addParser(v_categories_968_, v_catName_969_, v_declName_970_, v_leading_boxed_974_, v_p_972_, v_prio_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
if (lean_obj_tag(v_x_977_) == 0)
{
lean_object* v___x_978_; 
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v_x_976_);
return v___x_978_;
}
else
{
lean_object* v_head_979_; lean_object* v_tail_980_; lean_object* v___x_981_; 
v_head_979_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_head_979_);
v_tail_980_ = lean_ctor_get(v_x_977_, 1);
lean_inc(v_tail_980_);
lean_dec_ref_known(v_x_977_, 2);
v___x_981_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_x_976_, v_head_979_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_dec(v_tail_980_);
return v___x_981_;
}
else
{
lean_object* v_a_982_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v_x_976_ = v_a_982_;
v_x_977_ = v_tail_980_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object* v_tokenTable_984_, lean_object* v_info_985_){
_start:
{
lean_object* v_collectTokens_986_; lean_object* v___x_987_; lean_object* v_newTokens_988_; lean_object* v___x_989_; 
v_collectTokens_986_ = lean_ctor_get(v_info_985_, 0);
lean_inc_ref(v_collectTokens_986_);
lean_dec_ref(v_info_985_);
v___x_987_ = lean_box(0);
v_newTokens_988_ = lean_apply_1(v_collectTokens_986_, v___x_987_);
v___x_989_ = l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(v_tokenTable_984_, v_newTokens_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object* v_info_992_, lean_object* v_declName_993_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_995_ = l_Lean_Parser_builtinTokenTable;
v___x_996_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_997_ = lean_st_ref_swap(v___x_995_, v___x_996_);
v___x_998_ = l_Lean_Parser_addParserTokens(v___x_997_, v_info_992_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1015_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1015_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1015_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1003_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0));
v___x_1004_ = l_Lean_privateToUserName(v_declName_993_);
v___x_1005_ = 1;
v___x_1006_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1004_, v___x_1005_);
v___x_1007_ = lean_string_append(v___x_1003_, v___x_1006_);
lean_dec_ref(v___x_1006_);
v___x_1008_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_1009_ = lean_string_append(v___x_1007_, v___x_1008_);
v___x_1010_ = lean_string_append(v___x_1009_, v_a_999_);
lean_dec(v_a_999_);
v___x_1011_ = lean_mk_io_user_error(v___x_1010_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set_tag(v___x_1001_, 1);
lean_ctor_set(v___x_1001_, 0, v___x_1011_);
v___x_1013_ = v___x_1001_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v_declName_993_);
v_a_1016_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1018_ = v___x_998_;
v_isShared_1019_ = v_isSharedCheck_1025_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_998_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1025_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1020_ = lean_st_ref_swap(v___x_995_, v_a_1016_);
lean_dec(v___x_1020_);
v___x_1021_ = lean_box(0);
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1021_);
v___x_1023_ = v___x_1018_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___boxed(lean_object* v_info_1026_, lean_object* v_declName_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_1026_, v_declName_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(lean_object* v_msg_1030_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1032_ = lean_panic_fn_borrowed(v___x_1031_, v_msg_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object* v_s_1036_, lean_object* v_e_1037_){
_start:
{
switch(lean_obj_tag(v_e_1037_))
{
case 0:
{
lean_object* v_val_1038_; lean_object* v_tokens_1039_; lean_object* v_kinds_1040_; lean_object* v_categories_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1059_; 
v_val_1038_ = lean_ctor_get(v_e_1037_, 0);
lean_inc_ref(v_val_1038_);
lean_dec_ref_known(v_e_1037_, 1);
v_tokens_1039_ = lean_ctor_get(v_s_1036_, 0);
v_kinds_1040_ = lean_ctor_get(v_s_1036_, 1);
v_categories_1041_ = lean_ctor_get(v_s_1036_, 2);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_s_1036_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1043_ = v_s_1036_;
v_isShared_1044_ = v_isSharedCheck_1059_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_categories_1041_);
lean_inc(v_kinds_1040_);
lean_inc(v_tokens_1039_);
lean_dec(v_s_1036_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1059_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; 
v___x_1045_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_1039_, v_val_1038_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_del_object(v___x_1043_);
lean_dec_ref(v_categories_1041_);
lean_dec_ref(v_kinds_1040_);
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1048_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1049_ = lean_unsigned_to_nat(163u);
v___x_1050_ = lean_unsigned_to_nat(26u);
v___x_1051_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1052_ = lean_string_append(v___x_1051_, v_a_1046_);
lean_dec(v_a_1046_);
v___x_1053_ = l_mkPanicMessageWithDecl(v___x_1047_, v___x_1048_, v___x_1049_, v___x_1050_, v___x_1052_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1053_);
return v___x_1054_;
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; 
v_a_1055_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1045_, 1);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v_a_1055_);
v___x_1057_ = v___x_1043_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1055_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_kinds_1040_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_categories_1041_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
case 1:
{
lean_object* v_val_1060_; lean_object* v_tokens_1061_; lean_object* v_kinds_1062_; lean_object* v_categories_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1071_; 
v_val_1060_ = lean_ctor_get(v_e_1037_, 0);
lean_inc(v_val_1060_);
lean_dec_ref_known(v_e_1037_, 1);
v_tokens_1061_ = lean_ctor_get(v_s_1036_, 0);
v_kinds_1062_ = lean_ctor_get(v_s_1036_, 1);
v_categories_1063_ = lean_ctor_get(v_s_1036_, 2);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_s_1036_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1065_ = v_s_1036_;
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_categories_1063_);
lean_inc(v_kinds_1062_);
lean_inc(v_tokens_1061_);
lean_dec(v_s_1036_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_1062_, v_val_1060_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 1, v___x_1067_);
v___x_1069_ = v___x_1065_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_tokens_1061_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_categories_1063_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
case 2:
{
lean_object* v_catName_1072_; lean_object* v_declName_1073_; uint8_t v_behavior_1074_; lean_object* v_tokens_1075_; lean_object* v_kinds_1076_; lean_object* v_categories_1077_; uint8_t v___x_1078_; 
v_catName_1072_ = lean_ctor_get(v_e_1037_, 0);
lean_inc(v_catName_1072_);
v_declName_1073_ = lean_ctor_get(v_e_1037_, 1);
lean_inc(v_declName_1073_);
v_behavior_1074_ = lean_ctor_get_uint8(v_e_1037_, sizeof(void*)*2);
lean_dec_ref_known(v_e_1037_, 2);
v_tokens_1075_ = lean_ctor_get(v_s_1036_, 0);
v_kinds_1076_ = lean_ctor_get(v_s_1036_, 1);
v_categories_1077_ = lean_ctor_get(v_s_1036_, 2);
v___x_1078_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_1077_, v_catName_1072_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1089_; 
lean_inc_ref(v_categories_1077_);
lean_inc_ref(v_kinds_1076_);
lean_inc_ref(v_tokens_1075_);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_s_1036_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; lean_object* v_unused_1091_; lean_object* v_unused_1092_; 
v_unused_1090_ = lean_ctor_get(v_s_1036_, 2);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v_s_1036_, 1);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_s_1036_, 0);
lean_dec(v_unused_1092_);
v___x_1080_ = v_s_1036_;
v_isShared_1081_ = v_isSharedCheck_1089_;
goto v_resetjp_1079_;
}
else
{
lean_dec(v_s_1036_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1089_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1082_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_1083_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_1084_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1084_, 0, v_declName_1073_);
lean_ctor_set(v___x_1084_, 1, v___x_1082_);
lean_ctor_set(v___x_1084_, 2, v___x_1083_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*3, v_behavior_1074_);
v___x_1085_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_1077_, v_catName_1072_, v___x_1084_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 2, v___x_1085_);
v___x_1087_ = v___x_1080_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_tokens_1075_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_kinds_1076_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
lean_dec(v_declName_1073_);
lean_dec(v_catName_1072_);
return v_s_1036_;
}
}
default: 
{
lean_object* v_catName_1093_; lean_object* v_declName_1094_; uint8_t v_leading_1095_; lean_object* v_p_1096_; lean_object* v_prio_1097_; lean_object* v_tokens_1098_; lean_object* v_kinds_1099_; lean_object* v_categories_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1118_; 
v_catName_1093_ = lean_ctor_get(v_e_1037_, 0);
lean_inc(v_catName_1093_);
v_declName_1094_ = lean_ctor_get(v_e_1037_, 1);
lean_inc(v_declName_1094_);
v_leading_1095_ = lean_ctor_get_uint8(v_e_1037_, sizeof(void*)*4);
v_p_1096_ = lean_ctor_get(v_e_1037_, 2);
lean_inc_ref(v_p_1096_);
v_prio_1097_ = lean_ctor_get(v_e_1037_, 3);
lean_inc(v_prio_1097_);
lean_dec_ref_known(v_e_1037_, 4);
v_tokens_1098_ = lean_ctor_get(v_s_1036_, 0);
v_kinds_1099_ = lean_ctor_get(v_s_1036_, 1);
v_categories_1100_ = lean_ctor_get(v_s_1036_, 2);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_s_1036_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1102_ = v_s_1036_;
v_isShared_1103_ = v_isSharedCheck_1118_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_categories_1100_);
lean_inc(v_kinds_1099_);
lean_inc(v_tokens_1098_);
lean_dec(v_s_1036_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1118_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_Parser_addParser(v_categories_1100_, v_catName_1093_, v_declName_1094_, v_leading_1095_, v_p_1096_, v_prio_1097_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_del_object(v___x_1102_);
lean_dec_ref(v_kinds_1099_);
lean_dec_ref(v_tokens_1098_);
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v___x_1106_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1107_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1108_ = lean_unsigned_to_nat(173u);
v___x_1109_ = lean_unsigned_to_nat(30u);
v___x_1110_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1111_ = lean_string_append(v___x_1110_, v_a_1105_);
lean_dec(v_a_1105_);
v___x_1112_ = l_mkPanicMessageWithDecl(v___x_1106_, v___x_1107_, v___x_1108_, v___x_1109_, v___x_1111_);
lean_dec_ref(v___x_1111_);
v___x_1113_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1112_);
return v___x_1113_;
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; 
v_a_1114_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___x_1104_, 1);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 2, v_a_1114_);
v___x_1116_ = v___x_1102_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_tokens_1098_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_kinds_1099_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_a_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg(lean_object* v_x_1119_){
_start:
{
switch(lean_obj_tag(v_x_1119_))
{
case 0:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_unsigned_to_nat(0u);
return v___x_1120_;
}
case 1:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_unsigned_to_nat(1u);
return v___x_1121_;
}
default: 
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_unsigned_to_nat(2u);
return v___x_1122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg___boxed(lean_object* v_x_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Parser_AliasValue_ctorIdx___redArg(v_x_1123_);
lean_dec_ref(v_x_1123_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx(lean_object* v_00_u03b1_1125_, lean_object* v_x_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Parser_AliasValue_ctorIdx___redArg(v_x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___boxed(lean_object* v_00_u03b1_1128_, lean_object* v_x_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_Parser_AliasValue_ctorIdx(v_00_u03b1_1128_, v_x_1129_);
lean_dec_ref(v_x_1129_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___redArg(lean_object* v_t_1131_, lean_object* v_k_1132_){
_start:
{
lean_object* v_p_1133_; lean_object* v___x_1134_; 
v_p_1133_ = lean_ctor_get(v_t_1131_, 0);
lean_inc(v_p_1133_);
lean_dec_ref(v_t_1131_);
v___x_1134_ = lean_apply_1(v_k_1132_, v_p_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim(lean_object* v_00_u03b1_1135_, lean_object* v_motive_1136_, lean_object* v_ctorIdx_1137_, lean_object* v_t_1138_, lean_object* v_h_1139_, lean_object* v_k_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1138_, v_k_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___boxed(lean_object* v_00_u03b1_1142_, lean_object* v_motive_1143_, lean_object* v_ctorIdx_1144_, lean_object* v_t_1145_, lean_object* v_h_1146_, lean_object* v_k_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Parser_AliasValue_ctorElim(v_00_u03b1_1142_, v_motive_1143_, v_ctorIdx_1144_, v_t_1145_, v_h_1146_, v_k_1147_);
lean_dec(v_ctorIdx_1144_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim___redArg(lean_object* v_t_1149_, lean_object* v_const_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1149_, v_const_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim(lean_object* v_00_u03b1_1152_, lean_object* v_motive_1153_, lean_object* v_t_1154_, lean_object* v_h_1155_, lean_object* v_const_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1154_, v_const_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim___redArg(lean_object* v_t_1158_, lean_object* v_unary_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1158_, v_unary_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim(lean_object* v_00_u03b1_1161_, lean_object* v_motive_1162_, lean_object* v_t_1163_, lean_object* v_h_1164_, lean_object* v_unary_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1163_, v_unary_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim___redArg(lean_object* v_t_1167_, lean_object* v_binary_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1167_, v_binary_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim(lean_object* v_00_u03b1_1170_, lean_object* v_motive_1171_, lean_object* v_t_1172_, lean_object* v_h_1173_, lean_object* v_binary_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1172_, v_binary_1174_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_Parser_registerAliasCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__0));
v___x_1178_ = lean_mk_io_user_error(v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg(lean_object* v_mapRef_1181_, lean_object* v_aliasName_1182_, lean_object* v_value_1183_){
_start:
{
uint8_t v___x_1185_; 
v___x_1185_ = l_Lean_initializing();
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec_ref(v_value_1183_);
lean_dec(v_aliasName_1182_);
v___x_1186_ = lean_obj_once(&l_Lean_Parser_registerAliasCore___redArg___closed__1, &l_Lean_Parser_registerAliasCore___redArg___closed__1_once, _init_l_Lean_Parser_registerAliasCore___redArg___closed__1);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
else
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = lean_st_ref_get(v_mapRef_1181_);
v___x_1189_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_aliasName_1182_, v___x_1188_);
lean_dec(v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1190_ = lean_st_ref_take(v_mapRef_1181_);
v___x_1191_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1182_, v_value_1183_, v___x_1190_);
v___x_1192_ = lean_st_ref_put(v_mapRef_1181_, v___x_1191_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec_ref(v_value_1183_);
v___x_1194_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__2));
v___x_1195_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1182_, v___x_1189_);
v___x_1196_ = lean_string_append(v___x_1194_, v___x_1195_);
lean_dec_ref(v___x_1195_);
v___x_1197_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__3));
v___x_1198_ = lean_string_append(v___x_1196_, v___x_1197_);
v___x_1199_ = lean_mk_io_user_error(v___x_1198_);
v___x_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg___boxed(lean_object* v_mapRef_1201_, lean_object* v_aliasName_1202_, lean_object* v_value_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1201_, v_aliasName_1202_, v_value_1203_);
lean_dec(v_mapRef_1201_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore(lean_object* v_00_u03b1_1206_, lean_object* v_mapRef_1207_, lean_object* v_aliasName_1208_, lean_object* v_value_1209_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1207_, v_aliasName_1208_, v_value_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___boxed(lean_object* v_00_u03b1_1212_, lean_object* v_mapRef_1213_, lean_object* v_aliasName_1214_, lean_object* v_value_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_Parser_registerAliasCore(v_00_u03b1_1212_, v_mapRef_1213_, v_aliasName_1214_, v_value_1215_);
lean_dec(v_mapRef_1213_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg(lean_object* v_mapRef_1218_, lean_object* v_aliasName_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_st_ref_get(v_mapRef_1218_);
v___x_1222_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1221_, v_aliasName_1219_);
lean_dec(v___x_1221_);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg___boxed(lean_object* v_mapRef_1224_, lean_object* v_aliasName_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1224_, v_aliasName_1225_);
lean_dec(v_aliasName_1225_);
lean_dec(v_mapRef_1224_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias(lean_object* v_00_u03b1_1228_, lean_object* v_mapRef_1229_, lean_object* v_aliasName_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1229_, v_aliasName_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___boxed(lean_object* v_00_u03b1_1233_, lean_object* v_mapRef_1234_, lean_object* v_aliasName_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Parser_getAlias(v_00_u03b1_1233_, v_mapRef_1234_, v_aliasName_1235_);
lean_dec(v_aliasName_1235_);
lean_dec(v_mapRef_1234_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object* v_mapRef_1242_, lean_object* v_aliasName_1243_){
_start:
{
lean_object* v___x_1245_; lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1285_; 
v___x_1245_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1242_, v_aliasName_1243_);
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1285_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1285_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
if (lean_obj_tag(v_a_1246_) == 0)
{
lean_object* v___x_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1250_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1251_ = 1;
v___x_1252_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1243_, v___x_1251_);
v___x_1253_ = lean_string_append(v___x_1250_, v___x_1252_);
lean_dec_ref(v___x_1252_);
v___x_1254_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1255_ = lean_string_append(v___x_1253_, v___x_1254_);
v___x_1256_ = lean_mk_io_user_error(v___x_1255_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 1);
lean_ctor_set(v___x_1248_, 0, v___x_1256_);
v___x_1258_ = v___x_1248_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
else
{
lean_object* v_val_1260_; 
v_val_1260_ = lean_ctor_get(v_a_1246_, 0);
lean_inc(v_val_1260_);
lean_dec_ref_known(v_a_1246_, 1);
switch(lean_obj_tag(v_val_1260_))
{
case 0:
{
lean_object* v_p_1261_; lean_object* v___x_1263_; 
lean_dec(v_aliasName_1243_);
v_p_1261_ = lean_ctor_get(v_val_1260_, 0);
lean_inc(v_p_1261_);
lean_dec_ref_known(v_val_1260_, 1);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v_p_1261_);
v___x_1263_ = v___x_1248_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_p_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
case 1:
{
lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
lean_dec_ref_known(v_val_1260_, 1);
v___x_1265_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1266_ = 1;
v___x_1267_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1243_, v___x_1266_);
v___x_1268_ = lean_string_append(v___x_1265_, v___x_1267_);
lean_dec_ref(v___x_1267_);
v___x_1269_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__2));
v___x_1270_ = lean_string_append(v___x_1268_, v___x_1269_);
v___x_1271_ = lean_mk_io_user_error(v___x_1270_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 1);
lean_ctor_set(v___x_1248_, 0, v___x_1271_);
v___x_1273_ = v___x_1248_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
default: 
{
lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
lean_dec_ref_known(v_val_1260_, 1);
v___x_1275_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1276_ = 1;
v___x_1277_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1243_, v___x_1276_);
v___x_1278_ = lean_string_append(v___x_1275_, v___x_1277_);
lean_dec_ref(v___x_1277_);
v___x_1279_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__3));
v___x_1280_ = lean_string_append(v___x_1278_, v___x_1279_);
v___x_1281_ = lean_mk_io_user_error(v___x_1280_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 1);
lean_ctor_set(v___x_1248_, 0, v___x_1281_);
v___x_1283_ = v___x_1248_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object* v_mapRef_1286_, lean_object* v_aliasName_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1286_, v_aliasName_1287_);
lean_dec(v_mapRef_1286_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object* v_00_u03b1_1290_, lean_object* v_mapRef_1291_, lean_object* v_aliasName_1292_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1291_, v_aliasName_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object* v_00_u03b1_1295_, lean_object* v_mapRef_1296_, lean_object* v_aliasName_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Parser_getConstAlias(v_00_u03b1_1295_, v_mapRef_1296_, v_aliasName_1297_);
lean_dec(v_mapRef_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object* v_mapRef_1301_, lean_object* v_aliasName_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1334_; 
v___x_1304_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1301_, v_aliasName_1302_);
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1334_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1334_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
if (lean_obj_tag(v_a_1305_) == 0)
{
lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1309_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1310_ = 1;
v___x_1311_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1302_, v___x_1310_);
v___x_1312_ = lean_string_append(v___x_1309_, v___x_1311_);
lean_dec_ref(v___x_1311_);
v___x_1313_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1314_ = lean_string_append(v___x_1312_, v___x_1313_);
v___x_1315_ = lean_mk_io_user_error(v___x_1314_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set_tag(v___x_1307_, 1);
lean_ctor_set(v___x_1307_, 0, v___x_1315_);
v___x_1317_ = v___x_1307_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
else
{
lean_object* v_val_1319_; 
v_val_1319_ = lean_ctor_get(v_a_1305_, 0);
lean_inc(v_val_1319_);
lean_dec_ref_known(v_a_1305_, 1);
if (lean_obj_tag(v_val_1319_) == 1)
{
lean_object* v_p_1320_; lean_object* v___x_1322_; 
lean_dec(v_aliasName_1302_);
v_p_1320_ = lean_ctor_get(v_val_1319_, 0);
lean_inc(v_p_1320_);
lean_dec_ref_known(v_val_1319_, 1);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v_p_1320_);
v___x_1322_ = v___x_1307_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_p_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
else
{
lean_object* v___x_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
lean_dec(v_val_1319_);
v___x_1324_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1325_ = 1;
v___x_1326_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1302_, v___x_1325_);
v___x_1327_ = lean_string_append(v___x_1324_, v___x_1326_);
lean_dec_ref(v___x_1326_);
v___x_1328_ = ((lean_object*)(l_Lean_Parser_getUnaryAlias___redArg___closed__0));
v___x_1329_ = lean_string_append(v___x_1327_, v___x_1328_);
v___x_1330_ = lean_mk_io_user_error(v___x_1329_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set_tag(v___x_1307_, 1);
lean_ctor_set(v___x_1307_, 0, v___x_1330_);
v___x_1332_ = v___x_1307_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object* v_mapRef_1335_, lean_object* v_aliasName_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1335_, v_aliasName_1336_);
lean_dec(v_mapRef_1335_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object* v_00_u03b1_1339_, lean_object* v_mapRef_1340_, lean_object* v_aliasName_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1340_, v_aliasName_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object* v_00_u03b1_1344_, lean_object* v_mapRef_1345_, lean_object* v_aliasName_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Parser_getUnaryAlias(v_00_u03b1_1344_, v_mapRef_1345_, v_aliasName_1346_);
lean_dec(v_mapRef_1345_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object* v_mapRef_1350_, lean_object* v_aliasName_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1383_; 
v___x_1353_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1350_, v_aliasName_1351_);
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1383_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1383_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
if (lean_obj_tag(v_a_1354_) == 0)
{
lean_object* v___x_1358_; uint8_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1358_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1359_ = 1;
v___x_1360_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1351_, v___x_1359_);
v___x_1361_ = lean_string_append(v___x_1358_, v___x_1360_);
lean_dec_ref(v___x_1360_);
v___x_1362_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1363_ = lean_string_append(v___x_1361_, v___x_1362_);
v___x_1364_ = lean_mk_io_user_error(v___x_1363_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 1);
lean_ctor_set(v___x_1356_, 0, v___x_1364_);
v___x_1366_ = v___x_1356_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
else
{
lean_object* v_val_1368_; 
v_val_1368_ = lean_ctor_get(v_a_1354_, 0);
lean_inc(v_val_1368_);
lean_dec_ref_known(v_a_1354_, 1);
if (lean_obj_tag(v_val_1368_) == 2)
{
lean_object* v_p_1369_; lean_object* v___x_1371_; 
lean_dec(v_aliasName_1351_);
v_p_1369_ = lean_ctor_get(v_val_1368_, 0);
lean_inc(v_p_1369_);
lean_dec_ref_known(v_val_1368_, 1);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v_p_1369_);
v___x_1371_ = v___x_1356_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_p_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
else
{
lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_dec(v_val_1368_);
v___x_1373_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1374_ = 1;
v___x_1375_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1351_, v___x_1374_);
v___x_1376_ = lean_string_append(v___x_1373_, v___x_1375_);
lean_dec_ref(v___x_1375_);
v___x_1377_ = ((lean_object*)(l_Lean_Parser_getBinaryAlias___redArg___closed__0));
v___x_1378_ = lean_string_append(v___x_1376_, v___x_1377_);
v___x_1379_ = lean_mk_io_user_error(v___x_1378_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 1);
lean_ctor_set(v___x_1356_, 0, v___x_1379_);
v___x_1381_ = v___x_1356_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg___boxed(lean_object* v_mapRef_1384_, lean_object* v_aliasName_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1384_, v_aliasName_1385_);
lean_dec(v_mapRef_1384_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object* v_00_u03b1_1388_, lean_object* v_mapRef_1389_, lean_object* v_aliasName_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1389_, v_aliasName_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___boxed(lean_object* v_00_u03b1_1393_, lean_object* v_mapRef_1394_, lean_object* v_aliasName_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Parser_getBinaryAlias(v_00_u03b1_1393_, v_mapRef_1394_, v_aliasName_1395_);
lean_dec(v_mapRef_1394_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = lean_box(1);
v___x_1400_ = lean_st_mk_ref(v___x_1399_);
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1405_ = lean_box(1);
v___x_1406_ = lean_st_mk_ref(v___x_1405_);
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = lean_box(1);
v___x_1412_ = lean_st_mk_ref(v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(lean_object* v_t_1416_, lean_object* v_k_1417_, lean_object* v_fallback_1418_){
_start:
{
if (lean_obj_tag(v_t_1416_) == 0)
{
lean_object* v_k_1419_; lean_object* v_v_1420_; lean_object* v_l_1421_; lean_object* v_r_1422_; uint8_t v___x_1423_; 
v_k_1419_ = lean_ctor_get(v_t_1416_, 1);
v_v_1420_ = lean_ctor_get(v_t_1416_, 2);
v_l_1421_ = lean_ctor_get(v_t_1416_, 3);
v_r_1422_ = lean_ctor_get(v_t_1416_, 4);
v___x_1423_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1417_, v_k_1419_);
switch(v___x_1423_)
{
case 0:
{
v_t_1416_ = v_l_1421_;
goto _start;
}
case 1:
{
lean_inc(v_v_1420_);
return v_v_1420_;
}
default: 
{
v_t_1416_ = v_r_1422_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_1418_);
return v_fallback_1418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg___boxed(lean_object* v_t_1426_, lean_object* v_k_1427_, lean_object* v_fallback_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1426_, v_k_1427_, v_fallback_1428_);
lean_dec(v_fallback_1428_);
lean_dec(v_k_1427_);
lean_dec(v_t_1426_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo(lean_object* v_aliasName_1436_){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1438_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1439_ = lean_st_ref_get(v___x_1438_);
v___x_1440_ = ((lean_object*)(l_Lean_Parser_getParserAliasInfo___closed__1));
v___x_1441_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v___x_1439_, v_aliasName_1436_, v___x_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo___boxed(lean_object* v_aliasName_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_Parser_getParserAliasInfo(v_aliasName_1443_);
lean_dec(v_aliasName_1443_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(lean_object* v_00_u03b4_1446_, lean_object* v_t_1447_, lean_object* v_k_1448_, lean_object* v_fallback_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1447_, v_k_1448_, v_fallback_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___boxed(lean_object* v_00_u03b4_1451_, lean_object* v_t_1452_, lean_object* v_k_1453_, lean_object* v_fallback_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(v_00_u03b4_1451_, v_t_1452_, v_k_1453_, v_fallback_1454_);
lean_dec(v_fallback_1454_);
lean_dec(v_k_1453_);
lean_dec(v_t_1452_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object* v_aliasName_1456_, lean_object* v_declName_1457_, lean_object* v_p_1458_, lean_object* v_kind_x3f_1459_, lean_object* v_info_1460_){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = l_Lean_Parser_parserAliasesRef;
lean_inc(v_aliasName_1456_);
v___x_1479_ = l_Lean_Parser_registerAliasCore___redArg(v___x_1478_, v_aliasName_1456_, v_p_1458_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_dec_ref_known(v___x_1479_, 1);
if (lean_obj_tag(v_kind_x3f_1459_) == 1)
{
lean_object* v_val_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_val_1480_ = lean_ctor_get(v_kind_x3f_1459_, 0);
lean_inc(v_val_1480_);
lean_dec_ref_known(v_kind_x3f_1459_, 1);
v___x_1481_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1482_ = lean_st_ref_take(v___x_1481_);
lean_inc(v_aliasName_1456_);
v___x_1483_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1456_, v_val_1480_, v___x_1482_);
v___x_1484_ = lean_st_ref_put(v___x_1481_, v___x_1483_);
goto v___jp_1462_;
}
else
{
lean_dec(v_kind_x3f_1459_);
goto v___jp_1462_;
}
}
else
{
lean_dec_ref(v_info_1460_);
lean_dec(v_kind_x3f_1459_);
lean_dec(v_declName_1457_);
lean_dec(v_aliasName_1456_);
return v___x_1479_;
}
v___jp_1462_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v_stackSz_x3f_1465_; uint8_t v_autoGroupArgs_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1476_; 
v___x_1463_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1464_ = lean_st_ref_take(v___x_1463_);
v_stackSz_x3f_1465_ = lean_ctor_get(v_info_1460_, 1);
v_autoGroupArgs_1466_ = lean_ctor_get_uint8(v_info_1460_, sizeof(void*)*2);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_info_1460_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v_info_1460_, 0);
lean_dec(v_unused_1477_);
v___x_1468_ = v_info_1460_;
v_isShared_1469_ = v_isSharedCheck_1476_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_stackSz_x3f_1465_);
lean_dec(v_info_1460_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1476_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v_declName_1457_);
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_declName_1457_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_stackSz_x3f_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*2, v_autoGroupArgs_1466_);
v___x_1471_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1456_, v___x_1471_, v___x_1464_);
v___x_1473_ = lean_st_ref_put(v___x_1463_, v___x_1472_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
return v___x_1474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias___boxed(lean_object* v_aliasName_1485_, lean_object* v_declName_1486_, lean_object* v_p_1487_, lean_object* v_kind_x3f_1488_, lean_object* v_info_1489_, lean_object* v_a_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_Parser_registerAlias(v_aliasName_1485_, v_declName_1486_, v_p_1487_, v_kind_x3f_1488_, v_info_1489_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue___lam__0(lean_object* v_p_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_p_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0(lean_object* v_p_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_p_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0(lean_object* v_p_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_p_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object* v_aliasName_1504_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1522_; 
v___x_1506_ = l_Lean_Parser_parserAliasesRef;
v___x_1507_ = l_Lean_Parser_getAlias___redArg(v___x_1506_, v_aliasName_1504_);
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1522_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1522_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
if (lean_obj_tag(v_a_1508_) == 1)
{
uint8_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
lean_dec_ref_known(v_a_1508_, 1);
v___x_1512_ = 1;
v___x_1513_ = lean_box(v___x_1512_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1513_);
v___x_1515_ = v___x_1510_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
else
{
uint8_t v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
lean_dec(v_a_1508_);
v___x_1517_ = 0;
v___x_1518_ = lean_box(v___x_1517_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1518_);
v___x_1520_ = v___x_1510_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object* v_aliasName_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Parser_isParserAlias(v_aliasName_1523_);
lean_dec(v_aliasName_1523_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object* v_aliasName_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1528_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1529_ = lean_st_ref_get(v___x_1528_);
v___x_1530_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1529_, v_aliasName_1526_);
lean_dec(v___x_1529_);
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f___boxed(lean_object* v_aliasName_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v_aliasName_1532_);
lean_dec(v_aliasName_1532_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object* v_aliasName_1535_){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = l_Lean_Parser_parserAliasesRef;
v___x_1538_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1537_, v_aliasName_1535_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1546_; 
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v___x_1538_, 0);
lean_dec(v_unused_1547_);
v___x_1540_ = v___x_1538_;
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v___x_1538_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = lean_box(0);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1542_);
v___x_1544_ = v___x_1540_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
v_a_1548_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1538_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1538_);
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
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias___boxed(lean_object* v_aliasName_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Parser_ensureUnaryParserAlias(v_aliasName_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object* v_aliasName_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = l_Lean_Parser_parserAliasesRef;
v___x_1562_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1561_, v_aliasName_1559_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1570_; 
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v___x_1562_, 0);
lean_dec(v_unused_1571_);
v___x_1564_ = v___x_1562_;
v_isShared_1565_ = v_isSharedCheck_1570_;
goto v_resetjp_1563_;
}
else
{
lean_dec(v___x_1562_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1570_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1566_ = lean_box(0);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1566_);
v___x_1568_ = v___x_1564_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
v_a_1572_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1562_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1562_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias___boxed(lean_object* v_aliasName_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Parser_ensureBinaryParserAlias(v_aliasName_1580_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object* v_aliasName_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = l_Lean_Parser_parserAliasesRef;
v___x_1586_ = l_Lean_Parser_getConstAlias___redArg(v___x_1585_, v_aliasName_1583_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1594_; 
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; 
v_unused_1595_ = lean_ctor_get(v___x_1586_, 0);
lean_dec(v_unused_1595_);
v___x_1588_ = v___x_1586_;
v_isShared_1589_ = v_isSharedCheck_1594_;
goto v_resetjp_1587_;
}
else
{
lean_dec(v___x_1586_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1594_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1590_ = lean_box(0);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1590_);
v___x_1592_ = v___x_1588_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
v_a_1596_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1586_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1586_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias___boxed(lean_object* v_aliasName_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Parser_ensureConstantParserAlias(v_aliasName_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* v_constName_1615_, lean_object* v_compileParserDescr_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_env_1628_; lean_object* v_opts_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; 
v_env_1628_ = lean_ctor_get(v_a_1617_, 0);
v_opts_1629_ = lean_ctor_get(v_a_1617_, 1);
v___x_1630_ = 0;
lean_inc(v_constName_1615_);
lean_inc_ref(v_env_1628_);
v___x_1631_ = l_Lean_Environment_find_x3f(v_env_1628_, v_constName_1615_, v___x_1630_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v___x_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec_ref(v_compileParserDescr_1616_);
v___x_1632_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_1633_ = 1;
v___x_1634_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1615_, v___x_1633_);
v___x_1635_ = lean_string_append(v___x_1632_, v___x_1634_);
lean_dec_ref(v___x_1634_);
v___x_1636_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_1637_ = lean_string_append(v___x_1635_, v___x_1636_);
v___x_1638_ = lean_mk_io_user_error(v___x_1637_);
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
else
{
lean_object* v_val_1640_; lean_object* v___x_1641_; 
v_val_1640_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_val_1640_);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1641_ = l_Lean_ConstantInfo_type(v_val_1640_);
lean_dec(v_val_1640_);
if (lean_obj_tag(v___x_1641_) == 4)
{
lean_object* v_declName_1642_; 
v_declName_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_declName_1642_);
lean_dec_ref_known(v___x_1641_, 2);
if (lean_obj_tag(v_declName_1642_) == 1)
{
lean_object* v_pre_1643_; 
v_pre_1643_ = lean_ctor_get(v_declName_1642_, 0);
lean_inc(v_pre_1643_);
if (lean_obj_tag(v_pre_1643_) == 1)
{
lean_object* v_pre_1644_; 
v_pre_1644_ = lean_ctor_get(v_pre_1643_, 0);
switch(lean_obj_tag(v_pre_1644_))
{
case 1:
{
lean_object* v_pre_1645_; 
lean_inc_ref(v_pre_1644_);
lean_dec_ref(v_compileParserDescr_1616_);
v_pre_1645_ = lean_ctor_get(v_pre_1644_, 0);
if (lean_obj_tag(v_pre_1645_) == 0)
{
lean_object* v_str_1646_; lean_object* v_str_1647_; lean_object* v_str_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v_str_1646_ = lean_ctor_get(v_declName_1642_, 1);
lean_inc_ref(v_str_1646_);
lean_dec_ref_known(v_declName_1642_, 2);
v_str_1647_ = lean_ctor_get(v_pre_1643_, 1);
lean_inc_ref(v_str_1647_);
lean_dec_ref_known(v_pre_1643_, 2);
v_str_1648_ = lean_ctor_get(v_pre_1644_, 1);
lean_inc_ref(v_str_1648_);
lean_dec_ref_known(v_pre_1644_, 2);
v___x_1649_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1650_ = lean_string_dec_eq(v_str_1648_, v___x_1649_);
lean_dec_ref(v_str_1648_);
if (v___x_1650_ == 0)
{
lean_dec_ref(v_str_1647_);
lean_dec_ref(v_str_1646_);
goto v___jp_1619_;
}
else
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_1652_ = lean_string_dec_eq(v_str_1647_, v___x_1651_);
lean_dec_ref(v_str_1647_);
if (v___x_1652_ == 0)
{
lean_dec_ref(v_str_1646_);
goto v___jp_1619_;
}
else
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_1654_ = lean_string_dec_eq(v_str_1646_, v___x_1653_);
if (v___x_1654_ == 0)
{
uint8_t v___x_1655_; 
v___x_1655_ = lean_string_dec_eq(v_str_1646_, v___x_1651_);
lean_dec_ref(v_str_1646_);
if (v___x_1655_ == 0)
{
goto v___jp_1619_;
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = l_Lean_Environment_evalConst___redArg(v_env_1628_, v_opts_1629_, v_constName_1615_, v___x_1655_);
lean_dec(v_constName_1615_);
v___x_1657_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1656_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1667_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1662_ = lean_box(v___x_1655_);
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v_a_1658_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1663_);
v___x_1665_ = v___x_1660_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_a_1668_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1657_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1657_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec_ref(v_str_1646_);
v___x_1676_ = l_Lean_Environment_evalConst___redArg(v_env_1628_, v_opts_1629_, v_constName_1615_, v___x_1654_);
lean_dec(v_constName_1615_);
v___x_1677_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1676_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1687_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1687_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1687_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1682_ = lean_box(v___x_1630_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v_a_1678_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1683_);
v___x_1685_ = v___x_1680_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_a_1688_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1677_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1677_);
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
}
else
{
lean_dec_ref_known(v_pre_1644_, 2);
lean_dec_ref_known(v_pre_1643_, 2);
lean_dec_ref_known(v_declName_1642_, 2);
goto v___jp_1619_;
}
}
case 0:
{
lean_object* v_str_1696_; lean_object* v_str_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v_str_1696_ = lean_ctor_get(v_declName_1642_, 1);
lean_inc_ref(v_str_1696_);
lean_dec_ref_known(v_declName_1642_, 2);
v_str_1697_ = lean_ctor_get(v_pre_1643_, 1);
lean_inc_ref(v_str_1697_);
lean_dec_ref_known(v_pre_1643_, 2);
v___x_1698_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1699_ = lean_string_dec_eq(v_str_1697_, v___x_1698_);
lean_dec_ref(v_str_1697_);
if (v___x_1699_ == 0)
{
lean_dec_ref(v_str_1696_);
lean_dec_ref(v_compileParserDescr_1616_);
goto v___jp_1619_;
}
else
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_1701_ = lean_string_dec_eq(v_str_1696_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_1703_ = lean_string_dec_eq(v_str_1696_, v___x_1702_);
lean_dec_ref(v_str_1696_);
if (v___x_1703_ == 0)
{
lean_dec_ref(v_compileParserDescr_1616_);
goto v___jp_1619_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = l_Lean_Environment_evalConst___redArg(v_env_1628_, v_opts_1629_, v_constName_1615_, v___x_1703_);
lean_dec(v_constName_1615_);
v___x_1705_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1704_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
lean_inc_ref(v_a_1617_);
v___x_1707_ = lean_apply_3(v_compileParserDescr_1616_, v_a_1706_, v_a_1617_, lean_box(0));
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1717_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1717_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1717_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1712_ = lean_box(v___x_1630_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v_a_1708_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1713_);
v___x_1715_ = v___x_1710_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
v_a_1718_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1707_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1707_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec_ref(v_compileParserDescr_1616_);
v_a_1726_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1705_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1705_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec_ref(v_str_1696_);
v___x_1734_ = l_Lean_Environment_evalConst___redArg(v_env_1628_, v_opts_1629_, v_constName_1615_, v___x_1701_);
lean_dec(v_constName_1615_);
v___x_1735_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1734_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
lean_inc_ref(v_a_1617_);
v___x_1737_ = lean_apply_3(v_compileParserDescr_1616_, v_a_1736_, v_a_1617_, lean_box(0));
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1747_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1747_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1747_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1742_ = lean_box(v___x_1701_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v_a_1738_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1743_);
v___x_1745_ = v___x_1740_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
v_a_1748_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1737_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1737_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec_ref(v_compileParserDescr_1616_);
v_a_1756_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1735_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1735_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_pre_1643_, 2);
lean_dec_ref_known(v_declName_1642_, 2);
lean_dec_ref(v_compileParserDescr_1616_);
goto v___jp_1619_;
}
}
}
else
{
lean_dec_ref_known(v_declName_1642_, 2);
lean_dec(v_pre_1643_);
lean_dec_ref(v_compileParserDescr_1616_);
goto v___jp_1619_;
}
}
else
{
lean_dec(v_declName_1642_);
lean_dec_ref(v_compileParserDescr_1616_);
goto v___jp_1619_;
}
}
else
{
lean_dec_ref(v___x_1641_);
lean_dec_ref(v_compileParserDescr_1616_);
goto v___jp_1619_;
}
}
v___jp_1619_:
{
lean_object* v___x_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1620_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__0));
v___x_1621_ = 1;
v___x_1622_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1615_, v___x_1621_);
v___x_1623_ = lean_string_append(v___x_1620_, v___x_1622_);
lean_dec_ref(v___x_1622_);
v___x_1624_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1));
v___x_1625_ = lean_string_append(v___x_1623_, v___x_1624_);
v___x_1626_ = lean_mk_io_user_error(v___x_1625_);
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object* v_constName_1764_, lean_object* v_compileParserDescr_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1764_, v_compileParserDescr_1765_, v_a_1766_);
lean_dec_ref(v_a_1766_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed(lean_object* v_categories_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1769_, v_a_1770_, v_a_1771_);
lean_dec_ref(v_a_1771_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(lean_object* v_categories_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
switch(lean_obj_tag(v_a_1775_))
{
case 0:
{
lean_object* v_name_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec_ref(v_categories_1774_);
v_name_1778_ = lean_ctor_get(v_a_1775_, 0);
lean_inc(v_name_1778_);
lean_dec_ref_known(v_a_1775_, 1);
v___x_1779_ = l_Lean_Parser_parserAliasesRef;
v___x_1780_ = l_Lean_Parser_getConstAlias___redArg(v___x_1779_, v_name_1778_);
return v___x_1780_;
}
case 1:
{
lean_object* v_name_1781_; lean_object* v_p_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_name_1781_ = lean_ctor_get(v_a_1775_, 0);
lean_inc(v_name_1781_);
v_p_1782_ = lean_ctor_get(v_a_1775_, 1);
lean_inc_ref(v_p_1782_);
lean_dec_ref_known(v_a_1775_, 2);
v___x_1783_ = l_Lean_Parser_parserAliasesRef;
v___x_1784_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1783_, v_name_1781_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1774_, v_p_1782_, v_a_1776_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1795_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1791_ = lean_apply_1(v_a_1785_, v_a_1787_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1791_);
v___x_1793_ = v___x_1789_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
else
{
lean_dec(v_a_1785_);
return v___x_1786_;
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v_p_1782_);
lean_dec_ref(v_categories_1774_);
v_a_1796_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1784_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1784_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
case 2:
{
lean_object* v_name_1804_; lean_object* v_p_u2081_1805_; lean_object* v_p_u2082_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_name_1804_ = lean_ctor_get(v_a_1775_, 0);
lean_inc(v_name_1804_);
v_p_u2081_1805_ = lean_ctor_get(v_a_1775_, 1);
lean_inc_ref(v_p_u2081_1805_);
v_p_u2082_1806_ = lean_ctor_get(v_a_1775_, 2);
lean_inc_ref(v_p_u2082_1806_);
lean_dec_ref_known(v_a_1775_, 3);
v___x_1807_ = l_Lean_Parser_parserAliasesRef;
v___x_1808_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1807_, v_name_1804_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
lean_inc_ref(v_categories_1774_);
v___x_1810_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1774_, v_p_u2081_1805_, v_a_1776_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1812_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v___x_1812_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1774_, v_p_u2082_1806_, v_a_1776_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1821_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1821_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1821_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = lean_apply_2(v_a_1809_, v_a_1811_, v_a_1813_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
else
{
lean_dec(v_a_1811_);
lean_dec(v_a_1809_);
return v___x_1812_;
}
}
else
{
lean_dec(v_a_1809_);
lean_dec_ref(v_p_u2082_1806_);
lean_dec_ref(v_categories_1774_);
return v___x_1810_;
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec_ref(v_p_u2082_1806_);
lean_dec_ref(v_p_u2081_1805_);
lean_dec_ref(v_categories_1774_);
v_a_1822_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1808_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1808_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
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
case 3:
{
lean_object* v_kind_1830_; lean_object* v_prec_1831_; lean_object* v_p_1832_; lean_object* v___x_1833_; 
v_kind_1830_ = lean_ctor_get(v_a_1775_, 0);
lean_inc(v_kind_1830_);
v_prec_1831_ = lean_ctor_get(v_a_1775_, 1);
lean_inc(v_prec_1831_);
v_p_1832_ = lean_ctor_get(v_a_1775_, 2);
lean_inc_ref(v_p_1832_);
lean_dec_ref_known(v_a_1775_, 3);
v___x_1833_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1774_, v_p_1832_, v_a_1776_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1842_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1842_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = l_Lean_Parser_leadingNode(v_kind_1830_, v_prec_1831_, v_a_1834_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1838_);
v___x_1840_ = v___x_1836_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
else
{
lean_dec(v_prec_1831_);
lean_dec(v_kind_1830_);
return v___x_1833_;
}
}
case 4:
{
lean_object* v_kind_1843_; lean_object* v_prec_1844_; lean_object* v_lhsPrec_1845_; lean_object* v_p_1846_; lean_object* v___x_1847_; 
v_kind_1843_ = lean_ctor_get(v_a_1775_, 0);
lean_inc(v_kind_1843_);
v_prec_1844_ = lean_ctor_get(v_a_1775_, 1);
lean_inc(v_prec_1844_);
v_lhsPrec_1845_ = lean_ctor_get(v_a_1775_, 2);
lean_inc(v_lhsPrec_1845_);
v_p_1846_ = lean_ctor_get(v_a_1775_, 3);
lean_inc_ref(v_p_1846_);
lean_dec_ref_known(v_a_1775_, 4);
v___x_1847_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1774_, v_p_1846_, v_a_1776_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1856_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = l_Lean_Parser_trailingNode(v_kind_1843_, v_prec_1844_, v_lhsPrec_1845_, v_a_1848_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
else
{
lean_dec(v_lhsPrec_1845_);
lean_dec(v_prec_1844_);
lean_dec(v_kind_1843_);
return v___x_1847_;
}
}
case 5:
{
lean_object* v_val_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1865_; 
lean_dec_ref(v_categories_1774_);
v_val_1857_ = lean_ctor_get(v_a_1775_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_a_1775_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1859_ = v_a_1775_;
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_val_1857_);
lean_dec(v_a_1775_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1861_ = l_Lean_Parser_symbol(v_val_1857_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set_tag(v___x_1859_, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1861_);
v___x_1863_ = v___x_1859_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
case 6:
{
lean_object* v_val_1866_; uint8_t v_includeIdent_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec_ref(v_categories_1774_);
v_val_1866_ = lean_ctor_get(v_a_1775_, 0);
lean_inc_ref(v_val_1866_);
v_includeIdent_1867_ = lean_ctor_get_uint8(v_a_1775_, sizeof(void*)*1);
lean_dec_ref_known(v_a_1775_, 1);
v___x_1868_ = l_Lean_Parser_nonReservedSymbol(v_val_1866_, v_includeIdent_1867_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
case 7:
{
lean_object* v_catName_1870_; lean_object* v_rbp_1871_; lean_object* v___x_1872_; 
v_catName_1870_ = lean_ctor_get(v_a_1775_, 0);
lean_inc(v_catName_1870_);
v_rbp_1871_ = lean_ctor_get(v_a_1775_, 1);
lean_inc(v_rbp_1871_);
lean_dec_ref_known(v_a_1775_, 2);
v___x_1872_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_1774_, v_catName_1870_);
lean_dec_ref(v_categories_1774_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_dec(v_rbp_1871_);
v___x_1873_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_1870_);
v___x_1874_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1873_);
return v___x_1874_;
}
else
{
lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1882_; 
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; 
v_unused_1883_ = lean_ctor_get(v___x_1872_, 0);
lean_dec(v_unused_1883_);
v___x_1876_ = v___x_1872_;
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
else
{
lean_dec(v___x_1872_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1882_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = l_Lean_Parser_categoryParser(v_catName_1870_, v_rbp_1871_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set_tag(v___x_1876_, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1878_);
v___x_1880_ = v___x_1876_;
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
case 8:
{
lean_object* v_declName_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v_declName_1884_ = lean_ctor_get(v_a_1775_, 0);
lean_inc(v_declName_1884_);
lean_dec_ref_known(v_a_1775_, 1);
v___x_1885_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed), 4, 1);
lean_closure_set(v___x_1885_, 0, v_categories_1774_);
v___x_1886_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_declName_1884_, v___x_1885_, v_a_1776_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1895_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_snd_1891_; lean_object* v___x_1893_; 
v_snd_1891_ = lean_ctor_get(v_a_1887_, 1);
lean_inc(v_snd_1891_);
lean_dec(v_a_1887_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v_snd_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_snd_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
v_a_1896_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1886_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1886_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
case 9:
{
lean_object* v_name_1904_; lean_object* v_kind_1905_; lean_object* v_p_1906_; lean_object* v___x_1907_; 
v_name_1904_ = lean_ctor_get(v_a_1775_, 0);
lean_inc_ref(v_name_1904_);
v_kind_1905_ = lean_ctor_get(v_a_1775_, 1);
lean_inc(v_kind_1905_);
v_p_1906_ = lean_ctor_get(v_a_1775_, 2);
lean_inc_ref(v_p_1906_);
lean_dec_ref_known(v_a_1775_, 3);
v___x_1907_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1774_, v_p_1906_, v_a_1776_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1918_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1918_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1918_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
uint8_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1912_ = 1;
lean_inc(v_kind_1905_);
v___x_1913_ = l_Lean_Parser_nodeWithAntiquot(v_name_1904_, v_kind_1905_, v_a_1908_, v___x_1912_);
v___x_1914_ = l_Lean_Parser_withCache(v_kind_1905_, v___x_1913_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1914_);
v___x_1916_ = v___x_1910_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_dec(v_kind_1905_);
lean_dec_ref(v_name_1904_);
return v___x_1907_;
}
}
case 10:
{
lean_object* v_p_1919_; lean_object* v_sep_1920_; lean_object* v_psep_1921_; uint8_t v_allowTrailingSep_1922_; lean_object* v___x_1923_; 
v_p_1919_ = lean_ctor_get(v_a_1775_, 0);
lean_inc_ref(v_p_1919_);
v_sep_1920_ = lean_ctor_get(v_a_1775_, 1);
lean_inc_ref(v_sep_1920_);
v_psep_1921_ = lean_ctor_get(v_a_1775_, 2);
lean_inc_ref(v_psep_1921_);
v_allowTrailingSep_1922_ = lean_ctor_get_uint8(v_a_1775_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1775_, 3);
lean_inc_ref(v_categories_1774_);
v___x_1923_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1774_, v_p_1919_, v_a_1776_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1774_, v_psep_1921_, v_a_1776_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1934_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1934_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1934_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = l_Lean_Parser_sepBy(v_a_1924_, v_sep_1920_, v_a_1926_, v_allowTrailingSep_1922_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1930_);
v___x_1932_ = v___x_1928_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
else
{
lean_dec(v_a_1924_);
lean_dec_ref(v_sep_1920_);
return v___x_1925_;
}
}
else
{
lean_dec_ref(v_psep_1921_);
lean_dec_ref(v_sep_1920_);
lean_dec_ref(v_categories_1774_);
return v___x_1923_;
}
}
case 11:
{
lean_object* v_p_1935_; lean_object* v_sep_1936_; lean_object* v_psep_1937_; uint8_t v_allowTrailingSep_1938_; lean_object* v___x_1939_; 
v_p_1935_ = lean_ctor_get(v_a_1775_, 0);
lean_inc_ref(v_p_1935_);
v_sep_1936_ = lean_ctor_get(v_a_1775_, 1);
lean_inc_ref(v_sep_1936_);
v_psep_1937_ = lean_ctor_get(v_a_1775_, 2);
lean_inc_ref(v_psep_1937_);
v_allowTrailingSep_1938_ = lean_ctor_get_uint8(v_a_1775_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1775_, 3);
lean_inc_ref(v_categories_1774_);
v___x_1939_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1774_, v_p_1935_, v_a_1776_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1941_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v___x_1941_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1774_, v_psep_1937_, v_a_1776_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1950_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1950_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1950_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1946_ = l_Lean_Parser_sepBy1(v_a_1940_, v_sep_1936_, v_a_1942_, v_allowTrailingSep_1938_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1946_);
v___x_1948_ = v___x_1944_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
else
{
lean_dec(v_a_1940_);
lean_dec_ref(v_sep_1936_);
return v___x_1941_;
}
}
else
{
lean_dec_ref(v_psep_1937_);
lean_dec_ref(v_sep_1936_);
lean_dec_ref(v_categories_1774_);
return v___x_1939_;
}
}
default: 
{
lean_object* v_val_1951_; lean_object* v_asciiVal_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec_ref(v_categories_1774_);
v_val_1951_ = lean_ctor_get(v_a_1775_, 0);
lean_inc_ref(v_val_1951_);
v_asciiVal_1952_ = lean_ctor_get(v_a_1775_, 1);
lean_inc_ref(v_asciiVal_1952_);
lean_dec_ref_known(v_a_1775_, 2);
v___x_1953_ = l_Lean_Parser_unicodeSymbol___redArg(v_val_1951_, v_asciiVal_1952_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object* v_categories_1955_, lean_object* v_d_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1955_, v_d_1956_, v_a_1957_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object* v_categories_1960_, lean_object* v_d_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Parser_compileParserDescr(v_categories_1960_, v_d_1961_, v_a_1962_);
lean_dec_ref(v_a_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0(lean_object* v_categories_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1965_, v___y_1966_, v___y_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0___boxed(lean_object* v_categories_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_Parser_mkParserOfConstant___lam__0(v_categories_1970_, v___y_1971_, v___y_1972_);
lean_dec_ref(v___y_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* v_categories_1975_, lean_object* v_constName_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___f_1979_; lean_object* v___x_1980_; 
v___f_1979_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserOfConstant___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1979_, 0, v_categories_1975_);
v___x_1980_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1976_, v___f_1979_, v_a_1977_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___boxed(lean_object* v_categories_1981_, lean_object* v_constName_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_Parser_mkParserOfConstant(v_categories_1981_, v_constName_1982_, v_a_1983_);
lean_dec_ref(v_a_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = lean_box(0);
v___x_1988_ = lean_st_mk_ref(v___x_1987_);
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object* v_hook_1992_){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1994_ = l_Lean_Parser_parserAttributeHooks;
v___x_1995_ = lean_st_ref_take(v___x_1994_);
v___x_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1996_, 0, v_hook_1992_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = lean_st_ref_put(v___x_1994_, v___x_1996_);
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook___boxed(lean_object* v_hook_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_Parser_registerParserAttributeHook(v_hook_1999_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(lean_object* v_catName_2002_, lean_object* v_declName_2003_, uint8_t v_builtin_2004_, lean_object* v_as_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
if (lean_obj_tag(v_as_2005_) == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec(v_declName_2003_);
lean_dec(v_catName_2002_);
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
return v___x_2010_;
}
else
{
lean_object* v_head_2011_; lean_object* v_tail_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_head_2011_ = lean_ctor_get(v_as_2005_, 0);
lean_inc(v_head_2011_);
v_tail_2012_ = lean_ctor_get(v_as_2005_, 1);
lean_inc(v_tail_2012_);
lean_dec_ref_known(v_as_2005_, 2);
v___x_2013_ = lean_box(v_builtin_2004_);
lean_inc(v___y_2007_);
lean_inc_ref(v___y_2006_);
lean_inc(v_declName_2003_);
lean_inc(v_catName_2002_);
v___x_2014_ = lean_apply_6(v_head_2011_, v_catName_2002_, v_declName_2003_, v___x_2013_, v___y_2006_, v___y_2007_, lean_box(0));
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_dec_ref_known(v___x_2014_, 1);
v_as_2005_ = v_tail_2012_;
goto _start;
}
else
{
lean_dec(v_tail_2012_);
lean_dec(v_declName_2003_);
lean_dec(v_catName_2002_);
return v___x_2014_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0___boxed(lean_object* v_catName_2016_, lean_object* v_declName_2017_, lean_object* v_builtin_2018_, lean_object* v_as_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
uint8_t v_builtin_boxed_2023_; lean_object* v_res_2024_; 
v_builtin_boxed_2023_ = lean_unbox(v_builtin_2018_);
v_res_2024_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2016_, v_declName_2017_, v_builtin_boxed_2023_, v_as_2019_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object* v_catName_2025_, lean_object* v_declName_2026_, uint8_t v_builtin_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = l_Lean_Parser_parserAttributeHooks;
v___x_2032_ = lean_st_ref_get(v___x_2031_);
v___x_2033_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2025_, v_declName_2026_, v_builtin_2027_, v___x_2032_, v_a_2028_, v_a_2029_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object* v_catName_2034_, lean_object* v_declName_2035_, lean_object* v_builtin_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
uint8_t v_builtin_boxed_2040_; lean_object* v_res_2041_; 
v_builtin_boxed_2040_ = lean_unbox(v_builtin_2036_);
v_res_2041_ = l_Lean_Parser_runParserAttributeHooks(v_catName_2034_, v_declName_2035_, v_builtin_boxed_2040_, v_a_2037_, v_a_2038_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2042_, lean_object* v_decl_2043_, lean_object* v_stx_2044_, uint8_t v_x_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2044_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2049_) == 0)
{
uint8_t v___x_2050_; lean_object* v___x_2051_; 
lean_dec_ref_known(v___x_2049_, 1);
v___x_2050_ = 1;
v___x_2051_ = l_Lean_Parser_runParserAttributeHooks(v___x_2042_, v_decl_2043_, v___x_2050_, v___y_2046_, v___y_2047_);
return v___x_2051_;
}
else
{
lean_dec(v_decl_2043_);
lean_dec(v___x_2042_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2052_, lean_object* v_decl_2053_, lean_object* v_stx_2054_, lean_object* v_x_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
uint8_t v_x_1064__boxed_2059_; lean_object* v_res_2060_; 
v_x_1064__boxed_2059_ = lean_unbox(v_x_2055_);
v_res_2060_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2052_, v_decl_2053_, v_stx_2054_, v_x_1064__boxed_2059_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v_res_2060_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
return v___x_2063_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2065_ = lean_unsigned_to_nat(0u);
v___x_2066_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
lean_ctor_set(v___x_2066_, 2, v___x_2065_);
lean_ctor_set(v___x_2066_, 3, v___x_2065_);
lean_ctor_set(v___x_2066_, 4, v___x_2064_);
lean_ctor_set(v___x_2066_, 5, v___x_2064_);
lean_ctor_set(v___x_2066_, 6, v___x_2064_);
lean_ctor_set(v___x_2066_, 7, v___x_2064_);
lean_ctor_set(v___x_2066_, 8, v___x_2064_);
lean_ctor_set(v___x_2066_, 9, v___x_2064_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = lean_unsigned_to_nat(32u);
v___x_2068_ = lean_mk_empty_array_with_capacity(v___x_2067_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2070_ = ((size_t)5ULL);
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_unsigned_to_nat(32u);
v___x_2073_ = lean_mk_empty_array_with_capacity(v___x_2072_);
v___x_2074_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2075_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
lean_ctor_set(v___x_2075_, 1, v___x_2073_);
lean_ctor_set(v___x_2075_, 2, v___x_2071_);
lean_ctor_set(v___x_2075_, 3, v___x_2071_);
lean_ctor_set_usize(v___x_2075_, 4, v___x_2070_);
return v___x_2075_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2076_ = lean_box(1);
v___x_2077_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2078_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v___x_2077_);
lean_ctor_set(v___x_2079_, 2, v___x_2076_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___x_2084_; lean_object* v_env_2085_; lean_object* v_options_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2084_ = lean_st_ref_get(v___y_2082_);
v_env_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc_ref(v_env_2085_);
lean_dec(v___x_2084_);
v_options_2086_ = lean_ctor_get(v___y_2081_, 2);
v___x_2087_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_2088_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2086_);
v___x_2089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2089_, 0, v_env_2085_);
lean_ctor_set(v___x_2089_, 1, v___x_2087_);
lean_ctor_set(v___x_2089_, 2, v___x_2088_);
lean_ctor_set(v___x_2089_, 3, v_options_2086_);
v___x_2090_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v_msgData_2080_);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_ref_2101_; lean_object* v___x_2102_; lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2111_; 
v_ref_2101_ = lean_ctor_get(v___y_2098_, 5);
v___x_2102_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msg_2097_, v___y_2098_, v___y_2099_);
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
lean_inc(v_ref_2101_);
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v_ref_2101_);
lean_ctor_set(v___x_2107_, 1, v_a_2103_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set_tag(v___x_2105_, 1);
lean_ctor_set(v___x_2105_, 0, v___x_2107_);
v___x_2109_ = v___x_2105_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
return v_res_2116_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2122_ = l_Lean_stringToMessageData(v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2123_, lean_object* v_decl_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2128_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2129_ = l_Lean_MessageData_ofName(v___x_2123_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2132_, v___y_2125_, v___y_2126_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2134_, lean_object* v_decl_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2134_, v_decl_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v_decl_2135_);
return v_res_2139_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = lean_unsigned_to_nat(3646333153u);
v___x_2183_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2184_ = l_Lean_Name_num___override(v___x_2183_, v___x_2182_);
return v___x_2184_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2187_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2188_ = l_Lean_Name_str___override(v___x_2187_, v___x_2186_);
return v___x_2188_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2191_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2192_ = l_Lean_Name_str___override(v___x_2191_, v___x_2190_);
return v___x_2192_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = lean_unsigned_to_nat(2u);
v___x_2194_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2195_ = l_Lean_Name_num___override(v___x_2194_, v___x_2193_);
return v___x_2195_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2202_ = 0;
v___x_2203_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2204_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2205_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2206_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v___x_2204_);
lean_ctor_set(v___x_2206_, 2, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3, v___x_2202_);
return v___x_2206_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2207_; lean_object* v___f_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___f_2207_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___f_2208_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2209_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___f_2208_);
lean_ctor_set(v___x_2210_, 2, v___f_2207_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2213_ = l_Lean_registerBuiltinAttribute(v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2216_, lean_object* v_msg_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2217_, v___y_2218_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2222_, lean_object* v_msg_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(v_00_u03b1_2222_, v_msg_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2228_, lean_object* v_decl_2229_, lean_object* v_stx_2230_, uint8_t v_x_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2230_, v___y_2232_, v___y_2233_);
if (lean_obj_tag(v___x_2235_) == 0)
{
uint8_t v___x_2236_; lean_object* v___x_2237_; 
lean_dec_ref_known(v___x_2235_, 1);
v___x_2236_ = 0;
v___x_2237_ = l_Lean_Parser_runParserAttributeHooks(v___x_2228_, v_decl_2229_, v___x_2236_, v___y_2232_, v___y_2233_);
return v___x_2237_;
}
else
{
lean_dec(v_decl_2229_);
lean_dec(v___x_2228_);
return v___x_2235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2238_, lean_object* v_decl_2239_, lean_object* v_stx_2240_, lean_object* v_x_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
uint8_t v_x_211__boxed_2245_; lean_object* v_res_2246_; 
v_x_211__boxed_2245_ = lean_unbox(v_x_2241_);
v_res_2246_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2238_, v_decl_2239_, v_stx_2240_, v_x_211__boxed_2245_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2247_, lean_object* v_decl_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2252_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2253_ = l_Lean_MessageData_ofName(v___x_2247_);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2256_, v___y_2249_, v___y_2250_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2258_, lean_object* v_decl_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2258_, v_decl_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v_decl_2259_);
return v_res_2263_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = lean_unsigned_to_nat(3789407938u);
v___x_2267_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2268_ = l_Lean_Name_num___override(v___x_2267_, v___x_2266_);
return v___x_2268_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2270_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2271_ = l_Lean_Name_str___override(v___x_2270_, v___x_2269_);
return v___x_2271_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2273_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2274_ = l_Lean_Name_str___override(v___x_2273_, v___x_2272_);
return v___x_2274_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = lean_unsigned_to_nat(2u);
v___x_2276_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2277_ = l_Lean_Name_num___override(v___x_2276_, v___x_2275_);
return v___x_2277_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2284_ = 0;
v___x_2285_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2286_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2287_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2288_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v___x_2286_);
lean_ctor_set(v___x_2288_, 2, v___x_2285_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*3, v___x_2284_);
return v___x_2288_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2289_; lean_object* v___f_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___f_2289_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___f_2290_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2291_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v___f_2290_);
lean_ctor_set(v___x_2292_, 2, v___f_2289_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2295_ = l_Lean_registerBuiltinAttribute(v___x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object* v_s_2298_, lean_object* v_x_2299_, lean_object* v_a_2300_){
_start:
{
switch(lean_obj_tag(v_x_2299_))
{
case 0:
{
lean_object* v_val_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2310_; 
lean_dec_ref(v_s_2298_);
v_val_2302_ = lean_ctor_get(v_x_2299_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_x_2299_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2304_ = v_x_2299_;
v_isShared_2305_ = v_isSharedCheck_2310_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_val_2302_);
lean_dec(v_x_2299_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2310_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_val_2302_);
v___x_2307_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
return v___x_2308_;
}
}
}
case 1:
{
lean_object* v_val_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v_s_2298_);
v_val_2311_ = lean_ctor_get(v_x_2299_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_x_2299_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2313_ = v_x_2299_;
v_isShared_2314_ = v_isSharedCheck_2319_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_val_2311_);
lean_dec(v_x_2299_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2319_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_val_2311_);
v___x_2316_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
return v___x_2317_;
}
}
}
case 2:
{
lean_object* v_catName_2320_; lean_object* v_declName_2321_; uint8_t v_behavior_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v_s_2298_);
v_catName_2320_ = lean_ctor_get(v_x_2299_, 0);
v_declName_2321_ = lean_ctor_get(v_x_2299_, 1);
v_behavior_2322_ = lean_ctor_get_uint8(v_x_2299_, sizeof(void*)*2);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_x_2299_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2324_ = v_x_2299_;
v_isShared_2325_ = v_isSharedCheck_2330_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_declName_2321_);
lean_inc(v_catName_2320_);
lean_dec(v_x_2299_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2330_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_catName_2320_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_declName_2321_);
lean_ctor_set_uint8(v_reuseFailAlloc_2329_, sizeof(void*)*2, v_behavior_2322_);
v___x_2327_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
return v___x_2328_;
}
}
}
default: 
{
lean_object* v_catName_2331_; lean_object* v_declName_2332_; lean_object* v_prio_2333_; lean_object* v_categories_2334_; lean_object* v___x_2335_; 
v_catName_2331_ = lean_ctor_get(v_x_2299_, 0);
lean_inc(v_catName_2331_);
v_declName_2332_ = lean_ctor_get(v_x_2299_, 1);
lean_inc_n(v_declName_2332_, 2);
v_prio_2333_ = lean_ctor_get(v_x_2299_, 2);
lean_inc(v_prio_2333_);
lean_dec_ref_known(v_x_2299_, 3);
v_categories_2334_ = lean_ctor_get(v_s_2298_, 2);
lean_inc_ref(v_categories_2334_);
lean_dec_ref(v_s_2298_);
v___x_2335_ = l_Lean_Parser_mkParserOfConstant(v_categories_2334_, v_declName_2332_, v_a_2300_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2347_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2347_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2347_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_fst_2340_; lean_object* v_snd_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; lean_object* v___x_2345_; 
v_fst_2340_ = lean_ctor_get(v_a_2336_, 0);
lean_inc(v_fst_2340_);
v_snd_2341_ = lean_ctor_get(v_a_2336_, 1);
lean_inc(v_snd_2341_);
lean_dec(v_a_2336_);
v___x_2342_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_2342_, 0, v_catName_2331_);
lean_ctor_set(v___x_2342_, 1, v_declName_2332_);
lean_ctor_set(v___x_2342_, 2, v_snd_2341_);
lean_ctor_set(v___x_2342_, 3, v_prio_2333_);
v___x_2343_ = lean_unbox(v_fst_2340_);
lean_dec(v_fst_2340_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*4, v___x_2343_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2342_);
v___x_2345_ = v___x_2338_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2342_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec(v_prio_2333_);
lean_dec(v_declName_2332_);
lean_dec(v_catName_2331_);
v_a_2348_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2335_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2335_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object* v_s_2356_, lean_object* v_x_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(v_s_2356_, v_x_2357_, v_a_2358_);
lean_dec_ref(v_a_2358_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v_x_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2363_, 0, v_a_2362_);
lean_inc_ref_n(v___x_2363_, 2);
v___x_2364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
lean_ctor_set(v___x_2364_, 2, v___x_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_x_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v_x_2365_, v_a_2366_);
lean_dec_ref(v_x_2365_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v___y_2368_){
_start:
{
lean_inc_ref(v___y_2368_);
return v___y_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v___y_2369_);
lean_dec_ref(v___y_2369_);
return v_res_2370_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2381_; lean_object* v___f_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___f_2381_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___f_2382_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2383_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2384_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2385_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2386_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed), 1, 0);
v___x_2387_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2388_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
lean_ctor_set(v___x_2388_, 1, v___x_2386_);
lean_ctor_set(v___x_2388_, 2, v___x_2385_);
lean_ctor_set(v___x_2388_, 3, v___x_2384_);
lean_ctor_set(v___x_2388_, 4, v___x_2383_);
lean_ctor_set(v___x_2388_, 5, v___f_2382_);
lean_ctor_set(v___x_2388_, 6, v___f_2381_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_);
v___x_2391_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_a_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object* v_env_2394_, lean_object* v_catName_2395_){
_start:
{
lean_object* v___x_2396_; lean_object* v_ext_2397_; lean_object* v_toEnvExtension_2398_; lean_object* v_asyncMode_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v_categories_2402_; lean_object* v___x_2403_; 
v___x_2396_ = l_Lean_Parser_parserExtension;
v_ext_2397_ = lean_ctor_get(v___x_2396_, 1);
v_toEnvExtension_2398_ = lean_ctor_get(v_ext_2397_, 0);
v_asyncMode_2399_ = lean_ctor_get(v_toEnvExtension_2398_, 2);
v___x_2400_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2401_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2400_, v___x_2396_, v_env_2394_, v_asyncMode_2399_);
v_categories_2402_ = lean_ctor_get(v___x_2401_, 2);
lean_inc_ref(v_categories_2402_);
lean_dec(v___x_2401_);
v___x_2403_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2402_, v_catName_2395_);
lean_dec_ref(v_categories_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object* v_env_2404_, lean_object* v_catName_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_Parser_getParserCategory_x3f(v_env_2404_, v_catName_2405_);
lean_dec(v_catName_2405_);
return v_res_2406_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object* v_env_2407_, lean_object* v_catName_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Parser_getParserCategory_x3f(v_env_2407_, v_catName_2408_);
if (lean_obj_tag(v___x_2409_) == 0)
{
uint8_t v___x_2410_; 
v___x_2410_ = 0;
return v___x_2410_;
}
else
{
uint8_t v___x_2411_; 
lean_dec_ref_known(v___x_2409_, 1);
v___x_2411_ = 1;
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object* v_env_2412_, lean_object* v_catName_2413_){
_start:
{
uint8_t v_res_2414_; lean_object* v_r_2415_; 
v_res_2414_ = l_Lean_Parser_isParserCategory(v_env_2412_, v_catName_2413_);
lean_dec(v_catName_2413_);
v_r_2415_ = lean_box(v_res_2414_);
return v_r_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object* v_env_2416_, lean_object* v_catName_2417_, lean_object* v_declName_2418_, uint8_t v_behavior_2419_){
_start:
{
uint8_t v___x_2420_; 
lean_inc_ref(v_env_2416_);
v___x_2420_ = l_Lean_Parser_isParserCategory(v_env_2416_, v_catName_2417_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2421_ = l_Lean_Parser_parserExtension;
v___x_2422_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2422_, 0, v_catName_2417_);
lean_ctor_set(v___x_2422_, 1, v_declName_2418_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*2, v_behavior_2419_);
v___x_2423_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2421_, v_env_2416_, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; 
lean_dec(v_declName_2418_);
lean_dec_ref(v_env_2416_);
v___x_2425_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_2417_);
return v___x_2425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* v_env_2426_, lean_object* v_catName_2427_, lean_object* v_declName_2428_, lean_object* v_behavior_2429_){
_start:
{
uint8_t v_behavior_boxed_2430_; lean_object* v_res_2431_; 
v_behavior_boxed_2430_ = lean_unbox(v_behavior_2429_);
v_res_2431_ = l_Lean_Parser_addParserCategory(v_env_2426_, v_catName_2427_, v_declName_2428_, v_behavior_boxed_2430_);
return v_res_2431_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object* v_env_2432_, lean_object* v_catName_2433_){
_start:
{
lean_object* v___x_2434_; lean_object* v_ext_2435_; lean_object* v_toEnvExtension_2436_; lean_object* v_asyncMode_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v_categories_2440_; lean_object* v___x_2441_; 
v___x_2434_ = l_Lean_Parser_parserExtension;
v_ext_2435_ = lean_ctor_get(v___x_2434_, 1);
v_toEnvExtension_2436_ = lean_ctor_get(v_ext_2435_, 0);
v_asyncMode_2437_ = lean_ctor_get(v_toEnvExtension_2436_, 2);
v___x_2438_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2439_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2438_, v___x_2434_, v_env_2432_, v_asyncMode_2437_);
v_categories_2440_ = lean_ctor_get(v___x_2439_, 2);
lean_inc_ref(v_categories_2440_);
lean_dec(v___x_2439_);
v___x_2441_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2440_, v_catName_2433_);
lean_dec_ref(v_categories_2440_);
if (lean_obj_tag(v___x_2441_) == 0)
{
uint8_t v___x_2442_; 
v___x_2442_ = 0;
return v___x_2442_;
}
else
{
lean_object* v_val_2443_; uint8_t v_behavior_2444_; 
v_val_2443_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_val_2443_);
lean_dec_ref_known(v___x_2441_, 1);
v_behavior_2444_ = lean_ctor_get_uint8(v_val_2443_, sizeof(void*)*3);
lean_dec(v_val_2443_);
return v_behavior_2444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object* v_env_2445_, lean_object* v_catName_2446_){
_start:
{
uint8_t v_res_2447_; lean_object* v_r_2448_; 
v_res_2447_ = l_Lean_Parser_leadingIdentBehavior(v_env_2445_, v_catName_2446_);
lean_dec(v_catName_2446_);
v_r_2448_ = lean_box(v_res_2447_);
return v_r_2448_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(lean_object* v_x_2449_, lean_object* v_x_2450_){
_start:
{
if (lean_obj_tag(v_x_2450_) == 0)
{
return v_x_2449_;
}
else
{
lean_object* v_head_2451_; lean_object* v_tail_2452_; lean_object* v___x_2453_; 
v_head_2451_ = lean_ctor_get(v_x_2450_, 0);
lean_inc_n(v_head_2451_, 2);
v_tail_2452_ = lean_ctor_get(v_x_2450_, 1);
lean_inc(v_tail_2452_);
lean_dec_ref_known(v_x_2450_, 2);
v___x_2453_ = l_Lean_Data_Trie_insert___redArg(v_x_2449_, v_head_2451_, v_head_2451_);
lean_dec(v_head_2451_);
v_x_2449_ = v___x_2453_;
v_x_2450_ = v_tail_2452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__0(lean_object* v_info_2455_, lean_object* v_ctx_2456_){
_start:
{
lean_object* v_toInputContext_2457_; lean_object* v_toParserModuleContext_2458_; lean_object* v_toCacheableParserContext_2459_; lean_object* v_tokens_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2471_; 
v_toInputContext_2457_ = lean_ctor_get(v_ctx_2456_, 0);
v_toParserModuleContext_2458_ = lean_ctor_get(v_ctx_2456_, 1);
v_toCacheableParserContext_2459_ = lean_ctor_get(v_ctx_2456_, 2);
v_tokens_2460_ = lean_ctor_get(v_ctx_2456_, 3);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_ctx_2456_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2462_ = v_ctx_2456_;
v_isShared_2463_ = v_isSharedCheck_2471_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_tokens_2460_);
lean_inc(v_toCacheableParserContext_2459_);
lean_inc(v_toParserModuleContext_2458_);
lean_inc(v_toInputContext_2457_);
lean_dec(v_ctx_2456_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2471_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v_collectTokens_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
v_collectTokens_2464_ = lean_ctor_get(v_info_2455_, 0);
lean_inc_ref(v_collectTokens_2464_);
lean_dec_ref(v_info_2455_);
v___x_2465_ = lean_box(0);
v___x_2466_ = lean_apply_1(v_collectTokens_2464_, v___x_2465_);
v___x_2467_ = l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(v_tokens_2460_, v___x_2466_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 3, v___x_2467_);
v___x_2469_ = v___x_2462_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_toInputContext_2457_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_toParserModuleContext_2458_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_toCacheableParserContext_2459_);
lean_ctor_set(v_reuseFailAlloc_2470_, 3, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1(lean_object* v_categories_2472_, lean_object* v_declName_2473_, lean_object* v___x_2474_, lean_object* v_ctx_2475_, lean_object* v_s_2476_, lean_object* v_evalFallback_x3f_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Parser_mkParserOfConstant(v_categories_2472_, v_declName_2473_, v___x_2474_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v_snd_2481_; lean_object* v_info_2482_; lean_object* v_fn_2483_; lean_object* v___f_2484_; lean_object* v___x_2485_; 
lean_dec(v_evalFallback_x3f_2477_);
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref_known(v___x_2479_, 1);
v_snd_2481_ = lean_ctor_get(v_a_2480_, 1);
lean_inc(v_snd_2481_);
lean_dec(v_a_2480_);
v_info_2482_ = lean_ctor_get(v_snd_2481_, 0);
lean_inc_ref(v_info_2482_);
v_fn_2483_ = lean_ctor_get(v_snd_2481_, 1);
lean_inc_ref(v_fn_2483_);
lean_dec(v_snd_2481_);
v___f_2484_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__0), 2, 1);
lean_closure_set(v___f_2484_, 0, v_info_2482_);
v___x_2485_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2484_, v_fn_2483_, v_ctx_2475_, v_s_2476_);
return v___x_2485_;
}
else
{
if (lean_obj_tag(v_evalFallback_x3f_2477_) == 1)
{
lean_object* v_val_2486_; lean_object* v___x_2487_; 
lean_dec_ref_known(v___x_2479_, 1);
v_val_2486_ = lean_ctor_get(v_evalFallback_x3f_2477_, 0);
lean_inc(v_val_2486_);
lean_dec_ref_known(v_evalFallback_x3f_2477_, 1);
v___x_2487_ = lean_apply_2(v_val_2486_, v_ctx_2475_, v_s_2476_);
return v___x_2487_;
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; 
lean_dec(v_evalFallback_x3f_2477_);
lean_dec_ref(v_ctx_2475_);
v_a_2488_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2479_, 1);
v___x_2489_ = lean_io_error_to_string(v_a_2488_);
v___x_2490_ = lean_box(0);
v___x_2491_ = 1;
v___x_2492_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2476_, v___x_2489_, v___x_2490_, v___x_2491_);
return v___x_2492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed(lean_object* v_categories_2493_, lean_object* v_declName_2494_, lean_object* v___x_2495_, lean_object* v_ctx_2496_, lean_object* v_s_2497_, lean_object* v_evalFallback_x3f_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_Parser_evalParserConstUnsafe___lam__1(v_categories_2493_, v_declName_2494_, v___x_2495_, v_ctx_2496_, v_s_2497_, v_evalFallback_x3f_2498_);
lean_dec_ref(v___x_2495_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* v_declName_2501_, lean_object* v_evalFallback_x3f_2502_, lean_object* v_ctx_2503_, lean_object* v_s_2504_){
_start:
{
lean_object* v_toParserModuleContext_2505_; lean_object* v_env_2506_; lean_object* v_options_2507_; lean_object* v___x_2508_; lean_object* v_ext_2509_; lean_object* v_toEnvExtension_2510_; lean_object* v_asyncMode_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v_categories_2514_; lean_object* v___x_2515_; lean_object* v___f_2516_; lean_object* v___x_2517_; 
v_toParserModuleContext_2505_ = lean_ctor_get(v_ctx_2503_, 1);
v_env_2506_ = lean_ctor_get(v_toParserModuleContext_2505_, 0);
v_options_2507_ = lean_ctor_get(v_toParserModuleContext_2505_, 1);
v___x_2508_ = l_Lean_Parser_parserExtension;
v_ext_2509_ = lean_ctor_get(v___x_2508_, 1);
v_toEnvExtension_2510_ = lean_ctor_get(v_ext_2509_, 0);
v_asyncMode_2511_ = lean_ctor_get(v_toEnvExtension_2510_, 2);
v___x_2512_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref_n(v_env_2506_, 2);
v___x_2513_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2512_, v___x_2508_, v_env_2506_, v_asyncMode_2511_);
v_categories_2514_ = lean_ctor_get(v___x_2513_, 2);
lean_inc_ref(v_categories_2514_);
lean_dec(v___x_2513_);
lean_inc_ref(v_options_2507_);
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v_env_2506_);
lean_ctor_set(v___x_2515_, 1, v_options_2507_);
v___f_2516_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2516_, 0, v_categories_2514_);
lean_closure_set(v___f_2516_, 1, v_declName_2501_);
lean_closure_set(v___f_2516_, 2, v___x_2515_);
lean_closure_set(v___f_2516_, 3, v_ctx_2503_);
lean_closure_set(v___f_2516_, 4, v_s_2504_);
lean_closure_set(v___f_2516_, 5, v_evalFallback_x3f_2502_);
v___x_2517_ = l_unsafeBaseIO___redArg(v___f_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object* v_name_2518_, lean_object* v_decl_2519_, lean_object* v_ref_2520_){
_start:
{
lean_object* v_defValue_2522_; lean_object* v_descr_2523_; lean_object* v_deprecation_x3f_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v_defValue_2522_ = lean_ctor_get(v_decl_2519_, 0);
v_descr_2523_ = lean_ctor_get(v_decl_2519_, 1);
v_deprecation_x3f_2524_ = lean_ctor_get(v_decl_2519_, 2);
v___x_2525_ = lean_alloc_ctor(1, 0, 1);
v___x_2526_ = lean_unbox(v_defValue_2522_);
lean_ctor_set_uint8(v___x_2525_, 0, v___x_2526_);
lean_inc(v_deprecation_x3f_2524_);
lean_inc_ref(v_descr_2523_);
lean_inc_n(v_name_2518_, 2);
v___x_2527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2527_, 0, v_name_2518_);
lean_ctor_set(v___x_2527_, 1, v_ref_2520_);
lean_ctor_set(v___x_2527_, 2, v___x_2525_);
lean_ctor_set(v___x_2527_, 3, v_descr_2523_);
lean_ctor_set(v___x_2527_, 4, v_deprecation_x3f_2524_);
v___x_2528_ = lean_register_option(v_name_2518_, v___x_2527_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2536_; 
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2536_ == 0)
{
lean_object* v_unused_2537_; 
v_unused_2537_ = lean_ctor_get(v___x_2528_, 0);
lean_dec(v_unused_2537_);
v___x_2530_ = v___x_2528_;
v_isShared_2531_ = v_isSharedCheck_2536_;
goto v_resetjp_2529_;
}
else
{
lean_dec(v___x_2528_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2536_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
lean_inc(v_defValue_2522_);
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v_name_2518_);
lean_ctor_set(v___x_2532_, 1, v_defValue_2522_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v___x_2532_);
v___x_2534_ = v___x_2530_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_name_2518_);
v_a_2538_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2528_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2528_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2546_, lean_object* v_decl_2547_, lean_object* v_ref_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v_name_2546_, v_decl_2547_, v_ref_2548_);
lean_dec_ref(v_decl_2547_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2568_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2569_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2570_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2571_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v___x_2568_, v___x_2569_, v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object* v_a_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(lean_object* v_o_2577_, lean_object* v_k_2578_, uint8_t v_v_2579_){
_start:
{
lean_object* v_map_2580_; uint8_t v_hasTrace_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2595_; 
v_map_2580_ = lean_ctor_get(v_o_2577_, 0);
v_hasTrace_2581_ = lean_ctor_get_uint8(v_o_2577_, sizeof(void*)*1);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_o_2577_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2583_ = v_o_2577_;
v_isShared_2584_ = v_isSharedCheck_2595_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_map_2580_);
lean_dec(v_o_2577_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2595_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2585_, 0, v_v_2579_);
lean_inc(v_k_2578_);
v___x_2586_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2578_, v___x_2585_, v_map_2580_);
if (v_hasTrace_2581_ == 0)
{
lean_object* v___x_2587_; uint8_t v___x_2588_; lean_object* v___x_2590_; 
v___x_2587_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_2588_ = l_Lean_Name_isPrefixOf(v___x_2587_, v_k_2578_);
lean_dec(v_k_2578_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2586_);
v___x_2590_ = v___x_2583_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2586_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*1, v___x_2588_);
return v___x_2590_;
}
}
else
{
lean_object* v___x_2593_; 
lean_dec(v_k_2578_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2586_);
v___x_2593_ = v___x_2583_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2594_, sizeof(void*)*1, v_hasTrace_2581_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___boxed(lean_object* v_o_2596_, lean_object* v_k_2597_, lean_object* v_v_2598_){
_start:
{
uint8_t v_v_boxed_2599_; lean_object* v_res_2600_; 
v_v_boxed_2599_ = lean_unbox(v_v_2598_);
v_res_2600_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_o_2596_, v_k_2597_, v_v_boxed_2599_);
return v_res_2600_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(lean_object* v_opts_2601_, lean_object* v_opt_2602_){
_start:
{
lean_object* v_name_2603_; lean_object* v_defValue_2604_; lean_object* v_map_2605_; lean_object* v___x_2606_; 
v_name_2603_ = lean_ctor_get(v_opt_2602_, 0);
v_defValue_2604_ = lean_ctor_get(v_opt_2602_, 1);
v_map_2605_ = lean_ctor_get(v_opts_2601_, 0);
v___x_2606_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2605_, v_name_2603_);
if (lean_obj_tag(v___x_2606_) == 0)
{
uint8_t v___x_2607_; 
v___x_2607_ = lean_unbox(v_defValue_2604_);
return v___x_2607_;
}
else
{
lean_object* v_val_2608_; 
v_val_2608_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_val_2608_);
lean_dec_ref_known(v___x_2606_, 1);
if (lean_obj_tag(v_val_2608_) == 1)
{
uint8_t v_v_2609_; 
v_v_2609_ = lean_ctor_get_uint8(v_val_2608_, 0);
lean_dec_ref_known(v_val_2608_, 0);
return v_v_2609_;
}
else
{
uint8_t v___x_2610_; 
lean_dec(v_val_2608_);
v___x_2610_ = lean_unbox(v_defValue_2604_);
return v___x_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1___boxed(lean_object* v_opts_2611_, lean_object* v_opt_2612_){
_start:
{
uint8_t v_res_2613_; lean_object* v_r_2614_; 
v_res_2613_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_opts_2611_, v_opt_2612_);
lean_dec_ref(v_opt_2612_);
lean_dec_ref(v_opts_2611_);
v_r_2614_ = lean_box(v_res_2613_);
return v_r_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0(lean_object* v_ctx_2620_){
_start:
{
lean_object* v_toParserModuleContext_2621_; lean_object* v_toInputContext_2622_; lean_object* v_toCacheableParserContext_2623_; lean_object* v_tokens_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2645_; 
v_toParserModuleContext_2621_ = lean_ctor_get(v_ctx_2620_, 1);
v_toInputContext_2622_ = lean_ctor_get(v_ctx_2620_, 0);
v_toCacheableParserContext_2623_ = lean_ctor_get(v_ctx_2620_, 2);
v_tokens_2624_ = lean_ctor_get(v_ctx_2620_, 3);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_ctx_2620_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2626_ = v_ctx_2620_;
v_isShared_2627_ = v_isSharedCheck_2645_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_tokens_2624_);
lean_inc(v_toCacheableParserContext_2623_);
lean_inc(v_toParserModuleContext_2621_);
lean_inc(v_toInputContext_2622_);
lean_dec(v_ctx_2620_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2645_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v_env_2628_; lean_object* v_options_2629_; lean_object* v_currNamespace_2630_; lean_object* v_openDecls_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2644_; 
v_env_2628_ = lean_ctor_get(v_toParserModuleContext_2621_, 0);
v_options_2629_ = lean_ctor_get(v_toParserModuleContext_2621_, 1);
v_currNamespace_2630_ = lean_ctor_get(v_toParserModuleContext_2621_, 2);
v_openDecls_2631_ = lean_ctor_get(v_toParserModuleContext_2621_, 3);
v_isSharedCheck_2644_ = !lean_is_exclusive(v_toParserModuleContext_2621_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2633_ = v_toParserModuleContext_2621_;
v_isShared_2634_ = v_isSharedCheck_2644_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_openDecls_2631_);
lean_inc(v_currNamespace_2630_);
lean_inc(v_options_2629_);
lean_inc(v_env_2628_);
lean_dec(v_toParserModuleContext_2621_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2644_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2635_; uint8_t v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2635_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_2636_ = 0;
v___x_2637_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_2629_, v___x_2635_, v___x_2636_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 1, v___x_2637_);
v___x_2639_ = v___x_2633_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_env_2628_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_currNamespace_2630_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v_openDecls_2631_);
v___x_2639_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2641_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 1, v___x_2639_);
v___x_2641_ = v___x_2626_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_toInputContext_2622_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_toCacheableParserContext_2623_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v_tokens_2624_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object* v_fn_2646_, lean_object* v_declName_2647_, lean_object* v___f_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_toParserModuleContext_2651_; lean_object* v_toCacheableParserContext_2652_; uint8_t v___y_2654_; lean_object* v_quotDepth_2666_; uint8_t v_suppressInsideQuot_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v_toParserModuleContext_2651_ = lean_ctor_get(v___y_2649_, 1);
v_toCacheableParserContext_2652_ = lean_ctor_get(v___y_2649_, 2);
v_quotDepth_2666_ = lean_ctor_get(v_toCacheableParserContext_2652_, 1);
v_suppressInsideQuot_2667_ = lean_ctor_get_uint8(v_toCacheableParserContext_2652_, sizeof(void*)*4);
v___x_2668_ = lean_unsigned_to_nat(0u);
v___x_2669_ = lean_nat_dec_lt(v___x_2668_, v_quotDepth_2666_);
if (v___x_2669_ == 0)
{
v___y_2654_ = v___x_2669_;
goto v___jp_2653_;
}
else
{
if (v_suppressInsideQuot_2667_ == 0)
{
v___y_2654_ = v___x_2669_;
goto v___jp_2653_;
}
else
{
lean_object* v___x_2670_; 
lean_dec_ref(v___f_2648_);
lean_dec(v_declName_2647_);
v___x_2670_ = lean_apply_2(v_fn_2646_, v___y_2649_, v___y_2650_);
return v___x_2670_;
}
}
v___jp_2653_:
{
if (v___y_2654_ == 0)
{
lean_object* v___x_2655_; 
lean_dec_ref(v___f_2648_);
lean_dec(v_declName_2647_);
v___x_2655_ = lean_apply_2(v_fn_2646_, v___y_2649_, v___y_2650_);
return v___x_2655_;
}
else
{
lean_object* v_env_2656_; lean_object* v_options_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v_env_2656_ = lean_ctor_get(v_toParserModuleContext_2651_, 0);
v_options_2657_ = lean_ctor_get(v_toParserModuleContext_2651_, 1);
v___x_2658_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_2659_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_2657_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; 
lean_dec_ref(v___f_2648_);
lean_dec(v_declName_2647_);
v___x_2660_ = lean_apply_2(v_fn_2646_, v___y_2649_, v___y_2650_);
return v___x_2660_;
}
else
{
uint8_t v___x_2661_; 
lean_inc(v_declName_2647_);
lean_inc_ref(v_env_2656_);
v___x_2661_ = l_Lean_Environment_contains(v_env_2656_, v_declName_2647_, v___x_2659_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
lean_dec_ref(v___f_2648_);
lean_dec(v_declName_2647_);
v___x_2662_ = lean_apply_2(v_fn_2646_, v___y_2649_, v___y_2650_);
return v___x_2662_;
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2663_, 0, v_fn_2646_);
v___x_2664_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_2664_, 0, v_declName_2647_);
lean_closure_set(v___x_2664_, 1, v___x_2663_);
v___x_2665_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2648_, v___x_2664_, v___y_2649_, v___y_2650_);
return v___x_2665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object* v_declName_2672_, lean_object* v_p_2673_){
_start:
{
lean_object* v_info_2674_; lean_object* v_fn_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2684_; 
v_info_2674_ = lean_ctor_get(v_p_2673_, 0);
v_fn_2675_ = lean_ctor_get(v_p_2673_, 1);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_p_2673_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2677_ = v_p_2673_;
v_isShared_2678_ = v_isSharedCheck_2684_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_fn_2675_);
lean_inc(v_info_2674_);
lean_dec(v_p_2673_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2684_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___f_2679_; lean_object* v___f_2680_; lean_object* v___x_2682_; 
v___f_2679_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___closed__0));
v___f_2680_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__1), 5, 3);
lean_closure_set(v___f_2680_, 0, v_fn_2675_);
lean_closure_set(v___f_2680_, 1, v_declName_2672_);
lean_closure_set(v___f_2680_, 2, v___f_2679_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 1, v___f_2680_);
v___x_2682_ = v___x_2677_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_info_2674_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___f_2680_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object* v_catName_2685_, lean_object* v_declName_2686_, uint8_t v_leading_2687_, lean_object* v_p_2688_, lean_object* v_prio_2689_){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v_p_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2691_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_2692_ = lean_st_ref_get(v___x_2691_);
lean_inc_n(v_declName_2686_, 2);
v_p_2693_ = l_Lean_Parser_evalInsideQuot(v_declName_2686_, v_p_2688_);
lean_inc_ref(v_p_2693_);
v___x_2694_ = l_Lean_Parser_addParser(v___x_2692_, v_catName_2685_, v_declName_2686_, v_leading_2687_, v_p_2693_, v_prio_2689_);
v___x_2695_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_2694_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v_info_2700_; lean_object* v_collectKinds_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2697_ = lean_st_ref_swap(v___x_2691_, v_a_2696_);
lean_dec(v___x_2697_);
v___x_2698_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_2699_ = lean_st_ref_take(v___x_2698_);
v_info_2700_ = lean_ctor_get(v_p_2693_, 0);
lean_inc_ref(v_info_2700_);
lean_dec_ref(v_p_2693_);
v_collectKinds_2701_ = lean_ctor_get(v_info_2700_, 1);
lean_inc_ref(v_collectKinds_2701_);
v___x_2702_ = lean_apply_1(v_collectKinds_2701_, v___x_2699_);
v___x_2703_ = lean_st_ref_put(v___x_2698_, v___x_2702_);
v___x_2704_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_2700_, v_declName_2686_);
return v___x_2704_;
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec_ref(v_p_2693_);
lean_dec(v_declName_2686_);
v_a_2705_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2695_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2695_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* v_catName_2713_, lean_object* v_declName_2714_, lean_object* v_leading_2715_, lean_object* v_p_2716_, lean_object* v_prio_2717_, lean_object* v_a_2718_){
_start:
{
uint8_t v_leading_boxed_2719_; lean_object* v_res_2720_; 
v_leading_boxed_2719_ = lean_unbox(v_leading_2715_);
v_res_2720_ = l_Lean_Parser_addBuiltinParser(v_catName_2713_, v_declName_2714_, v_leading_boxed_2719_, v_p_2716_, v_prio_2717_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* v_catName_2721_, lean_object* v_declName_2722_, lean_object* v_p_2723_, lean_object* v_prio_2724_){
_start:
{
uint8_t v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = 1;
v___x_2727_ = l_Lean_Parser_addBuiltinParser(v_catName_2721_, v_declName_2722_, v___x_2726_, v_p_2723_, v_prio_2724_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object* v_catName_2728_, lean_object* v_declName_2729_, lean_object* v_p_2730_, lean_object* v_prio_2731_, lean_object* v_a_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_Parser_addBuiltinLeadingParser(v_catName_2728_, v_declName_2729_, v_p_2730_, v_prio_2731_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* v_catName_2734_, lean_object* v_declName_2735_, lean_object* v_p_2736_, lean_object* v_prio_2737_){
_start:
{
uint8_t v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = 0;
v___x_2740_ = l_Lean_Parser_addBuiltinParser(v_catName_2734_, v_declName_2735_, v___x_2739_, v_p_2736_, v_prio_2737_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object* v_catName_2741_, lean_object* v_declName_2742_, lean_object* v_p_2743_, lean_object* v_prio_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_Parser_addBuiltinTrailingParser(v_catName_2741_, v_declName_2742_, v_p_2743_, v_prio_2744_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object* v_kind_2747_){
_start:
{
uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2748_ = 1;
lean_inc(v_kind_2747_);
v___x_2749_ = l_Lean_Name_toString(v_kind_2747_, v___x_2748_);
v___x_2750_ = l_Lean_Parser_mkAntiquot(v___x_2749_, v_kind_2747_, v___x_2748_, v___x_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object* v_kind_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v___x_2754_; lean_object* v_fn_2755_; lean_object* v___x_2756_; 
v___x_2754_ = l_Lean_Parser_mkCategoryAntiquotParser(v_kind_2751_);
v_fn_2755_ = lean_ctor_get(v___x_2754_, 1);
lean_inc_ref(v_fn_2755_);
lean_dec_ref(v___x_2754_);
v___x_2756_ = lean_apply_2(v_fn_2755_, v_a_2752_, v_a_2753_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl___lam__0(lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___x_2760_; lean_object* v_fn_2761_; lean_object* v___x_2762_; 
v___x_2760_ = l_Lean_Parser_mkCategoryAntiquotParser(v___y_2757_);
v_fn_2761_ = lean_ctor_get(v___x_2760_, 1);
lean_inc_ref(v_fn_2761_);
lean_dec_ref(v___x_2760_);
v___x_2762_ = lean_apply_2(v_fn_2761_, v___y_2758_, v___y_2759_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* v_catName_2771_, lean_object* v_ctx_2772_, lean_object* v_s_2773_){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; uint8_t v___x_2777_; lean_object* v___y_2779_; 
v___x_2774_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2775_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__1));
v___x_2776_ = lean_name_eq(v_catName_2771_, v___x_2775_);
v___x_2777_ = 1;
if (v___x_2776_ == 0)
{
v___y_2779_ = v_catName_2771_;
goto v___jp_2778_;
}
else
{
lean_object* v___x_2801_; 
lean_dec(v_catName_2771_);
v___x_2801_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__5));
v___y_2779_ = v___x_2801_;
goto v___jp_2778_;
}
v___jp_2778_:
{
lean_object* v_toParserModuleContext_2780_; lean_object* v_env_2781_; lean_object* v___x_2782_; lean_object* v_ext_2783_; lean_object* v_toEnvExtension_2784_; lean_object* v_asyncMode_2785_; lean_object* v___x_2786_; lean_object* v_categories_2787_; lean_object* v___x_2788_; 
v_toParserModuleContext_2780_ = lean_ctor_get(v_ctx_2772_, 1);
v_env_2781_ = lean_ctor_get(v_toParserModuleContext_2780_, 0);
v___x_2782_ = l_Lean_Parser_parserExtension;
v_ext_2783_ = lean_ctor_get(v___x_2782_, 1);
v_toEnvExtension_2784_ = lean_ctor_get(v_ext_2783_, 0);
v_asyncMode_2785_ = lean_ctor_get(v_toEnvExtension_2784_, 2);
lean_inc_ref(v_env_2781_);
v___x_2786_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2774_, v___x_2782_, v_env_2781_, v_asyncMode_2785_);
v_categories_2787_ = lean_ctor_get(v___x_2786_, 2);
lean_inc_ref(v_categories_2787_);
lean_dec(v___x_2786_);
v___x_2788_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2787_, v___y_2779_);
lean_dec_ref(v_categories_2787_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
lean_dec_ref(v_ctx_2772_);
v___x_2789_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__2));
v___x_2790_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2779_, v___x_2777_);
v___x_2791_ = lean_string_append(v___x_2789_, v___x_2790_);
lean_dec_ref(v___x_2790_);
v___x_2792_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__3));
v___x_2793_ = lean_string_append(v___x_2791_, v___x_2792_);
v___x_2794_ = lean_box(0);
v___x_2795_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2773_, v___x_2793_, v___x_2794_, v___x_2777_);
return v___x_2795_;
}
else
{
lean_object* v_val_2796_; lean_object* v_tables_2797_; uint8_t v_behavior_2798_; lean_object* v___f_2799_; lean_object* v___x_2800_; 
v_val_2796_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_val_2796_);
lean_dec_ref_known(v___x_2788_, 1);
v_tables_2797_ = lean_ctor_get(v_val_2796_, 2);
lean_inc_ref(v_tables_2797_);
v_behavior_2798_ = lean_ctor_get_uint8(v_val_2796_, sizeof(void*)*3);
lean_dec(v_val_2796_);
lean_inc(v___y_2779_);
v___f_2799_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl___lam__0), 3, 1);
lean_closure_set(v___f_2799_, 0, v___y_2779_);
v___x_2800_ = l_Lean_Parser_prattParser(v___y_2779_, v_tables_2797_, v_behavior_2798_, v___f_2799_, v_ctx_2772_, v_s_2773_);
return v___x_2800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2804_ = l_Lean_Parser_categoryParserFnRef;
v___x_2805_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_));
v___x_2806_ = lean_st_ref_swap(v___x_2804_, v___x_2805_);
lean_dec(v___x_2806_);
v___x_2807_ = lean_box(0);
v___x_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object* v_a_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
return v_res_2810_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2811_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0);
v___x_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
return v___x_2813_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object* v_ext_2816_, lean_object* v_b_2817_, uint8_t v_kind_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_currNamespace_2822_; lean_object* v___x_2823_; lean_object* v_env_2824_; lean_object* v_nextMacroScope_2825_; lean_object* v_ngen_2826_; lean_object* v_auxDeclNGen_2827_; lean_object* v_traceState_2828_; lean_object* v_messages_2829_; lean_object* v_infoState_2830_; lean_object* v_snapshotTasks_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2843_; 
v_currNamespace_2822_ = lean_ctor_get(v___y_2819_, 6);
v___x_2823_ = lean_st_ref_take(v___y_2820_);
v_env_2824_ = lean_ctor_get(v___x_2823_, 0);
v_nextMacroScope_2825_ = lean_ctor_get(v___x_2823_, 1);
v_ngen_2826_ = lean_ctor_get(v___x_2823_, 2);
v_auxDeclNGen_2827_ = lean_ctor_get(v___x_2823_, 3);
v_traceState_2828_ = lean_ctor_get(v___x_2823_, 4);
v_messages_2829_ = lean_ctor_get(v___x_2823_, 6);
v_infoState_2830_ = lean_ctor_get(v___x_2823_, 7);
v_snapshotTasks_2831_ = lean_ctor_get(v___x_2823_, 8);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v___x_2823_, 5);
lean_dec(v_unused_2844_);
v___x_2833_ = v___x_2823_;
v_isShared_2834_ = v_isSharedCheck_2843_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_snapshotTasks_2831_);
lean_inc(v_infoState_2830_);
lean_inc(v_messages_2829_);
lean_inc(v_traceState_2828_);
lean_inc(v_auxDeclNGen_2827_);
lean_inc(v_ngen_2826_);
lean_inc(v_nextMacroScope_2825_);
lean_inc(v_env_2824_);
lean_dec(v___x_2823_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2843_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
lean_inc(v_currNamespace_2822_);
v___x_2835_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2824_, v_ext_2816_, v_b_2817_, v_kind_2818_, v_currNamespace_2822_);
v___x_2836_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 5, v___x_2836_);
lean_ctor_set(v___x_2833_, 0, v___x_2835_);
v___x_2838_ = v___x_2833_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_nextMacroScope_2825_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v_ngen_2826_);
lean_ctor_set(v_reuseFailAlloc_2842_, 3, v_auxDeclNGen_2827_);
lean_ctor_set(v_reuseFailAlloc_2842_, 4, v_traceState_2828_);
lean_ctor_set(v_reuseFailAlloc_2842_, 5, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2842_, 6, v_messages_2829_);
lean_ctor_set(v_reuseFailAlloc_2842_, 7, v_infoState_2830_);
lean_ctor_set(v_reuseFailAlloc_2842_, 8, v_snapshotTasks_2831_);
v___x_2838_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = lean_st_ref_put(v___y_2820_, v___x_2838_);
v___x_2840_ = lean_box(0);
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object* v_ext_2845_, lean_object* v_b_2846_, lean_object* v_kind_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
uint8_t v_kind_boxed_2851_; lean_object* v_res_2852_; 
v_kind_boxed_2851_ = lean_unbox(v_kind_2847_);
v_res_2852_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2845_, v_b_2846_, v_kind_boxed_2851_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object* v_00_u03b1_2853_, lean_object* v_00_u03b2_2854_, lean_object* v_00_u03c3_2855_, lean_object* v_ext_2856_, lean_object* v_b_2857_, uint8_t v_kind_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2856_, v_b_2857_, v_kind_2858_, v___y_2859_, v___y_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object* v_00_u03b1_2863_, lean_object* v_00_u03b2_2864_, lean_object* v_00_u03c3_2865_, lean_object* v_ext_2866_, lean_object* v_b_2867_, lean_object* v_kind_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
uint8_t v_kind_boxed_2872_; lean_object* v_res_2873_; 
v_kind_boxed_2872_ = lean_unbox(v_kind_2868_);
v_res_2873_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(v_00_u03b1_2863_, v_00_u03b2_2864_, v_00_u03c3_2865_, v_ext_2866_, v_b_2867_, v_kind_boxed_2872_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object* v_x_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
if (lean_obj_tag(v_x_2874_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v_a_2878_ = lean_ctor_get(v_x_2874_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v_x_2874_, 1);
v___x_2879_ = l_Lean_stringToMessageData(v_a_2878_);
v___x_2880_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2879_, v___y_2875_, v___y_2876_);
return v___x_2880_;
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
v_a_2881_ = lean_ctor_get(v_x_2874_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_x_2874_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v_x_2874_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v_x_2874_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
lean_ctor_set_tag(v___x_2883_, 0);
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object* v_x_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object* v_tk_2894_, uint8_t v_kind_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v___x_2899_; lean_object* v_env_2900_; lean_object* v___x_2901_; lean_object* v_ext_2902_; lean_object* v_toEnvExtension_2903_; lean_object* v_asyncMode_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v_tokens_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2899_ = lean_st_ref_get(v_a_2897_);
v_env_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc_ref(v_env_2900_);
lean_dec(v___x_2899_);
v___x_2901_ = l_Lean_Parser_parserExtension;
v_ext_2902_ = lean_ctor_get(v___x_2901_, 1);
v_toEnvExtension_2903_ = lean_ctor_get(v_ext_2902_, 0);
v_asyncMode_2904_ = lean_ctor_get(v_toEnvExtension_2903_, 2);
v___x_2905_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2906_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2905_, v___x_2901_, v_env_2900_, v_asyncMode_2904_);
v_tokens_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc_ref(v_tokens_2907_);
lean_dec(v___x_2906_);
lean_inc_ref(v_tk_2894_);
v___x_2908_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_2907_, v_tk_2894_);
v___x_2909_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v___x_2908_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
lean_dec_ref_known(v___x_2909_, 1);
v___x_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2910_, 0, v_tk_2894_);
v___x_2911_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_2901_, v___x_2910_, v_kind_2895_, v_a_2896_, v_a_2897_);
return v___x_2911_;
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec_ref(v_tk_2894_);
v_a_2912_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2909_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2909_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object* v_tk_2920_, lean_object* v_kind_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
uint8_t v_kind_boxed_2925_; lean_object* v_res_2926_; 
v_kind_boxed_2925_ = lean_unbox(v_kind_2921_);
v_res_2926_ = l_Lean_Parser_addToken(v_tk_2920_, v_kind_boxed_2925_, v_a_2922_, v_a_2923_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_object* v_00_u03b1_2927_, lean_object* v_x_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2928_, v___y_2929_, v___y_2930_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___boxed(lean_object* v_00_u03b1_2933_, lean_object* v_x_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(v_00_u03b1_2933_, v_x_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object* v_env_2939_, lean_object* v_k_2940_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = l_Lean_Parser_parserExtension;
v___x_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_k_2940_);
v___x_2943_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2941_, v_env_2939_, v___x_2942_);
return v___x_2943_;
}
}
static uint8_t _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0(void){
_start:
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = lean_box(0);
v___x_2945_ = lean_internal_is_stage0(v___x_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object* v_env_2946_, lean_object* v_k_2947_){
_start:
{
lean_object* v___x_2948_; lean_object* v_ext_2949_; lean_object* v_toEnvExtension_2950_; lean_object* v_asyncMode_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v_kinds_2954_; uint8_t v___x_2955_; 
v___x_2948_ = l_Lean_Parser_parserExtension;
v_ext_2949_ = lean_ctor_get(v___x_2948_, 1);
v_toEnvExtension_2950_ = lean_ctor_get(v_ext_2949_, 0);
v_asyncMode_2951_ = lean_ctor_get(v_toEnvExtension_2950_, 2);
v___x_2952_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_2946_);
v___x_2953_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2952_, v___x_2948_, v_env_2946_, v_asyncMode_2951_);
v_kinds_2954_ = lean_ctor_get(v___x_2953_, 1);
lean_inc_ref(v_kinds_2954_);
lean_dec(v___x_2953_);
v___x_2955_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_2954_, v_k_2947_);
lean_dec_ref(v_kinds_2954_);
if (v___x_2955_ == 0)
{
uint8_t v___x_2956_; 
v___x_2956_ = lean_uint8_once(&l_Lean_Parser_isValidSyntaxNodeKind___closed__0, &l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once, _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0);
if (v___x_2956_ == 0)
{
lean_dec(v_k_2947_);
lean_dec_ref(v_env_2946_);
return v___x_2956_;
}
else
{
uint8_t v___x_2957_; 
v___x_2957_ = l_Lean_Environment_contains(v_env_2946_, v_k_2947_, v___x_2956_);
return v___x_2957_;
}
}
else
{
lean_dec(v_k_2947_);
lean_dec_ref(v_env_2946_);
return v___x_2955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* v_env_2958_, lean_object* v_k_2959_){
_start:
{
uint8_t v_res_2960_; lean_object* v_r_2961_; 
v_res_2960_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_2958_, v_k_2959_);
v_r_2961_ = lean_box(v_res_2960_);
return v_r_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds___lam__0(lean_object* v_ks_2962_, lean_object* v_k_2963_, lean_object* v_x_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2965_, 0, v_k_2963_);
lean_ctor_set(v___x_2965_, 1, v_ks_2962_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2966_, lean_object* v_keys_2967_, lean_object* v_vals_2968_, lean_object* v_i_2969_, lean_object* v_acc_2970_){
_start:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = lean_array_get_size(v_keys_2967_);
v___x_2972_ = lean_nat_dec_lt(v_i_2969_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_dec(v_i_2969_);
lean_dec(v_f_2966_);
return v_acc_2970_;
}
else
{
lean_object* v_k_2973_; lean_object* v_v_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v_k_2973_ = lean_array_fget_borrowed(v_keys_2967_, v_i_2969_);
v_v_2974_ = lean_array_fget_borrowed(v_vals_2968_, v_i_2969_);
lean_inc(v_f_2966_);
lean_inc(v_v_2974_);
lean_inc(v_k_2973_);
v___x_2975_ = lean_apply_3(v_f_2966_, v_acc_2970_, v_k_2973_, v_v_2974_);
v___x_2976_ = lean_unsigned_to_nat(1u);
v___x_2977_ = lean_nat_add(v_i_2969_, v___x_2976_);
lean_dec(v_i_2969_);
v_i_2969_ = v___x_2977_;
v_acc_2970_ = v___x_2975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2979_, lean_object* v_keys_2980_, lean_object* v_vals_2981_, lean_object* v_i_2982_, lean_object* v_acc_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2979_, v_keys_2980_, v_vals_2981_, v_i_2982_, v_acc_2983_);
lean_dec_ref(v_vals_2981_);
lean_dec_ref(v_keys_2980_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2985_, lean_object* v_x_2986_, lean_object* v_x_2987_){
_start:
{
if (lean_obj_tag(v_x_2986_) == 0)
{
lean_object* v_es_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; uint8_t v___x_2991_; 
v_es_2988_ = lean_ctor_get(v_x_2986_, 0);
v___x_2989_ = lean_unsigned_to_nat(0u);
v___x_2990_ = lean_array_get_size(v_es_2988_);
v___x_2991_ = lean_nat_dec_lt(v___x_2989_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_dec(v_f_2985_);
return v_x_2987_;
}
else
{
uint8_t v___x_2992_; 
v___x_2992_ = lean_nat_dec_le(v___x_2990_, v___x_2990_);
if (v___x_2992_ == 0)
{
if (v___x_2991_ == 0)
{
lean_dec(v_f_2985_);
return v_x_2987_;
}
else
{
size_t v___x_2993_; size_t v___x_2994_; lean_object* v___x_2995_; 
v___x_2993_ = ((size_t)0ULL);
v___x_2994_ = lean_usize_of_nat(v___x_2990_);
v___x_2995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2985_, v_es_2988_, v___x_2993_, v___x_2994_, v_x_2987_);
return v___x_2995_;
}
}
else
{
size_t v___x_2996_; size_t v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = ((size_t)0ULL);
v___x_2997_ = lean_usize_of_nat(v___x_2990_);
v___x_2998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2985_, v_es_2988_, v___x_2996_, v___x_2997_, v_x_2987_);
return v___x_2998_;
}
}
}
else
{
lean_object* v_ks_2999_; lean_object* v_vs_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_ks_2999_ = lean_ctor_get(v_x_2986_, 0);
v_vs_3000_ = lean_ctor_get(v_x_2986_, 1);
v___x_3001_ = lean_unsigned_to_nat(0u);
v___x_3002_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2985_, v_ks_2999_, v_vs_3000_, v___x_3001_, v_x_2987_);
return v___x_3002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3003_, lean_object* v_as_3004_, size_t v_i_3005_, size_t v_stop_3006_, lean_object* v_b_3007_){
_start:
{
lean_object* v___y_3009_; uint8_t v___x_3013_; 
v___x_3013_ = lean_usize_dec_eq(v_i_3005_, v_stop_3006_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_array_uget_borrowed(v_as_3004_, v_i_3005_);
switch(lean_obj_tag(v___x_3014_))
{
case 0:
{
lean_object* v_key_3015_; lean_object* v_val_3016_; lean_object* v___x_3017_; 
v_key_3015_ = lean_ctor_get(v___x_3014_, 0);
v_val_3016_ = lean_ctor_get(v___x_3014_, 1);
lean_inc(v_f_3003_);
lean_inc(v_val_3016_);
lean_inc(v_key_3015_);
v___x_3017_ = lean_apply_3(v_f_3003_, v_b_3007_, v_key_3015_, v_val_3016_);
v___y_3009_ = v___x_3017_;
goto v___jp_3008_;
}
case 1:
{
lean_object* v_node_3018_; lean_object* v___x_3019_; 
v_node_3018_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_f_3003_);
v___x_3019_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3003_, v_node_3018_, v_b_3007_);
v___y_3009_ = v___x_3019_;
goto v___jp_3008_;
}
default: 
{
v___y_3009_ = v_b_3007_;
goto v___jp_3008_;
}
}
}
else
{
lean_dec(v_f_3003_);
return v_b_3007_;
}
v___jp_3008_:
{
size_t v___x_3010_; size_t v___x_3011_; 
v___x_3010_ = ((size_t)1ULL);
v___x_3011_ = lean_usize_add(v_i_3005_, v___x_3010_);
v_i_3005_ = v___x_3011_;
v_b_3007_ = v___y_3009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3020_, lean_object* v_as_3021_, lean_object* v_i_3022_, lean_object* v_stop_3023_, lean_object* v_b_3024_){
_start:
{
size_t v_i_boxed_3025_; size_t v_stop_boxed_3026_; lean_object* v_res_3027_; 
v_i_boxed_3025_ = lean_unbox_usize(v_i_3022_);
lean_dec(v_i_3022_);
v_stop_boxed_3026_ = lean_unbox_usize(v_stop_3023_);
lean_dec(v_stop_3023_);
v_res_3027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3020_, v_as_3021_, v_i_boxed_3025_, v_stop_boxed_3026_, v_b_3024_);
lean_dec_ref(v_as_3021_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3028_, lean_object* v_x_3029_, lean_object* v_x_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3028_, v_x_3029_, v_x_3030_);
lean_dec_ref(v_x_3029_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object* v_f_3032_, lean_object* v_x1_3033_, lean_object* v_x2_3034_, lean_object* v_x3_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_apply_3(v_f_3032_, v_x1_3033_, v_x2_3034_, v_x3_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object* v_map_3037_, lean_object* v_f_3038_, lean_object* v_init_3039_){
_start:
{
lean_object* v___f_3040_; lean_object* v___x_3041_; 
v___f_3040_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3040_, 0, v_f_3038_);
v___x_3041_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v___f_3040_, v_map_3037_, v_init_3039_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object* v_map_3042_, lean_object* v_f_3043_, lean_object* v_init_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3042_, v_f_3043_, v_init_3044_);
lean_dec_ref(v_map_3042_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* v_env_3047_){
_start:
{
lean_object* v___x_3048_; lean_object* v_ext_3049_; lean_object* v_toEnvExtension_3050_; lean_object* v_asyncMode_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v_kinds_3054_; lean_object* v___f_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3048_ = l_Lean_Parser_parserExtension;
v_ext_3049_ = lean_ctor_get(v___x_3048_, 1);
v_toEnvExtension_3050_ = lean_ctor_get(v_ext_3049_, 0);
v_asyncMode_3051_ = lean_ctor_get(v_toEnvExtension_3050_, 2);
v___x_3052_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3053_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3052_, v___x_3048_, v_env_3047_, v_asyncMode_3051_);
v_kinds_3054_ = lean_ctor_get(v___x_3053_, 1);
lean_inc_ref(v_kinds_3054_);
lean_dec(v___x_3053_);
v___f_3055_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKinds___closed__0));
v___x_3056_ = lean_box(0);
v___x_3057_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_kinds_3054_, v___f_3055_, v___x_3056_);
lean_dec_ref(v_kinds_3054_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object* v_00_u03c3_3058_, lean_object* v_00_u03b2_3059_, lean_object* v_map_3060_, lean_object* v_f_3061_, lean_object* v_init_3062_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3060_, v_f_3061_, v_init_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object* v_00_u03c3_3064_, lean_object* v_00_u03b2_3065_, lean_object* v_map_3066_, lean_object* v_f_3067_, lean_object* v_init_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(v_00_u03c3_3064_, v_00_u03b2_3065_, v_map_3066_, v_f_3067_, v_init_3068_);
lean_dec_ref(v_map_3066_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object* v_map_3070_, lean_object* v_f_3071_, lean_object* v_init_3072_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3071_, v_map_3070_, v_init_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object* v_map_3074_, lean_object* v_f_3075_, lean_object* v_init_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(v_map_3074_, v_f_3075_, v_init_3076_);
lean_dec_ref(v_map_3074_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object* v_00_u03c3_3078_, lean_object* v_00_u03b2_3079_, lean_object* v_map_3080_, lean_object* v_f_3081_, lean_object* v_init_3082_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3081_, v_map_3080_, v_init_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3084_, lean_object* v_00_u03b2_3085_, lean_object* v_map_3086_, lean_object* v_f_3087_, lean_object* v_init_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(v_00_u03c3_3084_, v_00_u03b2_3085_, v_map_3086_, v_f_3087_, v_init_3088_);
lean_dec_ref(v_map_3086_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3090_, lean_object* v_00_u03b1_3091_, lean_object* v_00_u03b2_3092_, lean_object* v_f_3093_, lean_object* v_x_3094_, lean_object* v_x_3095_){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3093_, v_x_3094_, v_x_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3097_, lean_object* v_00_u03b1_3098_, lean_object* v_00_u03b2_3099_, lean_object* v_f_3100_, lean_object* v_x_3101_, lean_object* v_x_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(v_00_u03c3_3097_, v_00_u03b1_3098_, v_00_u03b2_3099_, v_f_3100_, v_x_3101_, v_x_3102_);
lean_dec_ref(v_x_3101_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3104_, lean_object* v_00_u03b2_3105_, lean_object* v_00_u03c3_3106_, lean_object* v_f_3107_, lean_object* v_as_3108_, size_t v_i_3109_, size_t v_stop_3110_, lean_object* v_b_3111_){
_start:
{
lean_object* v___x_3112_; 
v___x_3112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3107_, v_as_3108_, v_i_3109_, v_stop_3110_, v_b_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3113_, lean_object* v_00_u03b2_3114_, lean_object* v_00_u03c3_3115_, lean_object* v_f_3116_, lean_object* v_as_3117_, lean_object* v_i_3118_, lean_object* v_stop_3119_, lean_object* v_b_3120_){
_start:
{
size_t v_i_boxed_3121_; size_t v_stop_boxed_3122_; lean_object* v_res_3123_; 
v_i_boxed_3121_ = lean_unbox_usize(v_i_3118_);
lean_dec(v_i_3118_);
v_stop_boxed_3122_ = lean_unbox_usize(v_stop_3119_);
lean_dec(v_stop_3119_);
v_res_3123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3113_, v_00_u03b2_3114_, v_00_u03c3_3115_, v_f_3116_, v_as_3117_, v_i_boxed_3121_, v_stop_boxed_3122_, v_b_3120_);
lean_dec_ref(v_as_3117_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3124_, lean_object* v_00_u03b1_3125_, lean_object* v_00_u03b2_3126_, lean_object* v_f_3127_, lean_object* v_keys_3128_, lean_object* v_vals_3129_, lean_object* v_heq_3130_, lean_object* v_i_3131_, lean_object* v_acc_3132_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3127_, v_keys_3128_, v_vals_3129_, v_i_3131_, v_acc_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3134_, lean_object* v_00_u03b1_3135_, lean_object* v_00_u03b2_3136_, lean_object* v_f_3137_, lean_object* v_keys_3138_, lean_object* v_vals_3139_, lean_object* v_heq_3140_, lean_object* v_i_3141_, lean_object* v_acc_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3134_, v_00_u03b1_3135_, v_00_u03b2_3136_, v_f_3137_, v_keys_3138_, v_vals_3139_, v_heq_3140_, v_i_3141_, v_acc_3142_);
lean_dec_ref(v_vals_3139_);
lean_dec_ref(v_keys_3138_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* v_env_3144_){
_start:
{
lean_object* v___x_3145_; lean_object* v_ext_3146_; lean_object* v_toEnvExtension_3147_; lean_object* v_asyncMode_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v_tokens_3151_; 
v___x_3145_ = l_Lean_Parser_parserExtension;
v_ext_3146_ = lean_ctor_get(v___x_3145_, 1);
v_toEnvExtension_3147_ = lean_ctor_get(v_ext_3146_, 0);
v_asyncMode_3148_ = lean_ctor_get(v_toEnvExtension_3147_, 2);
v___x_3149_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3150_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3149_, v___x_3145_, v_env_3144_, v_asyncMode_3148_);
v_tokens_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc_ref(v_tokens_3151_);
lean_dec(v___x_3150_);
return v_tokens_3151_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__8));
v___x_3177_ = l_Lean_mkAtom(v___x_3176_);
return v___x_3177_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__10, &l_Lean_Parser_mkInputContext___auto__1___closed__10_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__10);
v___x_3179_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3180_ = lean_array_push(v___x_3179_, v___x_3178_);
return v___x_3180_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3192_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3193_ = lean_array_push(v___x_3192_, v___x_3191_);
return v___x_3193_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3194_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__15, &l_Lean_Parser_mkInputContext___auto__1___closed__15_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__15);
v___x_3195_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__13));
v___x_3196_ = lean_box(2);
v___x_3197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
lean_ctor_set(v___x_3197_, 1, v___x_3195_);
lean_ctor_set(v___x_3197_, 2, v___x_3194_);
return v___x_3197_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3198_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__16, &l_Lean_Parser_mkInputContext___auto__1___closed__16_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__16);
v___x_3199_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__11, &l_Lean_Parser_mkInputContext___auto__1___closed__11_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__11);
v___x_3200_ = lean_array_push(v___x_3199_, v___x_3198_);
return v___x_3200_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3201_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3202_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__17, &l_Lean_Parser_mkInputContext___auto__1___closed__17_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__17);
v___x_3203_ = lean_array_push(v___x_3202_, v___x_3201_);
return v___x_3203_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3204_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3205_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__18, &l_Lean_Parser_mkInputContext___auto__1___closed__18_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__18);
v___x_3206_ = lean_array_push(v___x_3205_, v___x_3204_);
return v___x_3206_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3208_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__19, &l_Lean_Parser_mkInputContext___auto__1___closed__19_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__19);
v___x_3209_ = lean_array_push(v___x_3208_, v___x_3207_);
return v___x_3209_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3211_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__20, &l_Lean_Parser_mkInputContext___auto__1___closed__20_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__20);
v___x_3212_ = lean_array_push(v___x_3211_, v___x_3210_);
return v___x_3212_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3213_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__21, &l_Lean_Parser_mkInputContext___auto__1___closed__21_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__21);
v___x_3214_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__9));
v___x_3215_ = lean_box(2);
v___x_3216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set(v___x_3216_, 1, v___x_3214_);
lean_ctor_set(v___x_3216_, 2, v___x_3213_);
return v___x_3216_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3217_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__22, &l_Lean_Parser_mkInputContext___auto__1___closed__22_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__22);
v___x_3218_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3219_ = lean_array_push(v___x_3218_, v___x_3217_);
return v___x_3219_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3220_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__23, &l_Lean_Parser_mkInputContext___auto__1___closed__23_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__23);
v___x_3221_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3222_ = lean_box(2);
v___x_3223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
lean_ctor_set(v___x_3223_, 1, v___x_3221_);
lean_ctor_set(v___x_3223_, 2, v___x_3220_);
return v___x_3223_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__24, &l_Lean_Parser_mkInputContext___auto__1___closed__24_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__24);
v___x_3225_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3226_ = lean_array_push(v___x_3225_, v___x_3224_);
return v___x_3226_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3227_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__25, &l_Lean_Parser_mkInputContext___auto__1___closed__25_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__25);
v___x_3228_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3229_ = lean_box(2);
v___x_3230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
lean_ctor_set(v___x_3230_, 1, v___x_3228_);
lean_ctor_set(v___x_3230_, 2, v___x_3227_);
return v___x_3230_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3231_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__26, &l_Lean_Parser_mkInputContext___auto__1___closed__26_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__26);
v___x_3232_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3233_ = lean_array_push(v___x_3232_, v___x_3231_);
return v___x_3233_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3234_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__27, &l_Lean_Parser_mkInputContext___auto__1___closed__27_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__27);
v___x_3235_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3236_ = lean_box(2);
v___x_3237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
lean_ctor_set(v___x_3237_, 1, v___x_3235_);
lean_ctor_set(v___x_3237_, 2, v___x_3234_);
return v___x_3237_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1(void){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__28, &l_Lean_Parser_mkInputContext___auto__1___closed__28_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__28);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object* v_input_3239_, lean_object* v_fileName_3240_, uint8_t v_normalizeLineEndings_3241_, lean_object* v_endPos_3242_){
_start:
{
lean_object* v_fst_3244_; lean_object* v_snd_3245_; lean_object* v_text_3251_; 
v_text_3251_ = l_Lean_FileMap_ofString(v_input_3239_);
if (v_normalizeLineEndings_3241_ == 0)
{
v_fst_3244_ = v_text_3251_;
v_snd_3245_ = v_endPos_3242_;
goto v___jp_3243_;
}
else
{
lean_object* v_source_3252_; lean_object* v_endPos_x27_3253_; lean_object* v___x_3254_; lean_object* v_text_3255_; lean_object* v___x_3256_; 
v_source_3252_ = lean_ctor_get(v_text_3251_, 0);
lean_inc_ref(v_source_3252_);
v_endPos_x27_3253_ = l_Lean_FileMap_toPosition(v_text_3251_, v_endPos_3242_);
lean_dec(v_endPos_3242_);
v___x_3254_ = l_String_crlfToLf(v_source_3252_);
lean_dec_ref(v_source_3252_);
v_text_3255_ = l_Lean_FileMap_ofString(v___x_3254_);
v___x_3256_ = l_Lean_FileMap_ofPosition(v_text_3255_, v_endPos_x27_3253_);
v_fst_3244_ = v_text_3255_;
v_snd_3245_ = v___x_3256_;
goto v___jp_3243_;
}
v___jp_3243_:
{
lean_object* v_source_3246_; lean_object* v___x_3247_; uint8_t v___x_3248_; 
v_source_3246_ = lean_ctor_get(v_fst_3244_, 0);
lean_inc_ref(v_source_3246_);
v___x_3247_ = lean_string_utf8_byte_size(v_source_3246_);
v___x_3248_ = lean_nat_dec_le(v_snd_3245_, v___x_3247_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; 
lean_dec(v_snd_3245_);
v___x_3249_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3249_, 0, v_source_3246_);
lean_ctor_set(v___x_3249_, 1, v_fileName_3240_);
lean_ctor_set(v___x_3249_, 2, v_fst_3244_);
lean_ctor_set(v___x_3249_, 3, v___x_3247_);
return v___x_3249_;
}
else
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3250_, 0, v_source_3246_);
lean_ctor_set(v___x_3250_, 1, v_fileName_3240_);
lean_ctor_set(v___x_3250_, 2, v_fst_3244_);
lean_ctor_set(v___x_3250_, 3, v_snd_3245_);
return v___x_3250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object* v_input_3257_, lean_object* v_fileName_3258_, lean_object* v_normalizeLineEndings_3259_, lean_object* v_endPos_3260_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3261_; lean_object* v_res_3262_; 
v_normalizeLineEndings_boxed_3261_ = lean_unbox(v_normalizeLineEndings_3259_);
v_res_3262_ = l_Lean_Parser_mkInputContext___redArg(v_input_3257_, v_fileName_3258_, v_normalizeLineEndings_boxed_3261_, v_endPos_3260_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object* v_input_3263_, lean_object* v_fileName_3264_, uint8_t v_normalizeLineEndings_3265_, lean_object* v_endPos_3266_, lean_object* v_endPos__valid_3267_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Lean_Parser_mkInputContext___redArg(v_input_3263_, v_fileName_3264_, v_normalizeLineEndings_3265_, v_endPos_3266_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object* v_input_3269_, lean_object* v_fileName_3270_, lean_object* v_normalizeLineEndings_3271_, lean_object* v_endPos_3272_, lean_object* v_endPos__valid_3273_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3274_; lean_object* v_res_3275_; 
v_normalizeLineEndings_boxed_3274_ = lean_unbox(v_normalizeLineEndings_3271_);
v_res_3275_ = l_Lean_Parser_mkInputContext(v_input_3269_, v_fileName_3270_, v_normalizeLineEndings_boxed_3274_, v_endPos_3272_, v_endPos__valid_3273_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* v_input_3278_){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3279_ = l_Lean_Parser_SyntaxStack_empty;
v___x_3280_ = lean_unsigned_to_nat(0u);
v___x_3281_ = l_Lean_Parser_initCacheForInput(v_input_3278_);
v___x_3282_ = lean_box(0);
v___x_3283_ = ((lean_object*)(l_Lean_Parser_mkParserState___closed__0));
v___x_3284_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3279_);
lean_ctor_set(v___x_3284_, 1, v___x_3280_);
lean_ctor_set(v___x_3284_, 2, v___x_3280_);
lean_ctor_set(v___x_3284_, 3, v___x_3281_);
lean_ctor_set(v___x_3284_, 4, v___x_3282_);
lean_ctor_set(v___x_3284_, 5, v___x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* v_input_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_Parser_mkParserState(v_input_3285_);
lean_dec_ref(v_input_3285_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* v_env_3289_, lean_object* v_catName_3290_, lean_object* v_input_3291_, lean_object* v_fileName_3292_){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v_p_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; lean_object* v_ictx_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v_s_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; uint8_t v___x_3309_; 
v___x_3293_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__0));
v___x_3294_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 1);
lean_closure_set(v___x_3294_, 0, v_catName_3290_);
v_p_3295_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_3295_, 0, v___x_3293_);
lean_closure_set(v_p_3295_, 1, v___x_3294_);
v___x_3296_ = 1;
v___x_3297_ = lean_string_utf8_byte_size(v_input_3291_);
lean_inc_ref(v_input_3291_);
v_ictx_3298_ = l_Lean_Parser_mkInputContext___redArg(v_input_3291_, v_fileName_3292_, v___x_3296_, v___x_3297_);
v___x_3299_ = l_Lean_Options_empty;
v___x_3300_ = lean_box(0);
v___x_3301_ = lean_box(0);
lean_inc_ref(v_env_3289_);
v___x_3302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3302_, 0, v_env_3289_);
lean_ctor_set(v___x_3302_, 1, v___x_3299_);
lean_ctor_set(v___x_3302_, 2, v___x_3300_);
lean_ctor_set(v___x_3302_, 3, v___x_3301_);
v___x_3303_ = l_Lean_Parser_getTokenTable(v_env_3289_);
v___x_3304_ = l_Lean_Parser_mkParserState(v_input_3291_);
lean_dec_ref(v_input_3291_);
lean_inc_ref(v_ictx_3298_);
v_s_3305_ = l_Lean_Parser_ParserFn_run(v_p_3295_, v_ictx_3298_, v___x_3302_, v___x_3303_, v___x_3304_);
lean_inc_ref(v_s_3305_);
v___x_3306_ = l_Lean_Parser_ParserState_allErrors(v_s_3305_);
v___x_3307_ = lean_array_get_size(v___x_3306_);
lean_dec_ref(v___x_3306_);
v___x_3308_ = lean_unsigned_to_nat(0u);
v___x_3309_ = lean_nat_dec_eq(v___x_3307_, v___x_3308_);
if (v___x_3309_ == 0)
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3298_, v_s_3305_);
v___x_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
return v___x_3311_;
}
else
{
lean_object* v_stxStack_3312_; lean_object* v_pos_3313_; uint8_t v___x_3314_; 
v_stxStack_3312_ = lean_ctor_get(v_s_3305_, 0);
lean_inc_ref(v_stxStack_3312_);
v_pos_3313_ = lean_ctor_get(v_s_3305_, 2);
lean_inc(v_pos_3313_);
v___x_3314_ = l_Lean_Parser_InputContext_atEnd(v_ictx_3298_, v_pos_3313_);
lean_dec(v_pos_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_dec_ref(v_stxStack_3312_);
v___x_3315_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__1));
v___x_3316_ = l_Lean_Parser_ParserState_mkError(v_s_3305_, v___x_3315_);
v___x_3317_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3298_, v___x_3316_);
v___x_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
return v___x_3318_;
}
else
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
lean_dec_ref(v_s_3305_);
lean_dec_ref(v_ictx_3298_);
v___x_3319_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3312_);
lean_dec_ref(v_stxStack_3312_);
v___x_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
return v___x_3320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* v_addFnName_3321_, lean_object* v_catName_3322_, lean_object* v_declName_3323_, lean_object* v_prio_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v_val_3340_; lean_object* v___x_3341_; 
v___x_3328_ = lean_box(0);
v___x_3329_ = l_Lean_mkConst(v_addFnName_3321_, v___x_3328_);
v___x_3330_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_catName_3322_);
lean_inc_n(v_declName_3323_, 2);
v___x_3331_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3323_);
v___x_3332_ = l_Lean_mkConst(v_declName_3323_, v___x_3328_);
v___x_3333_ = l_Lean_mkRawNatLit(v_prio_3324_);
v___x_3334_ = lean_unsigned_to_nat(4u);
v___x_3335_ = lean_mk_empty_array_with_capacity(v___x_3334_);
v___x_3336_ = lean_array_push(v___x_3335_, v___x_3330_);
v___x_3337_ = lean_array_push(v___x_3336_, v___x_3331_);
v___x_3338_ = lean_array_push(v___x_3337_, v___x_3332_);
v___x_3339_ = lean_array_push(v___x_3338_, v___x_3333_);
v_val_3340_ = l_Lean_mkAppN(v___x_3329_, v___x_3339_);
lean_dec_ref(v___x_3339_);
v___x_3341_ = l_Lean_declareBuiltin(v_declName_3323_, v_val_3340_, v_a_3325_, v_a_3326_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object* v_addFnName_3342_, lean_object* v_catName_3343_, lean_object* v_declName_3344_, lean_object* v_prio_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3342_, v_catName_3343_, v_declName_3344_, v_prio_3345_, v_a_3346_, v_a_3347_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* v_catName_3355_, lean_object* v_declName_3356_, lean_object* v_prio_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = ((lean_object*)(l_Lean_Parser_declareLeadingBuiltinParser___closed__1));
v___x_3362_ = l_Lean_Parser_declareBuiltinParser(v___x_3361_, v_catName_3355_, v_declName_3356_, v_prio_3357_, v_a_3358_, v_a_3359_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object* v_catName_3363_, lean_object* v_declName_3364_, lean_object* v_prio_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3363_, v_declName_3364_, v_prio_3365_, v_a_3366_, v_a_3367_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* v_catName_3375_, lean_object* v_declName_3376_, lean_object* v_prio_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = ((lean_object*)(l_Lean_Parser_declareTrailingBuiltinParser___closed__1));
v___x_3382_ = l_Lean_Parser_declareBuiltinParser(v___x_3381_, v_catName_3375_, v_declName_3376_, v_prio_3377_, v_a_3378_, v_a_3379_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object* v_catName_3383_, lean_object* v_declName_3384_, lean_object* v_prio_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3383_, v_declName_3384_, v_prio_3385_, v_a_3386_, v_a_3387_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* v_args_3396_){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v___x_3397_ = l_Lean_Syntax_getNumArgs(v_args_3396_);
v___x_3398_ = lean_unsigned_to_nat(0u);
v___x_3399_ = lean_nat_dec_eq(v___x_3397_, v___x_3398_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; uint8_t v___x_3401_; 
v___x_3400_ = lean_unsigned_to_nat(1u);
v___x_3401_ = lean_nat_dec_eq(v___x_3397_, v___x_3400_);
lean_dec(v___x_3397_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; 
v___x_3402_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__1));
return v___x_3402_;
}
else
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = l_Lean_Syntax_getArg(v_args_3396_, v___x_3398_);
v___x_3404_ = l_Lean_Syntax_isNatLit_x3f(v___x_3403_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3405_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__2));
v___x_3406_ = l_Lean_Syntax_formatStx(v___x_3403_, v___x_3404_, v___x_3399_);
v___x_3407_ = l_Std_Format_defWidth;
v___x_3408_ = l_Std_Format_pretty(v___x_3406_, v___x_3407_, v___x_3398_, v___x_3398_);
v___x_3409_ = lean_string_append(v___x_3405_, v___x_3408_);
lean_dec_ref(v___x_3408_);
v___x_3410_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3411_ = lean_string_append(v___x_3409_, v___x_3410_);
v___x_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
return v___x_3412_;
}
else
{
lean_object* v_val_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v___x_3403_);
v_val_3413_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3404_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_val_3413_);
lean_dec(v___x_3404_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_val_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
else
{
lean_object* v___x_3421_; 
lean_dec(v___x_3397_);
v___x_3421_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__3));
return v___x_3421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* v_args_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_Parser_getParserPriority(v_args_3422_);
lean_dec(v_args_3422_);
return v_res_3423_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0));
v___x_3426_ = l_Lean_stringToMessageData(v___x_3425_);
return v___x_3426_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2));
v___x_3429_ = l_Lean_stringToMessageData(v___x_3428_);
return v___x_3429_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object* v_name_3435_, uint8_t v_kind_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___y_3446_; 
v___x_3440_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1);
v___x_3441_ = l_Lean_MessageData_ofName(v_name_3435_);
v___x_3442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3440_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
v___x_3443_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3);
v___x_3444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3442_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
switch(v_kind_3436_)
{
case 0:
{
lean_object* v___x_3453_; 
v___x_3453_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5));
v___y_3446_ = v___x_3453_;
goto v___jp_3445_;
}
case 1:
{
lean_object* v___x_3454_; 
v___x_3454_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6));
v___y_3446_ = v___x_3454_;
goto v___jp_3445_;
}
default: 
{
lean_object* v___x_3455_; 
v___x_3455_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7));
v___y_3446_ = v___x_3455_;
goto v___jp_3445_;
}
}
v___jp_3445_:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
lean_inc_ref(v___y_3446_);
v___x_3447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3447_, 0, v___y_3446_);
v___x_3448_ = l_Lean_MessageData_ofFormat(v___x_3447_);
v___x_3449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3444_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3449_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v___x_3452_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3451_, v___y_3437_, v___y_3438_);
return v___x_3452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object* v_name_3456_, lean_object* v_kind_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
uint8_t v_kind_boxed_3461_; lean_object* v_res_3462_; 
v_kind_boxed_3461_ = lean_unbox(v_kind_3457_);
v_res_3462_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3456_, v_kind_boxed_3461_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3463_, lean_object* v_msg_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_fileName_3468_; lean_object* v_fileMap_3469_; lean_object* v_options_3470_; lean_object* v_currRecDepth_3471_; lean_object* v_maxRecDepth_3472_; lean_object* v_ref_3473_; lean_object* v_currNamespace_3474_; lean_object* v_openDecls_3475_; lean_object* v_initHeartbeats_3476_; lean_object* v_maxHeartbeats_3477_; lean_object* v_quotContext_3478_; lean_object* v_currMacroScope_3479_; uint8_t v_diag_3480_; lean_object* v_cancelTk_x3f_3481_; uint8_t v_suppressElabErrors_3482_; lean_object* v_inheritedTraceOptions_3483_; lean_object* v_ref_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_fileName_3468_ = lean_ctor_get(v___y_3465_, 0);
v_fileMap_3469_ = lean_ctor_get(v___y_3465_, 1);
v_options_3470_ = lean_ctor_get(v___y_3465_, 2);
v_currRecDepth_3471_ = lean_ctor_get(v___y_3465_, 3);
v_maxRecDepth_3472_ = lean_ctor_get(v___y_3465_, 4);
v_ref_3473_ = lean_ctor_get(v___y_3465_, 5);
v_currNamespace_3474_ = lean_ctor_get(v___y_3465_, 6);
v_openDecls_3475_ = lean_ctor_get(v___y_3465_, 7);
v_initHeartbeats_3476_ = lean_ctor_get(v___y_3465_, 8);
v_maxHeartbeats_3477_ = lean_ctor_get(v___y_3465_, 9);
v_quotContext_3478_ = lean_ctor_get(v___y_3465_, 10);
v_currMacroScope_3479_ = lean_ctor_get(v___y_3465_, 11);
v_diag_3480_ = lean_ctor_get_uint8(v___y_3465_, sizeof(void*)*14);
v_cancelTk_x3f_3481_ = lean_ctor_get(v___y_3465_, 12);
v_suppressElabErrors_3482_ = lean_ctor_get_uint8(v___y_3465_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3483_ = lean_ctor_get(v___y_3465_, 13);
v_ref_3484_ = l_Lean_replaceRef(v_ref_3463_, v_ref_3473_);
lean_inc_ref(v_inheritedTraceOptions_3483_);
lean_inc(v_cancelTk_x3f_3481_);
lean_inc(v_currMacroScope_3479_);
lean_inc(v_quotContext_3478_);
lean_inc(v_maxHeartbeats_3477_);
lean_inc(v_initHeartbeats_3476_);
lean_inc(v_openDecls_3475_);
lean_inc(v_currNamespace_3474_);
lean_inc(v_maxRecDepth_3472_);
lean_inc(v_currRecDepth_3471_);
lean_inc_ref(v_options_3470_);
lean_inc_ref(v_fileMap_3469_);
lean_inc_ref(v_fileName_3468_);
v___x_3485_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3485_, 0, v_fileName_3468_);
lean_ctor_set(v___x_3485_, 1, v_fileMap_3469_);
lean_ctor_set(v___x_3485_, 2, v_options_3470_);
lean_ctor_set(v___x_3485_, 3, v_currRecDepth_3471_);
lean_ctor_set(v___x_3485_, 4, v_maxRecDepth_3472_);
lean_ctor_set(v___x_3485_, 5, v_ref_3484_);
lean_ctor_set(v___x_3485_, 6, v_currNamespace_3474_);
lean_ctor_set(v___x_3485_, 7, v_openDecls_3475_);
lean_ctor_set(v___x_3485_, 8, v_initHeartbeats_3476_);
lean_ctor_set(v___x_3485_, 9, v_maxHeartbeats_3477_);
lean_ctor_set(v___x_3485_, 10, v_quotContext_3478_);
lean_ctor_set(v___x_3485_, 11, v_currMacroScope_3479_);
lean_ctor_set(v___x_3485_, 12, v_cancelTk_x3f_3481_);
lean_ctor_set(v___x_3485_, 13, v_inheritedTraceOptions_3483_);
lean_ctor_set_uint8(v___x_3485_, sizeof(void*)*14, v_diag_3480_);
lean_ctor_set_uint8(v___x_3485_, sizeof(void*)*14 + 1, v_suppressElabErrors_3482_);
v___x_3486_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_3464_, v___x_3485_, v___y_3466_);
lean_dec_ref_known(v___x_3485_, 14);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3487_, lean_object* v_msg_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3487_, v_msg_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v_ref_3487_);
return v_res_3492_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_3495_ = l_Lean_stringToMessageData(v___x_3494_);
return v___x_3495_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_3498_ = l_Lean_stringToMessageData(v___x_3497_);
return v___x_3498_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_3501_ = l_Lean_stringToMessageData(v___x_3500_);
return v___x_3501_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_3504_ = l_Lean_stringToMessageData(v___x_3503_);
return v___x_3504_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_3507_ = l_Lean_stringToMessageData(v___x_3506_);
return v___x_3507_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_3510_ = l_Lean_stringToMessageData(v___x_3509_);
return v___x_3510_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_3513_ = l_Lean_stringToMessageData(v___x_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_3514_, lean_object* v_declHint_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___x_3518_; lean_object* v_env_3519_; uint8_t v___x_3520_; 
v___x_3518_ = lean_st_ref_get(v___y_3516_);
v_env_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc_ref(v_env_3519_);
lean_dec(v___x_3518_);
v___x_3520_ = l_Lean_Name_isAnonymous(v_declHint_3515_);
if (v___x_3520_ == 0)
{
uint8_t v_isExporting_3521_; 
v_isExporting_3521_ = lean_ctor_get_uint8(v_env_3519_, sizeof(void*)*8);
if (v_isExporting_3521_ == 0)
{
lean_object* v___x_3522_; 
lean_dec_ref(v_env_3519_);
lean_dec(v_declHint_3515_);
v___x_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3522_, 0, v_msg_3514_);
return v___x_3522_;
}
else
{
lean_object* v___x_3523_; uint8_t v___x_3524_; 
lean_inc_ref(v_env_3519_);
v___x_3523_ = l_Lean_Environment_setExporting(v_env_3519_, v___x_3520_);
lean_inc(v_declHint_3515_);
lean_inc_ref(v___x_3523_);
v___x_3524_ = l_Lean_Environment_contains(v___x_3523_, v_declHint_3515_, v_isExporting_3521_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; 
lean_dec_ref(v___x_3523_);
lean_dec_ref(v_env_3519_);
lean_dec(v_declHint_3515_);
v___x_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3525_, 0, v_msg_3514_);
return v___x_3525_;
}
else
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v_c_3531_; lean_object* v___x_3532_; 
v___x_3526_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_3527_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_3528_ = l_Lean_Options_empty;
v___x_3529_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3523_);
lean_ctor_set(v___x_3529_, 1, v___x_3526_);
lean_ctor_set(v___x_3529_, 2, v___x_3527_);
lean_ctor_set(v___x_3529_, 3, v___x_3528_);
lean_inc(v_declHint_3515_);
v___x_3530_ = l_Lean_MessageData_ofConstName(v_declHint_3515_, v___x_3520_);
v_c_3531_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3531_, 0, v___x_3529_);
lean_ctor_set(v_c_3531_, 1, v___x_3530_);
v___x_3532_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3519_, v_declHint_3515_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
lean_dec_ref(v_env_3519_);
lean_dec(v_declHint_3515_);
v___x_3533_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
lean_ctor_set(v___x_3534_, 1, v_c_3531_);
v___x_3535_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_3536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3534_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v___x_3537_ = l_Lean_MessageData_note(v___x_3536_);
v___x_3538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3538_, 0, v_msg_3514_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
return v___x_3539_;
}
else
{
lean_object* v_val_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3575_; 
v_val_3540_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3542_ = v___x_3532_;
v_isShared_3543_ = v_isSharedCheck_3575_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_val_3540_);
lean_dec(v___x_3532_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3575_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v_mod_3547_; uint8_t v___x_3548_; 
v___x_3544_ = lean_box(0);
v___x_3545_ = l_Lean_Environment_header(v_env_3519_);
lean_dec_ref(v_env_3519_);
v___x_3546_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3545_);
v_mod_3547_ = lean_array_get(v___x_3544_, v___x_3546_, v_val_3540_);
lean_dec(v_val_3540_);
lean_dec_ref(v___x_3546_);
v___x_3548_ = l_Lean_isPrivateName(v_declHint_3515_);
lean_dec(v_declHint_3515_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3549_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_3550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
lean_ctor_set(v___x_3550_, 1, v_c_3531_);
v___x_3551_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_3552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3550_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = l_Lean_MessageData_ofName(v_mod_3547_);
v___x_3554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3552_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
v___x_3555_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_3556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3554_);
lean_ctor_set(v___x_3556_, 1, v___x_3555_);
v___x_3557_ = l_Lean_MessageData_note(v___x_3556_);
v___x_3558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3558_, 0, v_msg_3514_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set_tag(v___x_3542_, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3558_);
v___x_3560_ = v___x_3542_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3558_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3573_; 
v___x_3562_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
lean_ctor_set(v___x_3563_, 1, v_c_3531_);
v___x_3564_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_3565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3563_);
lean_ctor_set(v___x_3565_, 1, v___x_3564_);
v___x_3566_ = l_Lean_MessageData_ofName(v_mod_3547_);
v___x_3567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3565_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_3569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3567_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = l_Lean_MessageData_note(v___x_3569_);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v_msg_3514_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set_tag(v___x_3542_, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3571_);
v___x_3573_ = v___x_3542_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3576_; 
lean_dec_ref(v_env_3519_);
lean_dec(v_declHint_3515_);
v___x_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3576_, 0, v_msg_3514_);
return v___x_3576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_3577_, lean_object* v_declHint_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3577_, v_declHint_3578_, v___y_3579_);
lean_dec(v___y_3579_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_3582_, lean_object* v_declHint_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___x_3587_; lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3597_; 
v___x_3587_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3582_, v_declHint_3583_, v___y_3585_);
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3590_ = v___x_3587_;
v_isShared_3591_ = v_isSharedCheck_3597_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3587_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3597_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3592_ = l_Lean_unknownIdentifierMessageTag;
v___x_3593_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
lean_ctor_set(v___x_3593_, 1, v_a_3588_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v___x_3593_);
v___x_3595_ = v___x_3590_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3593_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_3598_, lean_object* v_declHint_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3598_, v_declHint_3599_, v___y_3600_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3604_, lean_object* v_msg_3605_, lean_object* v_declHint_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v___x_3610_; lean_object* v_a_3611_; lean_object* v___x_3612_; 
v___x_3610_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3605_, v_declHint_3606_, v___y_3607_, v___y_3608_);
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref(v___x_3610_);
v___x_3612_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3604_, v_a_3611_, v___y_3607_, v___y_3608_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3613_, lean_object* v_msg_3614_, lean_object* v_declHint_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3613_, v_msg_3614_, v_declHint_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v_ref_3613_);
return v_res_3619_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_3621_ = l_Lean_stringToMessageData(v___x_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3622_, lean_object* v_constName_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v___x_3627_; uint8_t v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3627_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3628_ = 0;
lean_inc(v_constName_3623_);
v___x_3629_ = l_Lean_MessageData_ofConstName(v_constName_3623_, v___x_3628_);
v___x_3630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3627_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3630_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3622_, v___x_3632_, v_constName_3623_, v___y_3624_, v___y_3625_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3634_, lean_object* v_constName_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3634_, v_constName_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v_ref_3634_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object* v_constName_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v_ref_3644_; lean_object* v___x_3645_; 
v_ref_3644_ = lean_ctor_get(v___y_3641_, 5);
v___x_3645_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3644_, v_constName_3640_, v___y_3641_, v___y_3642_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object* v_constName_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v___x_3655_; lean_object* v_env_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; 
v___x_3655_ = lean_st_ref_get(v___y_3653_);
v_env_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc_ref(v_env_3656_);
lean_dec(v___x_3655_);
v___x_3657_ = 0;
lean_inc(v_constName_3651_);
v___x_3658_ = l_Lean_Environment_find_x3f(v_env_3656_, v_constName_3651_, v___x_3657_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3651_, v___y_3652_, v___y_3653_);
return v___x_3659_;
}
else
{
lean_object* v_val_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec(v_constName_3651_);
v_val_3660_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3658_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_val_3660_);
lean_dec(v___x_3658_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set_tag(v___x_3662_, 0);
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_val_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object* v_constName_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
return v_res_3672_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0));
v___x_3675_ = l_Lean_stringToMessageData(v___x_3674_);
return v___x_3675_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3(void){
_start:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3677_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2));
v___x_3678_ = l_Lean_stringToMessageData(v___x_3677_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* v_attrName_3679_, lean_object* v_catName_3680_, lean_object* v_declName_3681_, lean_object* v_stx_3682_, uint8_t v_kind_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_Attribute_Builtin_getPrio(v_stx_3682_, v_a_3684_, v_a_3685_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___y_3710_; lean_object* v___y_3711_; uint8_t v___x_3739_; uint8_t v___x_3740_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___x_3707_, 1);
v___x_3739_ = 0;
v___x_3740_ = l_Lean_instBEqAttributeKind_beq(v_kind_3683_, v___x_3739_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_dec(v_a_3708_);
lean_dec(v_declName_3681_);
lean_dec(v_catName_3680_);
v___x_3741_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_attrName_3679_, v_kind_3683_, v_a_3684_, v_a_3685_);
return v___x_3741_;
}
else
{
lean_dec(v_attrName_3679_);
v___y_3710_ = v_a_3684_;
v___y_3711_ = v_a_3685_;
goto v___jp_3709_;
}
v___jp_3709_:
{
lean_object* v___x_3712_; 
lean_inc(v_declName_3681_);
v___x_3712_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_declName_3681_, v___y_3710_, v___y_3711_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3714_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3712_, 1);
v___x_3714_ = l_Lean_ConstantInfo_type(v_a_3713_);
if (lean_obj_tag(v___x_3714_) == 4)
{
lean_object* v_declName_3715_; 
v_declName_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc(v_declName_3715_);
lean_dec_ref_known(v___x_3714_, 2);
if (lean_obj_tag(v_declName_3715_) == 1)
{
lean_object* v_pre_3716_; 
v_pre_3716_ = lean_ctor_get(v_declName_3715_, 0);
lean_inc(v_pre_3716_);
if (lean_obj_tag(v_pre_3716_) == 1)
{
lean_object* v_pre_3717_; 
v_pre_3717_ = lean_ctor_get(v_pre_3716_, 0);
lean_inc(v_pre_3717_);
if (lean_obj_tag(v_pre_3717_) == 1)
{
lean_object* v_pre_3718_; 
v_pre_3718_ = lean_ctor_get(v_pre_3717_, 0);
if (lean_obj_tag(v_pre_3718_) == 0)
{
lean_object* v_str_3719_; lean_object* v_str_3720_; lean_object* v_str_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v_str_3719_ = lean_ctor_get(v_declName_3715_, 1);
lean_inc_ref(v_str_3719_);
lean_dec_ref_known(v_declName_3715_, 2);
v_str_3720_ = lean_ctor_get(v_pre_3716_, 1);
lean_inc_ref(v_str_3720_);
lean_dec_ref_known(v_pre_3716_, 2);
v_str_3721_ = lean_ctor_get(v_pre_3717_, 1);
lean_inc_ref(v_str_3721_);
lean_dec_ref_known(v_pre_3717_, 2);
v___x_3722_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3723_ = lean_string_dec_eq(v_str_3721_, v___x_3722_);
lean_dec_ref(v_str_3721_);
if (v___x_3723_ == 0)
{
lean_dec_ref(v_str_3720_);
lean_dec_ref(v_str_3719_);
lean_dec(v_a_3708_);
lean_dec(v_catName_3680_);
v___y_3694_ = v_a_3713_;
v___y_3695_ = v___y_3710_;
v___y_3696_ = v___y_3711_;
goto v___jp_3693_;
}
else
{
lean_object* v___x_3724_; uint8_t v___x_3725_; 
v___x_3724_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3725_ = lean_string_dec_eq(v_str_3720_, v___x_3724_);
lean_dec_ref(v_str_3720_);
if (v___x_3725_ == 0)
{
lean_dec_ref(v_str_3719_);
lean_dec(v_a_3708_);
lean_dec(v_catName_3680_);
v___y_3694_ = v_a_3713_;
v___y_3695_ = v___y_3710_;
v___y_3696_ = v___y_3711_;
goto v___jp_3693_;
}
else
{
lean_object* v___x_3726_; uint8_t v___x_3727_; 
v___x_3726_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_3727_ = lean_string_dec_eq(v_str_3719_, v___x_3726_);
if (v___x_3727_ == 0)
{
uint8_t v___x_3728_; 
v___x_3728_ = lean_string_dec_eq(v_str_3719_, v___x_3724_);
lean_dec_ref(v_str_3719_);
if (v___x_3728_ == 0)
{
lean_dec(v_a_3708_);
lean_dec(v_catName_3680_);
v___y_3694_ = v_a_3713_;
v___y_3695_ = v___y_3710_;
v___y_3696_ = v___y_3711_;
goto v___jp_3693_;
}
else
{
lean_object* v___x_3729_; 
lean_dec(v_a_3713_);
lean_inc(v_declName_3681_);
lean_inc(v_catName_3680_);
v___x_3729_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3680_, v_declName_3681_, v_a_3708_, v___y_3710_, v___y_3711_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_dec_ref_known(v___x_3729_, 1);
v___y_3688_ = v___y_3710_;
v___y_3689_ = v___y_3711_;
goto v___jp_3687_;
}
else
{
lean_dec(v_declName_3681_);
lean_dec(v_catName_3680_);
return v___x_3729_;
}
}
}
else
{
lean_object* v___x_3730_; 
lean_dec_ref(v_str_3719_);
lean_dec(v_a_3713_);
lean_inc(v_declName_3681_);
lean_inc(v_catName_3680_);
v___x_3730_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3680_, v_declName_3681_, v_a_3708_, v___y_3710_, v___y_3711_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_dec_ref_known(v___x_3730_, 1);
v___y_3688_ = v___y_3710_;
v___y_3689_ = v___y_3711_;
goto v___jp_3687_;
}
else
{
lean_dec(v_declName_3681_);
lean_dec(v_catName_3680_);
return v___x_3730_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3717_, 2);
lean_dec_ref_known(v_pre_3716_, 2);
lean_dec_ref_known(v_declName_3715_, 2);
lean_dec(v_a_3708_);
lean_dec(v_catName_3680_);
v___y_3694_ = v_a_3713_;
v___y_3695_ = v___y_3710_;
v___y_3696_ = v___y_3711_;
goto v___jp_3693_;
}
}
else
{
lean_dec_ref_known(v_pre_3716_, 2);
lean_dec(v_pre_3717_);
lean_dec_ref_known(v_declName_3715_, 2);
lean_dec(v_a_3708_);
lean_dec(v_catName_3680_);
v___y_3694_ = v_a_3713_;
v___y_3695_ = v___y_3710_;
v___y_3696_ = v___y_3711_;
goto v___jp_3693_;
}
}
else
{
lean_dec(v_pre_3716_);
lean_dec_ref_known(v_declName_3715_, 2);
lean_dec(v_a_3708_);
lean_dec(v_catName_3680_);
v___y_3694_ = v_a_3713_;
v___y_3695_ = v___y_3710_;
v___y_3696_ = v___y_3711_;
goto v___jp_3693_;
}
}
else
{
lean_dec(v_declName_3715_);
lean_dec(v_a_3708_);
lean_dec(v_catName_3680_);
v___y_3694_ = v_a_3713_;
v___y_3695_ = v___y_3710_;
v___y_3696_ = v___y_3711_;
goto v___jp_3693_;
}
}
else
{
lean_dec_ref(v___x_3714_);
lean_dec(v_a_3708_);
lean_dec(v_catName_3680_);
v___y_3694_ = v_a_3713_;
v___y_3695_ = v___y_3710_;
v___y_3696_ = v___y_3711_;
goto v___jp_3693_;
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec(v_a_3708_);
lean_dec(v_declName_3681_);
lean_dec(v_catName_3680_);
v_a_3731_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3712_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3712_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec(v_declName_3681_);
lean_dec(v_catName_3680_);
lean_dec(v_attrName_3679_);
v_a_3742_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3707_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3707_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
v___jp_3687_:
{
lean_object* v___x_3690_; 
lean_inc(v_declName_3681_);
v___x_3690_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_3681_, v___y_3688_, v___y_3689_);
if (lean_obj_tag(v___x_3690_) == 0)
{
uint8_t v___x_3691_; lean_object* v___x_3692_; 
lean_dec_ref_known(v___x_3690_, 1);
v___x_3691_ = 1;
v___x_3692_ = l_Lean_Parser_runParserAttributeHooks(v_catName_3680_, v_declName_3681_, v___x_3691_, v___y_3688_, v___y_3689_);
return v___x_3692_;
}
else
{
lean_dec(v_declName_3681_);
lean_dec(v_catName_3680_);
return v___x_3690_;
}
}
v___jp_3693_:
{
lean_object* v___x_3697_; uint8_t v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3697_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
v___x_3698_ = 0;
v___x_3699_ = l_Lean_MessageData_ofConstName(v_declName_3681_, v___x_3698_);
v___x_3700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3697_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
v___x_3701_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
v___x_3702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3700_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
v___x_3703_ = l_Lean_ConstantInfo_type(v___y_3694_);
lean_dec_ref(v___y_3694_);
v___x_3704_ = l_Lean_indentExpr(v___x_3703_);
v___x_3705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3702_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
v___x_3706_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3705_, v___y_3695_, v___y_3696_);
return v___x_3706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* v_attrName_3750_, lean_object* v_catName_3751_, lean_object* v_declName_3752_, lean_object* v_stx_3753_, lean_object* v_kind_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_){
_start:
{
uint8_t v_kind_boxed_3758_; lean_object* v_res_3759_; 
v_kind_boxed_3758_ = lean_unbox(v_kind_3754_);
v_res_3759_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3750_, v_catName_3751_, v_declName_3752_, v_stx_3753_, v_kind_boxed_3758_, v_a_3755_, v_a_3756_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object* v_00_u03b1_3760_, lean_object* v_name_3761_, uint8_t v_kind_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3761_, v_kind_3762_, v___y_3763_, v___y_3764_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b1_3767_, lean_object* v_name_3768_, lean_object* v_kind_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
uint8_t v_kind_boxed_3773_; lean_object* v_res_3774_; 
v_kind_boxed_3773_ = lean_unbox(v_kind_3769_);
v_res_3774_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(v_00_u03b1_3767_, v_name_3768_, v_kind_boxed_3773_, v___y_3770_, v___y_3771_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object* v_00_u03b1_3775_, lean_object* v_constName_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3776_, v___y_3777_, v___y_3778_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3781_, lean_object* v_constName_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(v_00_u03b1_3781_, v_constName_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3787_, lean_object* v_ref_3788_, lean_object* v_constName_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v___x_3793_; 
v___x_3793_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3788_, v_constName_3789_, v___y_3790_, v___y_3791_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3794_, lean_object* v_ref_3795_, lean_object* v_constName_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(v_00_u03b1_3794_, v_ref_3795_, v_constName_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v_ref_3795_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3801_, lean_object* v_ref_3802_, lean_object* v_msg_3803_, lean_object* v_declHint_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3802_, v_msg_3803_, v_declHint_3804_, v___y_3805_, v___y_3806_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3809_, lean_object* v_ref_3810_, lean_object* v_msg_3811_, lean_object* v_declHint_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3809_, v_ref_3810_, v_msg_3811_, v_declHint_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v_ref_3810_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_3817_, lean_object* v_declHint_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3817_, v_declHint_3818_, v___y_3820_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_3823_, lean_object* v_declHint_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_3823_, v_declHint_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3829_, lean_object* v_ref_3830_, lean_object* v_msg_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v___x_3835_; 
v___x_3835_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3830_, v_msg_3831_, v___y_3832_, v___y_3833_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3836_, lean_object* v_ref_3837_, lean_object* v_msg_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3836_, v_ref_3837_, v_msg_3838_, v___y_3839_, v___y_3840_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v_ref_3837_);
return v_res_3842_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2(void){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3849_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0));
v___x_3850_ = l_Lean_mkAtom(v___x_3849_);
return v___x_3850_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3851_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2);
v___x_3852_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3853_ = lean_array_push(v___x_3852_, v___x_3851_);
return v___x_3853_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3862_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7));
v___x_3863_ = l_Lean_mkAtom(v___x_3862_);
return v___x_3863_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3864_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8);
v___x_3865_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3866_ = lean_array_push(v___x_3865_, v___x_3864_);
return v___x_3866_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3867_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9);
v___x_3868_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6));
v___x_3869_ = lean_box(2);
v___x_3870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
lean_ctor_set(v___x_3870_, 1, v___x_3868_);
lean_ctor_set(v___x_3870_, 2, v___x_3867_);
return v___x_3870_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3871_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10);
v___x_3872_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3);
v___x_3873_ = lean_array_push(v___x_3872_, v___x_3871_);
return v___x_3873_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3874_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11);
v___x_3875_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1));
v___x_3876_ = lean_box(2);
v___x_3877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3876_);
lean_ctor_set(v___x_3877_, 1, v___x_3875_);
lean_ctor_set(v___x_3877_, 2, v___x_3874_);
return v___x_3877_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3878_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12);
v___x_3879_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3880_ = lean_array_push(v___x_3879_, v___x_3878_);
return v___x_3880_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14(void){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3881_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13);
v___x_3882_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3883_ = lean_box(2);
v___x_3884_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
lean_ctor_set(v___x_3884_, 1, v___x_3882_);
lean_ctor_set(v___x_3884_, 2, v___x_3881_);
return v___x_3884_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3885_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14);
v___x_3886_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3887_ = lean_array_push(v___x_3886_, v___x_3885_);
return v___x_3887_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3888_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15);
v___x_3889_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3890_ = lean_box(2);
v___x_3891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
lean_ctor_set(v___x_3891_, 1, v___x_3889_);
lean_ctor_set(v___x_3891_, 2, v___x_3888_);
return v___x_3891_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3892_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16);
v___x_3893_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3894_ = lean_array_push(v___x_3893_, v___x_3892_);
return v___x_3894_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3895_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17);
v___x_3896_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3897_ = lean_box(2);
v___x_3898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
lean_ctor_set(v___x_3898_, 1, v___x_3896_);
lean_ctor_set(v___x_3898_, 2, v___x_3895_);
return v___x_3898_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object* v_attrName_3900_, lean_object* v_decl_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3905_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3906_ = l_Lean_MessageData_ofName(v_attrName_3900_);
v___x_3907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3905_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3907_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3909_, v___y_3902_, v___y_3903_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object* v_attrName_3911_, lean_object* v_decl_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_3911_, v_decl_3912_, v___y_3913_, v___y_3914_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v_decl_3912_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object* v_attrName_3917_, lean_object* v_catName_3918_, lean_object* v_declName_3919_, lean_object* v_stx_3920_, uint8_t v_kind_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3917_, v_catName_3918_, v_declName_3919_, v_stx_3920_, v_kind_3921_, v___y_3922_, v___y_3923_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object* v_attrName_3926_, lean_object* v_catName_3927_, lean_object* v_declName_3928_, lean_object* v_stx_3929_, lean_object* v_kind_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
uint8_t v_kind_boxed_3934_; lean_object* v_res_3935_; 
v_kind_boxed_3934_ = lean_unbox(v_kind_3930_);
v_res_3935_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_3926_, v_catName_3927_, v_declName_3928_, v_stx_3929_, v_kind_boxed_3934_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
return v_res_3935_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1(void){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__0));
v___x_3938_ = lean_mk_io_user_error(v___x_3937_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* v_attrName_3941_, lean_object* v_declName_3942_, uint8_t v_behavior_3943_, lean_object* v_ref_3944_){
_start:
{
if (lean_obj_tag(v_declName_3942_) == 1)
{
lean_object* v_pre_3949_; 
v_pre_3949_ = lean_ctor_get(v_declName_3942_, 0);
if (lean_obj_tag(v_pre_3949_) == 1)
{
lean_object* v_pre_3950_; 
v_pre_3950_ = lean_ctor_get(v_pre_3949_, 0);
if (lean_obj_tag(v_pre_3950_) == 1)
{
lean_object* v_pre_3951_; 
v_pre_3951_ = lean_ctor_get(v_pre_3950_, 0);
if (lean_obj_tag(v_pre_3951_) == 1)
{
lean_object* v_pre_3952_; 
v_pre_3952_ = lean_ctor_get(v_pre_3951_, 0);
if (lean_obj_tag(v_pre_3952_) == 0)
{
lean_object* v_str_3953_; lean_object* v_str_3954_; lean_object* v_str_3955_; lean_object* v_str_3956_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
v_str_3953_ = lean_ctor_get(v_declName_3942_, 1);
v_str_3954_ = lean_ctor_get(v_pre_3949_, 1);
v_str_3955_ = lean_ctor_get(v_pre_3950_, 1);
v_str_3956_ = lean_ctor_get(v_pre_3951_, 1);
v___x_3957_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3958_ = lean_string_dec_eq(v_str_3956_, v___x_3957_);
if (v___x_3958_ == 0)
{
lean_dec_ref_known(v_declName_3942_, 2);
lean_dec(v_ref_3944_);
lean_dec(v_attrName_3941_);
goto v___jp_3946_;
}
else
{
lean_object* v___x_3959_; uint8_t v___x_3960_; 
v___x_3959_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3960_ = lean_string_dec_eq(v_str_3955_, v___x_3959_);
if (v___x_3960_ == 0)
{
lean_dec_ref_known(v_declName_3942_, 2);
lean_dec(v_ref_3944_);
lean_dec(v_attrName_3941_);
goto v___jp_3946_;
}
else
{
lean_object* v___x_3961_; uint8_t v___x_3962_; 
v___x_3961_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__2));
v___x_3962_ = lean_string_dec_eq(v_str_3954_, v___x_3961_);
if (v___x_3962_ == 0)
{
lean_dec_ref_known(v_declName_3942_, 2);
lean_dec(v_ref_3944_);
lean_dec(v_attrName_3941_);
goto v___jp_3946_;
}
else
{
lean_object* v___x_3963_; lean_object* v_catName_3964_; lean_object* v___x_3965_; 
v___x_3963_ = lean_box(0);
lean_inc_ref(v_str_3953_);
v_catName_3964_ = l_Lean_Name_str___override(v___x_3963_, v_str_3953_);
lean_inc(v_catName_3964_);
v___x_3965_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_3964_, v_declName_3942_, v_behavior_3943_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v___f_3966_; lean_object* v___f_3967_; lean_object* v___x_3968_; uint8_t v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
lean_dec_ref_known(v___x_3965_, 1);
lean_inc_n(v_attrName_3941_, 2);
v___f_3966_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3966_, 0, v_attrName_3941_);
v___f_3967_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3967_, 0, v_attrName_3941_);
lean_closure_set(v___f_3967_, 1, v_catName_3964_);
v___x_3968_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__3));
v___x_3969_ = 1;
v___x_3970_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3970_, 0, v_ref_3944_);
lean_ctor_set(v___x_3970_, 1, v_attrName_3941_);
lean_ctor_set(v___x_3970_, 2, v___x_3968_);
lean_ctor_set_uint8(v___x_3970_, sizeof(void*)*3, v___x_3969_);
v___x_3971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
lean_ctor_set(v___x_3971_, 1, v___f_3967_);
lean_ctor_set(v___x_3971_, 2, v___f_3966_);
v___x_3972_ = l_Lean_registerBuiltinAttribute(v___x_3971_);
return v___x_3972_;
}
else
{
lean_dec(v_catName_3964_);
lean_dec(v_ref_3944_);
lean_dec(v_attrName_3941_);
return v___x_3965_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_declName_3942_, 2);
lean_dec(v_ref_3944_);
lean_dec(v_attrName_3941_);
goto v___jp_3946_;
}
}
else
{
lean_dec_ref_known(v_declName_3942_, 2);
lean_dec(v_ref_3944_);
lean_dec(v_attrName_3941_);
goto v___jp_3946_;
}
}
else
{
lean_dec_ref_known(v_declName_3942_, 2);
lean_dec(v_ref_3944_);
lean_dec(v_attrName_3941_);
goto v___jp_3946_;
}
}
else
{
lean_dec_ref_known(v_declName_3942_, 2);
lean_dec(v_ref_3944_);
lean_dec(v_attrName_3941_);
goto v___jp_3946_;
}
}
else
{
lean_dec(v_ref_3944_);
lean_dec(v_declName_3942_);
lean_dec(v_attrName_3941_);
goto v___jp_3946_;
}
v___jp_3946_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___closed__1, &l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
v___x_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3947_);
return v___x_3948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* v_attrName_3973_, lean_object* v_declName_3974_, lean_object* v_behavior_3975_, lean_object* v_ref_3976_, lean_object* v_a_3977_){
_start:
{
uint8_t v_behavior_boxed_3978_; lean_object* v_res_3979_; 
v_behavior_boxed_3978_ = lean_unbox(v_behavior_3975_);
v_res_3979_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_3973_, v_declName_3974_, v_behavior_boxed_3978_, v_ref_3976_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object* v_kind_3980_, lean_object* v_x_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v___x_3985_; lean_object* v_env_3986_; lean_object* v_nextMacroScope_3987_; lean_object* v_ngen_3988_; lean_object* v_auxDeclNGen_3989_; lean_object* v_traceState_3990_; lean_object* v_messages_3991_; lean_object* v_infoState_3992_; lean_object* v_snapshotTasks_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4005_; 
v___x_3985_ = lean_st_ref_take(v___y_3983_);
v_env_3986_ = lean_ctor_get(v___x_3985_, 0);
v_nextMacroScope_3987_ = lean_ctor_get(v___x_3985_, 1);
v_ngen_3988_ = lean_ctor_get(v___x_3985_, 2);
v_auxDeclNGen_3989_ = lean_ctor_get(v___x_3985_, 3);
v_traceState_3990_ = lean_ctor_get(v___x_3985_, 4);
v_messages_3991_ = lean_ctor_get(v___x_3985_, 6);
v_infoState_3992_ = lean_ctor_get(v___x_3985_, 7);
v_snapshotTasks_3993_ = lean_ctor_get(v___x_3985_, 8);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4005_ == 0)
{
lean_object* v_unused_4006_; 
v_unused_4006_ = lean_ctor_get(v___x_3985_, 5);
lean_dec(v_unused_4006_);
v___x_3995_ = v___x_3985_;
v_isShared_3996_ = v_isSharedCheck_4005_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_snapshotTasks_3993_);
lean_inc(v_infoState_3992_);
lean_inc(v_messages_3991_);
lean_inc(v_traceState_3990_);
lean_inc(v_auxDeclNGen_3989_);
lean_inc(v_ngen_3988_);
lean_inc(v_nextMacroScope_3987_);
lean_inc(v_env_3986_);
lean_dec(v___x_3985_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4005_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_4000_; 
v___x_3997_ = l_Lean_Parser_addSyntaxNodeKind(v_env_3986_, v_kind_3980_);
v___x_3998_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 5, v___x_3998_);
lean_ctor_set(v___x_3995_, 0, v___x_3997_);
v___x_4000_ = v___x_3995_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_3997_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_nextMacroScope_3987_);
lean_ctor_set(v_reuseFailAlloc_4004_, 2, v_ngen_3988_);
lean_ctor_set(v_reuseFailAlloc_4004_, 3, v_auxDeclNGen_3989_);
lean_ctor_set(v_reuseFailAlloc_4004_, 4, v_traceState_3990_);
lean_ctor_set(v_reuseFailAlloc_4004_, 5, v___x_3998_);
lean_ctor_set(v_reuseFailAlloc_4004_, 6, v_messages_3991_);
lean_ctor_set(v_reuseFailAlloc_4004_, 7, v_infoState_3992_);
lean_ctor_set(v_reuseFailAlloc_4004_, 8, v_snapshotTasks_3993_);
v___x_4000_ = v_reuseFailAlloc_4004_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4001_ = lean_st_ref_put(v___y_3983_, v___x_4000_);
v___x_4002_ = lean_box(0);
v___x_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
return v___x_4003_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object* v_kind_4007_, lean_object* v_x_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_4007_, v_x_4008_, v___y_4009_, v___y_4010_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_4013_, lean_object* v_keys_4014_, lean_object* v_vals_4015_, lean_object* v_i_4016_, lean_object* v_acc_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v___x_4021_; uint8_t v___x_4022_; 
v___x_4021_ = lean_array_get_size(v_keys_4014_);
v___x_4022_ = lean_nat_dec_lt(v_i_4016_, v___x_4021_);
if (v___x_4022_ == 0)
{
lean_object* v___x_4023_; 
lean_dec(v_i_4016_);
lean_dec_ref(v_f_4013_);
v___x_4023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4023_, 0, v_acc_4017_);
return v___x_4023_;
}
else
{
lean_object* v_k_4024_; lean_object* v_v_4025_; lean_object* v___x_4026_; 
v_k_4024_ = lean_array_fget_borrowed(v_keys_4014_, v_i_4016_);
v_v_4025_ = lean_array_fget_borrowed(v_vals_4015_, v_i_4016_);
lean_inc_ref(v_f_4013_);
lean_inc(v___y_4019_);
lean_inc_ref(v___y_4018_);
lean_inc(v_v_4025_);
lean_inc(v_k_4024_);
v___x_4026_ = lean_apply_6(v_f_4013_, v_acc_4017_, v_k_4024_, v_v_4025_, v___y_4018_, v___y_4019_, lean_box(0));
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref_known(v___x_4026_, 1);
v___x_4028_ = lean_unsigned_to_nat(1u);
v___x_4029_ = lean_nat_add(v_i_4016_, v___x_4028_);
lean_dec(v_i_4016_);
v_i_4016_ = v___x_4029_;
v_acc_4017_ = v_a_4027_;
goto _start;
}
else
{
lean_dec(v_i_4016_);
lean_dec_ref(v_f_4013_);
return v___x_4026_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_4031_, lean_object* v_keys_4032_, lean_object* v_vals_4033_, lean_object* v_i_4034_, lean_object* v_acc_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4031_, v_keys_4032_, v_vals_4033_, v_i_4034_, v_acc_4035_, v___y_4036_, v___y_4037_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec_ref(v_vals_4033_);
lean_dec_ref(v_keys_4032_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object* v_f_4040_, lean_object* v_x_4041_, lean_object* v_x_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
if (lean_obj_tag(v_x_4041_) == 0)
{
lean_object* v_es_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4066_; 
v_es_4046_ = lean_ctor_get(v_x_4041_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v_x_4041_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4048_ = v_x_4041_;
v_isShared_4049_ = v_isSharedCheck_4066_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_es_4046_);
lean_dec(v_x_4041_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4066_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; uint8_t v___x_4052_; 
v___x_4050_ = lean_unsigned_to_nat(0u);
v___x_4051_ = lean_array_get_size(v_es_4046_);
v___x_4052_ = lean_nat_dec_lt(v___x_4050_, v___x_4051_);
if (v___x_4052_ == 0)
{
lean_object* v___x_4054_; 
lean_dec_ref(v_es_4046_);
lean_dec_ref(v_f_4040_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v_x_4042_);
v___x_4054_ = v___x_4048_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_x_4042_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
else
{
uint8_t v___x_4056_; 
v___x_4056_ = lean_nat_dec_le(v___x_4051_, v___x_4051_);
if (v___x_4056_ == 0)
{
if (v___x_4052_ == 0)
{
lean_object* v___x_4058_; 
lean_dec_ref(v_es_4046_);
lean_dec_ref(v_f_4040_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v_x_4042_);
v___x_4058_ = v___x_4048_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_x_4042_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
else
{
size_t v___x_4060_; size_t v___x_4061_; lean_object* v___x_4062_; 
lean_del_object(v___x_4048_);
v___x_4060_ = ((size_t)0ULL);
v___x_4061_ = lean_usize_of_nat(v___x_4051_);
v___x_4062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4040_, v_es_4046_, v___x_4060_, v___x_4061_, v_x_4042_, v___y_4043_, v___y_4044_);
lean_dec_ref(v_es_4046_);
return v___x_4062_;
}
}
else
{
size_t v___x_4063_; size_t v___x_4064_; lean_object* v___x_4065_; 
lean_del_object(v___x_4048_);
v___x_4063_ = ((size_t)0ULL);
v___x_4064_ = lean_usize_of_nat(v___x_4051_);
v___x_4065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4040_, v_es_4046_, v___x_4063_, v___x_4064_, v_x_4042_, v___y_4043_, v___y_4044_);
lean_dec_ref(v_es_4046_);
return v___x_4065_;
}
}
}
}
else
{
lean_object* v_ks_4067_; lean_object* v_vs_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v_ks_4067_ = lean_ctor_get(v_x_4041_, 0);
lean_inc_ref(v_ks_4067_);
v_vs_4068_ = lean_ctor_get(v_x_4041_, 1);
lean_inc_ref(v_vs_4068_);
lean_dec_ref_known(v_x_4041_, 2);
v___x_4069_ = lean_unsigned_to_nat(0u);
v___x_4070_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4040_, v_ks_4067_, v_vs_4068_, v___x_4069_, v_x_4042_, v___y_4043_, v___y_4044_);
lean_dec_ref(v_vs_4068_);
lean_dec_ref(v_ks_4067_);
return v___x_4070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_4071_, lean_object* v_as_4072_, size_t v_i_4073_, size_t v_stop_4074_, lean_object* v_b_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_a_4080_; lean_object* v___y_4085_; uint8_t v___x_4087_; 
v___x_4087_ = lean_usize_dec_eq(v_i_4073_, v_stop_4074_);
if (v___x_4087_ == 0)
{
lean_object* v___x_4088_; 
v___x_4088_ = lean_array_uget_borrowed(v_as_4072_, v_i_4073_);
switch(lean_obj_tag(v___x_4088_))
{
case 0:
{
lean_object* v_key_4089_; lean_object* v_val_4090_; lean_object* v___x_4091_; 
v_key_4089_ = lean_ctor_get(v___x_4088_, 0);
v_val_4090_ = lean_ctor_get(v___x_4088_, 1);
lean_inc_ref(v_f_4071_);
lean_inc(v___y_4077_);
lean_inc_ref(v___y_4076_);
lean_inc(v_val_4090_);
lean_inc(v_key_4089_);
v___x_4091_ = lean_apply_6(v_f_4071_, v_b_4075_, v_key_4089_, v_val_4090_, v___y_4076_, v___y_4077_, lean_box(0));
v___y_4085_ = v___x_4091_;
goto v___jp_4084_;
}
case 1:
{
lean_object* v_node_4092_; lean_object* v___x_4093_; 
v_node_4092_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_node_4092_);
lean_inc_ref(v_f_4071_);
v___x_4093_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4071_, v_node_4092_, v_b_4075_, v___y_4076_, v___y_4077_);
v___y_4085_ = v___x_4093_;
goto v___jp_4084_;
}
default: 
{
v_a_4080_ = v_b_4075_;
goto v___jp_4079_;
}
}
}
else
{
lean_object* v___x_4094_; 
lean_dec_ref(v_f_4071_);
v___x_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4094_, 0, v_b_4075_);
return v___x_4094_;
}
v___jp_4079_:
{
size_t v___x_4081_; size_t v___x_4082_; 
v___x_4081_ = ((size_t)1ULL);
v___x_4082_ = lean_usize_add(v_i_4073_, v___x_4081_);
v_i_4073_ = v___x_4082_;
v_b_4075_ = v_a_4080_;
goto _start;
}
v___jp_4084_:
{
if (lean_obj_tag(v___y_4085_) == 0)
{
lean_object* v_a_4086_; 
v_a_4086_ = lean_ctor_get(v___y_4085_, 0);
lean_inc(v_a_4086_);
lean_dec_ref_known(v___y_4085_, 1);
v_a_4080_ = v_a_4086_;
goto v___jp_4079_;
}
else
{
lean_dec_ref(v_f_4071_);
return v___y_4085_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_4095_, lean_object* v_as_4096_, lean_object* v_i_4097_, lean_object* v_stop_4098_, lean_object* v_b_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
size_t v_i_boxed_4103_; size_t v_stop_boxed_4104_; lean_object* v_res_4105_; 
v_i_boxed_4103_ = lean_unbox_usize(v_i_4097_);
lean_dec(v_i_4097_);
v_stop_boxed_4104_ = lean_unbox_usize(v_stop_4098_);
lean_dec(v_stop_4098_);
v_res_4105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4095_, v_as_4096_, v_i_boxed_4103_, v_stop_boxed_4104_, v_b_4099_, v___y_4100_, v___y_4101_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec_ref(v_as_4096_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_4106_, lean_object* v_x_4107_, lean_object* v_x_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4106_, v_x_4107_, v_x_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object* v_f_4113_, lean_object* v_x_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___x_4120_; 
lean_inc(v___y_4118_);
lean_inc_ref(v___y_4117_);
v___x_4120_ = lean_apply_5(v_f_4113_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, lean_box(0));
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object* v_f_4121_, lean_object* v_x_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4121_, v_x_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object* v_map_4129_, lean_object* v_f_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v___f_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___f_4134_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4134_, 0, v_f_4130_);
v___x_4135_ = lean_box(0);
v___x_4136_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v___f_4134_, v_map_4129_, v___x_4135_, v___y_4131_, v___y_4132_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object* v_map_4137_, lean_object* v_f_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4137_, v_f_4138_, v___y_4139_, v___y_4140_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
return v_res_4142_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4144_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0));
v___x_4145_ = l_Lean_stringToMessageData(v___x_4144_);
return v___x_4145_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_4147_ = l_Lean_stringToMessageData(v___x_4146_);
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t v_attrKind_4148_, lean_object* v_declName_4149_, lean_object* v_as_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
if (lean_obj_tag(v_as_4150_) == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
lean_dec(v_declName_4149_);
v___x_4154_ = lean_box(0);
v___x_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
return v___x_4155_;
}
else
{
lean_object* v_head_4156_; lean_object* v_tail_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4187_; 
v_head_4156_ = lean_ctor_get(v_as_4150_, 0);
v_tail_4157_ = lean_ctor_get(v_as_4150_, 1);
v_isSharedCheck_4187_ = !lean_is_exclusive(v_as_4150_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4159_ = v_as_4150_;
v_isShared_4160_ = v_isSharedCheck_4187_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_tail_4157_);
lean_inc(v_head_4156_);
lean_dec(v_as_4150_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4187_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___y_4162_; lean_object* v___x_4164_; 
v___x_4164_ = l_Lean_Parser_addToken(v_head_4156_, v_attrKind_4148_, v___y_4151_, v___y_4152_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_del_object(v___x_4159_);
v___y_4162_ = v___x_4164_;
goto v___jp_4161_;
}
else
{
lean_object* v_a_4165_; uint8_t v___y_4167_; uint8_t v___x_4185_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
v___x_4185_ = l_Lean_Exception_isInterrupt(v_a_4165_);
if (v___x_4185_ == 0)
{
uint8_t v___x_4186_; 
lean_inc(v_a_4165_);
v___x_4186_ = l_Lean_Exception_isRuntime(v_a_4165_);
v___y_4167_ = v___x_4186_;
goto v___jp_4166_;
}
else
{
v___y_4167_ = v___x_4185_;
goto v___jp_4166_;
}
v___jp_4166_:
{
if (v___y_4167_ == 0)
{
if (lean_obj_tag(v_a_4165_) == 0)
{
lean_object* v_msg_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4183_; 
lean_dec_ref_known(v___x_4164_, 1);
v_msg_4168_ = lean_ctor_get(v_a_4165_, 1);
v_isSharedCheck_4183_ = !lean_is_exclusive(v_a_4165_);
if (v_isSharedCheck_4183_ == 0)
{
lean_object* v_unused_4184_; 
v_unused_4184_ = lean_ctor_get(v_a_4165_, 0);
lean_dec(v_unused_4184_);
v___x_4170_ = v_a_4165_;
v_isShared_4171_ = v_isSharedCheck_4183_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_msg_4168_);
lean_dec(v_a_4165_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4183_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
v___x_4172_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1);
lean_inc(v_declName_4149_);
v___x_4173_ = l_Lean_MessageData_ofConstName(v_declName_4149_, v___y_4167_);
if (v_isShared_4171_ == 0)
{
lean_ctor_set_tag(v___x_4170_, 7);
lean_ctor_set(v___x_4170_, 1, v___x_4173_);
lean_ctor_set(v___x_4170_, 0, v___x_4172_);
v___x_4175_ = v___x_4170_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4172_);
lean_ctor_set(v_reuseFailAlloc_4182_, 1, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
lean_object* v___x_4176_; lean_object* v___x_4178_; 
v___x_4176_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2);
if (v_isShared_4160_ == 0)
{
lean_ctor_set_tag(v___x_4159_, 7);
lean_ctor_set(v___x_4159_, 1, v___x_4176_);
lean_ctor_set(v___x_4159_, 0, v___x_4175_);
v___x_4178_ = v___x_4159_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4175_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v___x_4176_);
v___x_4178_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4178_);
lean_ctor_set(v___x_4179_, 1, v_msg_4168_);
v___x_4180_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4179_, v___y_4151_, v___y_4152_);
v___y_4162_ = v___x_4180_;
goto v___jp_4161_;
}
}
}
}
else
{
lean_dec(v_a_4165_);
lean_del_object(v___x_4159_);
v___y_4162_ = v___x_4164_;
goto v___jp_4161_;
}
}
else
{
lean_dec(v_a_4165_);
lean_del_object(v___x_4159_);
v___y_4162_ = v___x_4164_;
goto v___jp_4161_;
}
}
}
v___jp_4161_:
{
if (lean_obj_tag(v___y_4162_) == 0)
{
lean_dec_ref_known(v___y_4162_, 1);
v_as_4150_ = v_tail_4157_;
goto _start;
}
else
{
lean_dec(v_tail_4157_);
lean_dec(v_declName_4149_);
return v___y_4162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object* v_attrKind_4188_, lean_object* v_declName_4189_, lean_object* v_as_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
uint8_t v_attrKind_boxed_4194_; lean_object* v_res_4195_; 
v_attrKind_boxed_4194_ = lean_unbox(v_attrKind_4188_);
v_res_4195_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_boxed_4194_, v_declName_4189_, v_as_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object* v_catName_4197_, lean_object* v_declName_4198_, lean_object* v_stx_4199_, uint8_t v_attrKind_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___x_4209_; 
v___x_4209_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4199_, v_a_4201_, v_a_4202_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v_env_4213_; lean_object* v___x_4214_; lean_object* v_ext_4215_; lean_object* v_toEnvExtension_4216_; lean_object* v_asyncMode_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v_categories_4220_; lean_object* v_env_4221_; lean_object* v_options_4222_; lean_object* v_ref_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_a_4210_);
lean_dec_ref_known(v___x_4209_, 1);
v___x_4211_ = lean_st_ref_get(v_a_4202_);
v___x_4212_ = lean_st_ref_get(v_a_4202_);
v_env_4213_ = lean_ctor_get(v___x_4211_, 0);
lean_inc_ref(v_env_4213_);
lean_dec(v___x_4211_);
v___x_4214_ = l_Lean_Parser_parserExtension;
v_ext_4215_ = lean_ctor_get(v___x_4214_, 1);
v_toEnvExtension_4216_ = lean_ctor_get(v_ext_4215_, 0);
v_asyncMode_4217_ = lean_ctor_get(v_toEnvExtension_4216_, 2);
v___x_4218_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4219_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4218_, v___x_4214_, v_env_4213_, v_asyncMode_4217_);
v_categories_4220_ = lean_ctor_get(v___x_4219_, 2);
lean_inc_ref_n(v_categories_4220_, 2);
lean_dec(v___x_4219_);
v_env_4221_ = lean_ctor_get(v___x_4212_, 0);
lean_inc_ref(v_env_4221_);
lean_dec(v___x_4212_);
v_options_4222_ = lean_ctor_get(v_a_4201_, 2);
v_ref_4223_ = lean_ctor_get(v_a_4201_, 5);
lean_inc_ref(v_options_4222_);
v___x_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4224_, 0, v_env_4221_);
lean_ctor_set(v___x_4224_, 1, v_options_4222_);
lean_inc(v_declName_4198_);
v___x_4225_ = l_Lean_Parser_mkParserOfConstant(v_categories_4220_, v_declName_4198_, v___x_4224_);
lean_dec_ref_known(v___x_4224_, 2);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v_snd_4227_; lean_object* v_info_4228_; lean_object* v_fst_4229_; lean_object* v_collectTokens_4230_; lean_object* v_collectKinds_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
v_snd_4227_ = lean_ctor_get(v_a_4226_, 1);
lean_inc(v_snd_4227_);
v_info_4228_ = lean_ctor_get(v_snd_4227_, 0);
v_fst_4229_ = lean_ctor_get(v_a_4226_, 0);
lean_inc(v_fst_4229_);
lean_dec(v_a_4226_);
v_collectTokens_4230_ = lean_ctor_get(v_info_4228_, 0);
v_collectKinds_4231_ = lean_ctor_get(v_info_4228_, 1);
v___x_4232_ = lean_box(0);
lean_inc_ref(v_collectTokens_4230_);
v___x_4233_ = lean_apply_1(v_collectTokens_4230_, v___x_4232_);
lean_inc(v_declName_4198_);
v___x_4234_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4200_, v_declName_4198_, v___x_4233_, v_a_4201_, v_a_4202_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v___f_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
lean_dec_ref_known(v___x_4234_, 1);
v___f_4235_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0));
v___x_4236_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
lean_inc_ref(v_collectKinds_4231_);
v___x_4237_ = lean_apply_1(v_collectKinds_4231_, v___x_4236_);
v___x_4238_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v___x_4237_, v___f_4235_, v_a_4201_, v_a_4202_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v___x_4239_; uint8_t v___x_4240_; uint8_t v___x_4241_; lean_object* v___x_4242_; 
lean_dec_ref_known(v___x_4238_, 1);
lean_inc(v_a_4210_);
lean_inc(v_snd_4227_);
lean_inc_n(v_declName_4198_, 2);
lean_inc_n(v_catName_4197_, 2);
v___x_4239_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_4239_, 0, v_catName_4197_);
lean_ctor_set(v___x_4239_, 1, v_declName_4198_);
lean_ctor_set(v___x_4239_, 2, v_snd_4227_);
lean_ctor_set(v___x_4239_, 3, v_a_4210_);
v___x_4240_ = lean_unbox(v_fst_4229_);
lean_ctor_set_uint8(v___x_4239_, sizeof(void*)*4, v___x_4240_);
v___x_4241_ = lean_unbox(v_fst_4229_);
lean_dec(v_fst_4229_);
v___x_4242_ = l_Lean_Parser_addParser(v_categories_4220_, v_catName_4197_, v_declName_4198_, v___x_4241_, v_snd_4227_, v_a_4210_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4252_; 
lean_dec_ref_known(v___x_4239_, 4);
lean_dec(v_declName_4198_);
lean_dec(v_catName_4197_);
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4245_ = v___x_4242_;
v_isShared_4246_ = v_isSharedCheck_4252_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4242_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4252_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
lean_ctor_set_tag(v___x_4245_, 3);
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = l_Lean_MessageData_ofFormat(v___x_4248_);
v___x_4250_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4249_, v_a_4201_, v_a_4202_);
return v___x_4250_;
}
}
}
else
{
lean_object* v___x_4253_; 
lean_dec_ref_known(v___x_4242_, 1);
v___x_4253_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_4214_, v___x_4239_, v_attrKind_4200_, v_a_4201_, v_a_4202_);
lean_dec_ref(v___x_4253_);
v___y_4205_ = v_a_4201_;
v___y_4206_ = v_a_4202_;
goto v___jp_4204_;
}
}
else
{
lean_dec(v_fst_4229_);
lean_dec(v_snd_4227_);
lean_dec_ref(v_categories_4220_);
lean_dec(v_a_4210_);
lean_dec(v_declName_4198_);
lean_dec(v_catName_4197_);
return v___x_4238_;
}
}
else
{
lean_dec(v_fst_4229_);
lean_dec(v_snd_4227_);
lean_dec_ref(v_categories_4220_);
lean_dec(v_a_4210_);
lean_dec(v_declName_4198_);
lean_dec(v_catName_4197_);
return v___x_4234_;
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4265_; 
lean_dec_ref(v_categories_4220_);
lean_dec(v_a_4210_);
lean_dec(v_declName_4198_);
lean_dec(v_catName_4197_);
v_a_4254_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4256_ = v___x_4225_;
v_isShared_4257_ = v_isSharedCheck_4265_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4225_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4265_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4263_; 
v___x_4258_ = lean_io_error_to_string(v_a_4254_);
v___x_4259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4258_);
v___x_4260_ = l_Lean_MessageData_ofFormat(v___x_4259_);
lean_inc(v_ref_4223_);
v___x_4261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4261_, 0, v_ref_4223_);
lean_ctor_set(v___x_4261_, 1, v___x_4260_);
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 0, v___x_4261_);
v___x_4263_ = v___x_4256_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4261_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
else
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
lean_dec(v_declName_4198_);
lean_dec(v_catName_4197_);
v_a_4266_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4268_ = v___x_4209_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___x_4209_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4266_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
v___jp_4204_:
{
uint8_t v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = 0;
v___x_4208_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4197_, v_declName_4198_, v___x_4207_, v___y_4205_, v___y_4206_);
return v___x_4208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object* v_catName_4274_, lean_object* v_declName_4275_, lean_object* v_stx_4276_, lean_object* v_attrKind_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_){
_start:
{
uint8_t v_attrKind_boxed_4281_; lean_object* v_res_4282_; 
v_attrKind_boxed_4281_ = lean_unbox(v_attrKind_4277_);
v_res_4282_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4274_, v_declName_4275_, v_stx_4276_, v_attrKind_boxed_4281_, v_a_4278_, v_a_4279_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* v___attrName_4283_, lean_object* v_catName_4284_, lean_object* v_declName_4285_, lean_object* v_stx_4286_, uint8_t v_attrKind_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4284_, v_declName_4285_, v_stx_4286_, v_attrKind_4287_, v_a_4288_, v_a_4289_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* v___attrName_4292_, lean_object* v_catName_4293_, lean_object* v_declName_4294_, lean_object* v_stx_4295_, lean_object* v_attrKind_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_){
_start:
{
uint8_t v_attrKind_boxed_4300_; lean_object* v_res_4301_; 
v_attrKind_boxed_4300_ = lean_unbox(v_attrKind_4296_);
v_res_4301_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4292_, v_catName_4293_, v_declName_4294_, v_stx_4295_, v_attrKind_boxed_4300_, v_a_4297_, v_a_4298_);
lean_dec(v_a_4298_);
lean_dec_ref(v_a_4297_);
lean_dec(v___attrName_4292_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object* v_00_u03b2_4302_, lean_object* v_map_4303_, lean_object* v_f_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4303_, v_f_4304_, v___y_4305_, v___y_4306_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b2_4309_, lean_object* v_map_4310_, lean_object* v_f_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(v_00_u03b2_4309_, v_map_4310_, v_f_4311_, v___y_4312_, v___y_4313_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object* v_map_4316_, lean_object* v_f_4317_, lean_object* v_init_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4317_, v_map_4316_, v_init_4318_, v___y_4319_, v___y_4320_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object* v_map_4323_, lean_object* v_f_4324_, lean_object* v_init_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4323_, v_f_4324_, v_init_4325_, v___y_4326_, v___y_4327_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object* v_00_u03c3_4330_, lean_object* v_00_u03b2_4331_, lean_object* v_map_4332_, lean_object* v_f_4333_, lean_object* v_init_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4333_, v_map_4332_, v_init_4334_, v___y_4335_, v___y_4336_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object* v_00_u03c3_4339_, lean_object* v_00_u03b2_4340_, lean_object* v_map_4341_, lean_object* v_f_4342_, lean_object* v_init_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(v_00_u03c3_4339_, v_00_u03b2_4340_, v_map_4341_, v_f_4342_, v_init_4343_, v___y_4344_, v___y_4345_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_4348_, lean_object* v_00_u03b1_4349_, lean_object* v_00_u03b2_4350_, lean_object* v_f_4351_, lean_object* v_x_4352_, lean_object* v_x_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4351_, v_x_4352_, v_x_4353_, v___y_4354_, v___y_4355_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03c3_4358_, lean_object* v_00_u03b1_4359_, lean_object* v_00_u03b2_4360_, lean_object* v_f_4361_, lean_object* v_x_4362_, lean_object* v_x_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(v_00_u03c3_4358_, v_00_u03b1_4359_, v_00_u03b2_4360_, v_f_4361_, v_x_4362_, v_x_4363_, v___y_4364_, v___y_4365_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4368_, lean_object* v_00_u03b2_4369_, lean_object* v_00_u03c3_4370_, lean_object* v_f_4371_, lean_object* v_as_4372_, size_t v_i_4373_, size_t v_stop_4374_, lean_object* v_b_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v___x_4379_; 
v___x_4379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4371_, v_as_4372_, v_i_4373_, v_stop_4374_, v_b_4375_, v___y_4376_, v___y_4377_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4380_, lean_object* v_00_u03b2_4381_, lean_object* v_00_u03c3_4382_, lean_object* v_f_4383_, lean_object* v_as_4384_, lean_object* v_i_4385_, lean_object* v_stop_4386_, lean_object* v_b_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
size_t v_i_boxed_4391_; size_t v_stop_boxed_4392_; lean_object* v_res_4393_; 
v_i_boxed_4391_ = lean_unbox_usize(v_i_4385_);
lean_dec(v_i_4385_);
v_stop_boxed_4392_ = lean_unbox_usize(v_stop_4386_);
lean_dec(v_stop_4386_);
v_res_4393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4380_, v_00_u03b2_4381_, v_00_u03c3_4382_, v_f_4383_, v_as_4384_, v_i_boxed_4391_, v_stop_boxed_4392_, v_b_4387_, v___y_4388_, v___y_4389_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec_ref(v_as_4384_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_4394_, lean_object* v_00_u03b1_4395_, lean_object* v_00_u03b2_4396_, lean_object* v_f_4397_, lean_object* v_keys_4398_, lean_object* v_vals_4399_, lean_object* v_heq_4400_, lean_object* v_i_4401_, lean_object* v_acc_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v___x_4406_; 
v___x_4406_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4397_, v_keys_4398_, v_vals_4399_, v_i_4401_, v_acc_4402_, v___y_4403_, v___y_4404_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_4407_, lean_object* v_00_u03b1_4408_, lean_object* v_00_u03b2_4409_, lean_object* v_f_4410_, lean_object* v_keys_4411_, lean_object* v_vals_4412_, lean_object* v_heq_4413_, lean_object* v_i_4414_, lean_object* v_acc_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4407_, v_00_u03b1_4408_, v_00_u03b2_4409_, v_f_4410_, v_keys_4411_, v_vals_4412_, v_heq_4413_, v_i_4414_, v_acc_4415_, v___y_4416_, v___y_4417_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
lean_dec_ref(v_vals_4412_);
lean_dec_ref(v_keys_4411_);
return v_res_4419_;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___auto__1(void){
_start:
{
lean_object* v___x_4420_; 
v___x_4420_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object* v_catName_4421_, lean_object* v_declName_4422_, lean_object* v_stx_4423_, uint8_t v_attrKind_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v___x_4428_; 
v___x_4428_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4421_, v_declName_4422_, v_stx_4423_, v_attrKind_4424_, v___y_4425_, v___y_4426_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object* v_catName_4429_, lean_object* v_declName_4430_, lean_object* v_stx_4431_, lean_object* v_attrKind_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
uint8_t v_attrKind_boxed_4436_; lean_object* v_res_4437_; 
v_attrKind_boxed_4436_ = lean_unbox(v_attrKind_4432_);
v_res_4437_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4429_, v_declName_4430_, v_stx_4431_, v_attrKind_boxed_4436_, v___y_4433_, v___y_4434_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* v_attrName_4439_, lean_object* v_catName_4440_, lean_object* v_ref_4441_){
_start:
{
lean_object* v___f_4442_; lean_object* v___f_4443_; lean_object* v___x_4444_; uint8_t v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___f_4442_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4442_, 0, v_catName_4440_);
lean_inc(v_attrName_4439_);
v___f_4443_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4443_, 0, v_attrName_4439_);
v___x_4444_ = ((lean_object*)(l_Lean_Parser_mkParserAttributeImpl___closed__0));
v___x_4445_ = 1;
v___x_4446_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4446_, 0, v_ref_4441_);
lean_ctor_set(v___x_4446_, 1, v_attrName_4439_);
lean_ctor_set(v___x_4446_, 2, v___x_4444_);
lean_ctor_set_uint8(v___x_4446_, sizeof(void*)*3, v___x_4445_);
v___x_4447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4446_);
lean_ctor_set(v___x_4447_, 1, v___f_4442_);
lean_ctor_set(v___x_4447_, 2, v___f_4443_);
return v___x_4447_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* v_attrName_4449_, lean_object* v_catName_4450_, lean_object* v_ref_4451_){
_start:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = l_Lean_Parser_mkParserAttributeImpl(v_attrName_4449_, v_catName_4450_, v_ref_4451_);
v___x_4454_ = l_Lean_registerBuiltinAttribute(v___x_4453_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object* v_attrName_4455_, lean_object* v_catName_4456_, lean_object* v_ref_4457_, lean_object* v_a_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4455_, v_catName_4456_, v_ref_4457_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object* v_ref_4463_, lean_object* v_args_4464_){
_start:
{
if (lean_obj_tag(v_args_4464_) == 1)
{
lean_object* v_head_4467_; 
v_head_4467_ = lean_ctor_get(v_args_4464_, 0);
lean_inc(v_head_4467_);
if (lean_obj_tag(v_head_4467_) == 2)
{
lean_object* v_tail_4468_; 
v_tail_4468_ = lean_ctor_get(v_args_4464_, 1);
lean_inc(v_tail_4468_);
lean_dec_ref_known(v_args_4464_, 2);
if (lean_obj_tag(v_tail_4468_) == 1)
{
lean_object* v_head_4469_; 
v_head_4469_ = lean_ctor_get(v_tail_4468_, 0);
lean_inc(v_head_4469_);
if (lean_obj_tag(v_head_4469_) == 2)
{
lean_object* v_tail_4470_; 
v_tail_4470_ = lean_ctor_get(v_tail_4468_, 1);
lean_inc(v_tail_4470_);
lean_dec_ref_known(v_tail_4468_, 2);
if (lean_obj_tag(v_tail_4470_) == 0)
{
lean_object* v_v_4471_; lean_object* v_v_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4480_; 
v_v_4471_ = lean_ctor_get(v_head_4467_, 0);
lean_inc(v_v_4471_);
lean_dec_ref_known(v_head_4467_, 1);
v_v_4472_ = lean_ctor_get(v_head_4469_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v_head_4469_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4474_ = v_head_4469_;
v_isShared_4475_ = v_isSharedCheck_4480_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_v_4472_);
lean_dec(v_head_4469_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4480_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4476_; lean_object* v___x_4478_; 
v___x_4476_ = l_Lean_Parser_mkParserAttributeImpl(v_v_4471_, v_v_4472_, v_ref_4463_);
if (v_isShared_4475_ == 0)
{
lean_ctor_set_tag(v___x_4474_, 1);
lean_ctor_set(v___x_4474_, 0, v___x_4476_);
v___x_4478_ = v___x_4474_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4476_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
else
{
lean_dec(v_tail_4470_);
lean_dec_ref_known(v_head_4469_, 1);
lean_dec_ref_known(v_head_4467_, 1);
lean_dec(v_ref_4463_);
goto v___jp_4465_;
}
}
else
{
lean_dec(v_head_4469_);
lean_dec_ref_known(v_tail_4468_, 2);
lean_dec_ref_known(v_head_4467_, 1);
lean_dec(v_ref_4463_);
goto v___jp_4465_;
}
}
else
{
lean_dec_ref_known(v_head_4467_, 1);
lean_dec(v_tail_4468_);
lean_dec(v_ref_4463_);
goto v___jp_4465_;
}
}
else
{
lean_dec(v_head_4467_);
lean_dec_ref_known(v_args_4464_, 2);
lean_dec(v_ref_4463_);
goto v___jp_4465_;
}
}
else
{
lean_dec(v_args_4464_);
lean_dec(v_ref_4463_);
goto v___jp_4465_;
}
v___jp_4465_:
{
lean_object* v___x_4466_; 
v___x_4466_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
return v___x_4466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___f_4486_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4487_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4488_ = l_Lean_registerAttributeImplBuilder(v___x_4487_, v___f_4486_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object* v_a_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
return v_res_4490_;
}
}
static lean_object* _init_l_Lean_Parser_registerParserCategory___auto__1(void){
_start:
{
lean_object* v___x_4491_; 
v___x_4491_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object* v_env_4492_, lean_object* v_attrName_4493_, lean_object* v_catName_4494_, uint8_t v_behavior_4495_, lean_object* v_ref_4496_){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; 
lean_inc(v_ref_4496_);
lean_inc(v_catName_4494_);
v___x_4498_ = l_Lean_Parser_addParserCategory(v_env_4492_, v_catName_4494_, v_ref_4496_, v_behavior_4495_);
v___x_4499_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_4498_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4513_; 
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4502_ = v___x_4499_;
v_isShared_4503_ = v_isSharedCheck_4513_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4499_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4513_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4504_; lean_object* v___x_4506_; 
v___x_4504_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
if (v_isShared_4503_ == 0)
{
lean_ctor_set_tag(v___x_4502_, 2);
lean_ctor_set(v___x_4502_, 0, v_attrName_4493_);
v___x_4506_ = v___x_4502_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_attrName_4493_);
v___x_4506_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4507_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4507_, 0, v_catName_4494_);
v___x_4508_ = lean_box(0);
v___x_4509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4507_);
lean_ctor_set(v___x_4509_, 1, v___x_4508_);
v___x_4510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4506_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
v___x_4511_ = l_Lean_registerAttributeOfBuilder(v_a_4500_, v___x_4504_, v_ref_4496_, v___x_4510_);
return v___x_4511_;
}
}
}
else
{
lean_dec(v_ref_4496_);
lean_dec(v_catName_4494_);
lean_dec(v_attrName_4493_);
return v___x_4499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* v_env_4514_, lean_object* v_attrName_4515_, lean_object* v_catName_4516_, lean_object* v_behavior_4517_, lean_object* v_ref_4518_, lean_object* v_a_4519_){
_start:
{
uint8_t v_behavior_boxed_4520_; lean_object* v_res_4521_; 
v_behavior_boxed_4520_ = lean_unbox(v_behavior_4517_);
v_res_4521_ = l_Lean_Parser_registerParserCategory(v_env_4514_, v_attrName_4515_, v_catName_4516_, v_behavior_boxed_4520_, v_ref_4518_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; uint8_t v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4544_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4545_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4546_ = 0;
v___x_4547_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4548_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4544_, v___x_4545_, v___x_4546_, v___x_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object* v_a_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
return v_res_4550_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4556_ = lean_unsigned_to_nat(3431364690u);
v___x_4557_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4558_ = l_Lean_Name_num___override(v___x_4557_, v___x_4556_);
return v___x_4558_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4559_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4560_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4561_ = l_Lean_Name_str___override(v___x_4560_, v___x_4559_);
return v___x_4561_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4562_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4563_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4564_ = l_Lean_Name_str___override(v___x_4563_, v___x_4562_);
return v___x_4564_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4565_ = lean_unsigned_to_nat(2u);
v___x_4566_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4567_ = l_Lean_Name_num___override(v___x_4566_, v___x_4565_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4569_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4570_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4571_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4572_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4569_, v___x_4570_, v___x_4571_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object* v_a_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
return v_res_4574_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4584_ = lean_unsigned_to_nat(2342493449u);
v___x_4585_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4586_ = l_Lean_Name_num___override(v___x_4585_, v___x_4584_);
return v___x_4586_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4587_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4588_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4589_ = l_Lean_Name_str___override(v___x_4588_, v___x_4587_);
return v___x_4589_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4590_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4591_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4592_ = l_Lean_Name_str___override(v___x_4591_, v___x_4590_);
return v___x_4592_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4593_ = lean_unsigned_to_nat(2u);
v___x_4594_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4595_ = l_Lean_Name_num___override(v___x_4594_, v___x_4593_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; uint8_t v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4597_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4598_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4599_ = 0;
v___x_4600_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4601_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4597_, v___x_4598_, v___x_4599_, v___x_4600_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object* v_a_4602_){
_start:
{
lean_object* v_res_4603_; 
v_res_4603_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
return v_res_4603_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4609_ = lean_unsigned_to_nat(3226070615u);
v___x_4610_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4611_ = l_Lean_Name_num___override(v___x_4610_, v___x_4609_);
return v___x_4611_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4612_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4613_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4614_ = l_Lean_Name_str___override(v___x_4613_, v___x_4612_);
return v___x_4614_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4615_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4616_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4617_ = l_Lean_Name_str___override(v___x_4616_, v___x_4615_);
return v___x_4617_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4618_ = lean_unsigned_to_nat(2u);
v___x_4619_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4620_ = l_Lean_Name_num___override(v___x_4619_, v___x_4618_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4622_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4623_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4624_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4625_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4622_, v___x_4623_, v___x_4624_);
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object* v_a_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* v_rbp_4628_){
_start:
{
lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4629_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4630_ = l_Lean_Parser_categoryParser(v___x_4629_, v_rbp_4628_);
return v___x_4630_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t v_addOpenSimple_4631_, lean_object* v_x_4632_, lean_object* v_x_4633_){
_start:
{
if (lean_obj_tag(v_x_4633_) == 0)
{
return v_x_4632_;
}
else
{
lean_object* v_head_4634_; lean_object* v_tail_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4658_; 
v_head_4634_ = lean_ctor_get(v_x_4633_, 0);
v_tail_4635_ = lean_ctor_get(v_x_4633_, 1);
v_isSharedCheck_4658_ = !lean_is_exclusive(v_x_4633_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4637_ = v_x_4633_;
v_isShared_4638_ = v_isSharedCheck_4658_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_tail_4635_);
lean_inc(v_head_4634_);
lean_dec(v_x_4633_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4658_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v_fst_4639_; lean_object* v_snd_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4657_; 
v_fst_4639_ = lean_ctor_get(v_x_4632_, 0);
v_snd_4640_ = lean_ctor_get(v_x_4632_, 1);
v_isSharedCheck_4657_ = !lean_is_exclusive(v_x_4632_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4642_ = v_x_4632_;
v_isShared_4643_ = v_isSharedCheck_4657_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_snd_4640_);
lean_inc(v_fst_4639_);
lean_dec(v_x_4632_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4657_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___y_4645_; 
if (v_addOpenSimple_4631_ == 0)
{
lean_del_object(v___x_4637_);
v___y_4645_ = v_snd_4640_;
goto v___jp_4644_;
}
else
{
lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4655_; 
v___x_4652_ = lean_box(0);
lean_inc(v_head_4634_);
v___x_4653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4653_, 0, v_head_4634_);
lean_ctor_set(v___x_4653_, 1, v___x_4652_);
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 1, v_snd_4640_);
lean_ctor_set(v___x_4637_, 0, v___x_4653_);
v___x_4655_ = v___x_4637_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4656_, 1, v_snd_4640_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
v___y_4645_ = v___x_4655_;
goto v___jp_4644_;
}
}
v___jp_4644_:
{
lean_object* v___x_4646_; lean_object* v_env_4647_; lean_object* v___x_4649_; 
v___x_4646_ = l_Lean_Parser_parserExtension;
v_env_4647_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v___x_4646_, v_fst_4639_, v_head_4634_);
if (v_isShared_4643_ == 0)
{
lean_ctor_set(v___x_4642_, 1, v___y_4645_);
lean_ctor_set(v___x_4642_, 0, v_env_4647_);
v___x_4649_ = v___x_4642_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_env_4647_);
lean_ctor_set(v_reuseFailAlloc_4651_, 1, v___y_4645_);
v___x_4649_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
v_x_4632_ = v___x_4649_;
v_x_4633_ = v_tail_4635_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object* v_addOpenSimple_4659_, lean_object* v_x_4660_, lean_object* v_x_4661_){
_start:
{
uint8_t v_addOpenSimple_boxed_4662_; lean_object* v_res_4663_; 
v_addOpenSimple_boxed_4662_ = lean_unbox(v_addOpenSimple_4659_);
v_res_4663_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_boxed_4662_, v_x_4660_, v_x_4661_);
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t v_addOpenSimple_4664_, lean_object* v_as_4665_, size_t v_i_4666_, size_t v_stop_4667_, lean_object* v_b_4668_){
_start:
{
uint8_t v___x_4669_; 
v___x_4669_ = lean_usize_dec_eq(v_i_4666_, v_stop_4667_);
if (v___x_4669_ == 0)
{
lean_object* v_toParserModuleContext_4670_; lean_object* v_toInputContext_4671_; lean_object* v_toCacheableParserContext_4672_; lean_object* v_tokens_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4700_; 
v_toParserModuleContext_4670_ = lean_ctor_get(v_b_4668_, 1);
v_toInputContext_4671_ = lean_ctor_get(v_b_4668_, 0);
v_toCacheableParserContext_4672_ = lean_ctor_get(v_b_4668_, 2);
v_tokens_4673_ = lean_ctor_get(v_b_4668_, 3);
v_isSharedCheck_4700_ = !lean_is_exclusive(v_b_4668_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4675_ = v_b_4668_;
v_isShared_4676_ = v_isSharedCheck_4700_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_tokens_4673_);
lean_inc(v_toCacheableParserContext_4672_);
lean_inc(v_toParserModuleContext_4670_);
lean_inc(v_toInputContext_4671_);
lean_dec(v_b_4668_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4700_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v_env_4677_; lean_object* v_options_4678_; lean_object* v_currNamespace_4679_; lean_object* v_openDecls_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4699_; 
v_env_4677_ = lean_ctor_get(v_toParserModuleContext_4670_, 0);
v_options_4678_ = lean_ctor_get(v_toParserModuleContext_4670_, 1);
v_currNamespace_4679_ = lean_ctor_get(v_toParserModuleContext_4670_, 2);
v_openDecls_4680_ = lean_ctor_get(v_toParserModuleContext_4670_, 3);
v_isSharedCheck_4699_ = !lean_is_exclusive(v_toParserModuleContext_4670_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4682_ = v_toParserModuleContext_4670_;
v_isShared_4683_ = v_isSharedCheck_4699_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_openDecls_4680_);
lean_inc(v_currNamespace_4679_);
lean_inc(v_options_4678_);
lean_inc(v_env_4677_);
lean_dec(v_toParserModuleContext_4670_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4699_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4684_; lean_object* v_nss_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v_fst_4688_; lean_object* v_snd_4689_; lean_object* v___x_4691_; 
v___x_4684_ = lean_array_uget_borrowed(v_as_4665_, v_i_4666_);
lean_inc(v___x_4684_);
lean_inc(v_openDecls_4680_);
lean_inc(v_currNamespace_4679_);
lean_inc_ref(v_env_4677_);
v_nss_4685_ = l_Lean_ResolveName_resolveNamespace(v_env_4677_, v_currNamespace_4679_, v_openDecls_4680_, v___x_4684_);
v___x_4686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4686_, 0, v_env_4677_);
lean_ctor_set(v___x_4686_, 1, v_openDecls_4680_);
v___x_4687_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4664_, v___x_4686_, v_nss_4685_);
v_fst_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_fst_4688_);
v_snd_4689_ = lean_ctor_get(v___x_4687_, 1);
lean_inc(v_snd_4689_);
lean_dec_ref(v___x_4687_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 3, v_snd_4689_);
lean_ctor_set(v___x_4682_, 0, v_fst_4688_);
v___x_4691_ = v___x_4682_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_fst_4688_);
lean_ctor_set(v_reuseFailAlloc_4698_, 1, v_options_4678_);
lean_ctor_set(v_reuseFailAlloc_4698_, 2, v_currNamespace_4679_);
lean_ctor_set(v_reuseFailAlloc_4698_, 3, v_snd_4689_);
v___x_4691_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
lean_object* v___x_4693_; 
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 1, v___x_4691_);
v___x_4693_ = v___x_4675_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_toInputContext_4671_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v___x_4691_);
lean_ctor_set(v_reuseFailAlloc_4697_, 2, v_toCacheableParserContext_4672_);
lean_ctor_set(v_reuseFailAlloc_4697_, 3, v_tokens_4673_);
v___x_4693_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
size_t v___x_4694_; size_t v___x_4695_; 
v___x_4694_ = ((size_t)1ULL);
v___x_4695_ = lean_usize_add(v_i_4666_, v___x_4694_);
v_i_4666_ = v___x_4695_;
v_b_4668_ = v___x_4693_;
goto _start;
}
}
}
}
}
else
{
return v_b_4668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object* v_addOpenSimple_4701_, lean_object* v_as_4702_, lean_object* v_i_4703_, lean_object* v_stop_4704_, lean_object* v_b_4705_){
_start:
{
uint8_t v_addOpenSimple_boxed_4706_; size_t v_i_boxed_4707_; size_t v_stop_boxed_4708_; lean_object* v_res_4709_; 
v_addOpenSimple_boxed_4706_ = lean_unbox(v_addOpenSimple_4701_);
v_i_boxed_4707_ = lean_unbox_usize(v_i_4703_);
lean_dec(v_i_4703_);
v_stop_boxed_4708_ = lean_unbox_usize(v_stop_4704_);
lean_dec(v_stop_4704_);
v_res_4709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_boxed_4706_, v_as_4702_, v_i_boxed_4707_, v_stop_boxed_4708_, v_b_4705_);
lean_dec_ref(v_as_4702_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object* v___x_4710_, lean_object* v_ids_4711_, uint8_t v_addOpenSimple_4712_, lean_object* v_c_4713_){
_start:
{
lean_object* v___y_4715_; lean_object* v___x_4734_; lean_object* v___x_4735_; uint8_t v___x_4736_; 
v___x_4734_ = lean_unsigned_to_nat(0u);
v___x_4735_ = lean_array_get_size(v_ids_4711_);
v___x_4736_ = lean_nat_dec_lt(v___x_4734_, v___x_4735_);
if (v___x_4736_ == 0)
{
v___y_4715_ = v_c_4713_;
goto v___jp_4714_;
}
else
{
uint8_t v___x_4737_; 
v___x_4737_ = lean_nat_dec_le(v___x_4735_, v___x_4735_);
if (v___x_4737_ == 0)
{
if (v___x_4736_ == 0)
{
v___y_4715_ = v_c_4713_;
goto v___jp_4714_;
}
else
{
size_t v___x_4738_; size_t v___x_4739_; lean_object* v___x_4740_; 
v___x_4738_ = ((size_t)0ULL);
v___x_4739_ = lean_usize_of_nat(v___x_4735_);
v___x_4740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4712_, v_ids_4711_, v___x_4738_, v___x_4739_, v_c_4713_);
v___y_4715_ = v___x_4740_;
goto v___jp_4714_;
}
}
else
{
size_t v___x_4741_; size_t v___x_4742_; lean_object* v___x_4743_; 
v___x_4741_ = ((size_t)0ULL);
v___x_4742_ = lean_usize_of_nat(v___x_4735_);
v___x_4743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4712_, v_ids_4711_, v___x_4741_, v___x_4742_, v_c_4713_);
v___y_4715_ = v___x_4743_;
goto v___jp_4714_;
}
}
v___jp_4714_:
{
lean_object* v_toParserModuleContext_4716_; lean_object* v_toInputContext_4717_; lean_object* v_toCacheableParserContext_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4732_; 
v_toParserModuleContext_4716_ = lean_ctor_get(v___y_4715_, 1);
v_toInputContext_4717_ = lean_ctor_get(v___y_4715_, 0);
v_toCacheableParserContext_4718_ = lean_ctor_get(v___y_4715_, 2);
v_isSharedCheck_4732_ = !lean_is_exclusive(v___y_4715_);
if (v_isSharedCheck_4732_ == 0)
{
lean_object* v_unused_4733_; 
v_unused_4733_ = lean_ctor_get(v___y_4715_, 3);
lean_dec(v_unused_4733_);
v___x_4720_ = v___y_4715_;
v_isShared_4721_ = v_isSharedCheck_4732_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_toCacheableParserContext_4718_);
lean_inc(v_toParserModuleContext_4716_);
lean_inc(v_toInputContext_4717_);
lean_dec(v___y_4715_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4732_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v_env_4722_; lean_object* v___x_4723_; lean_object* v_ext_4724_; lean_object* v_toEnvExtension_4725_; lean_object* v_asyncMode_4726_; lean_object* v___x_4727_; lean_object* v_tokens_4728_; lean_object* v___x_4730_; 
v_env_4722_ = lean_ctor_get(v_toParserModuleContext_4716_, 0);
v___x_4723_ = l_Lean_Parser_parserExtension;
v_ext_4724_ = lean_ctor_get(v___x_4723_, 1);
v_toEnvExtension_4725_ = lean_ctor_get(v_ext_4724_, 0);
v_asyncMode_4726_ = lean_ctor_get(v_toEnvExtension_4725_, 2);
lean_inc_ref(v_env_4722_);
v___x_4727_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4710_, v___x_4723_, v_env_4722_, v_asyncMode_4726_);
v_tokens_4728_ = lean_ctor_get(v___x_4727_, 0);
lean_inc_ref(v_tokens_4728_);
lean_dec(v___x_4727_);
if (v_isShared_4721_ == 0)
{
lean_ctor_set(v___x_4720_, 3, v_tokens_4728_);
v___x_4730_ = v___x_4720_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_toInputContext_4717_);
lean_ctor_set(v_reuseFailAlloc_4731_, 1, v_toParserModuleContext_4716_);
lean_ctor_set(v_reuseFailAlloc_4731_, 2, v_toCacheableParserContext_4718_);
lean_ctor_set(v_reuseFailAlloc_4731_, 3, v_tokens_4728_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object* v___x_4744_, lean_object* v_ids_4745_, lean_object* v_addOpenSimple_4746_, lean_object* v_c_4747_){
_start:
{
uint8_t v_addOpenSimple_boxed_4748_; lean_object* v_res_4749_; 
v_addOpenSimple_boxed_4748_ = lean_unbox(v_addOpenSimple_4746_);
v_res_4749_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_4744_, v_ids_4745_, v_addOpenSimple_boxed_4748_, v_c_4747_);
lean_dec_ref(v_ids_4745_);
lean_dec_ref(v___x_4744_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* v_ids_4750_, uint8_t v_addOpenSimple_4751_, lean_object* v_p_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___f_4757_; lean_object* v___x_4758_; 
v___x_4755_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4756_ = lean_box(v_addOpenSimple_4751_);
v___f_4757_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4757_, 0, v___x_4755_);
lean_closure_set(v___f_4757_, 1, v_ids_4750_);
lean_closure_set(v___f_4757_, 2, v___x_4756_);
v___x_4758_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_4757_, v_p_4752_, v_a_4753_, v_a_4754_);
return v___x_4758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* v_ids_4759_, lean_object* v_addOpenSimple_4760_, lean_object* v_p_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_){
_start:
{
uint8_t v_addOpenSimple_boxed_4764_; lean_object* v_res_4765_; 
v_addOpenSimple_boxed_4764_ = lean_unbox(v_addOpenSimple_4760_);
v_res_4765_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_4759_, v_addOpenSimple_boxed_4764_, v_p_4761_, v_a_4762_, v_a_4763_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t v_sz_4766_, size_t v_i_4767_, lean_object* v_bs_4768_){
_start:
{
uint8_t v___x_4769_; 
v___x_4769_ = lean_usize_dec_lt(v_i_4767_, v_sz_4766_);
if (v___x_4769_ == 0)
{
return v_bs_4768_;
}
else
{
lean_object* v_v_4770_; lean_object* v___x_4771_; lean_object* v_bs_x27_4772_; lean_object* v___x_4773_; size_t v___x_4774_; size_t v___x_4775_; lean_object* v___x_4776_; 
v_v_4770_ = lean_array_uget(v_bs_4768_, v_i_4767_);
v___x_4771_ = lean_unsigned_to_nat(0u);
v_bs_x27_4772_ = lean_array_uset(v_bs_4768_, v_i_4767_, v___x_4771_);
v___x_4773_ = l_Lean_Syntax_getId(v_v_4770_);
lean_dec(v_v_4770_);
v___x_4774_ = ((size_t)1ULL);
v___x_4775_ = lean_usize_add(v_i_4767_, v___x_4774_);
v___x_4776_ = lean_array_uset(v_bs_x27_4772_, v_i_4767_, v___x_4773_);
v_i_4767_ = v___x_4775_;
v_bs_4768_ = v___x_4776_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object* v_sz_4778_, lean_object* v_i_4779_, lean_object* v_bs_4780_){
_start:
{
size_t v_sz_boxed_4781_; size_t v_i_boxed_4782_; lean_object* v_res_4783_; 
v_sz_boxed_4781_ = lean_unbox_usize(v_sz_4778_);
lean_dec(v_sz_4778_);
v_i_boxed_4782_ = lean_unbox_usize(v_i_4779_);
lean_dec(v_i_4779_);
v_res_4783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_boxed_4781_, v_i_boxed_4782_, v_bs_4780_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* v_openDeclStx_4797_, lean_object* v_p_4798_, lean_object* v_c_4799_, lean_object* v_s_4800_){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; uint8_t v___x_4803_; 
lean_inc(v_openDeclStx_4797_);
v___x_4801_ = l_Lean_Syntax_getKind(v_openDeclStx_4797_);
v___x_4802_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__2));
v___x_4803_ = lean_name_eq(v___x_4801_, v___x_4802_);
if (v___x_4803_ == 0)
{
lean_object* v___x_4804_; uint8_t v___x_4805_; 
v___x_4804_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__4));
v___x_4805_ = lean_name_eq(v___x_4801_, v___x_4804_);
lean_dec(v___x_4801_);
if (v___x_4805_ == 0)
{
lean_object* v___x_4806_; 
lean_dec(v_openDeclStx_4797_);
v___x_4806_ = lean_apply_2(v_p_4798_, v_c_4799_, v_s_4800_);
return v___x_4806_;
}
else
{
lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; size_t v_sz_4810_; size_t v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4807_ = lean_unsigned_to_nat(1u);
v___x_4808_ = l_Lean_Syntax_getArg(v_openDeclStx_4797_, v___x_4807_);
lean_dec(v_openDeclStx_4797_);
v___x_4809_ = l_Lean_Syntax_getArgs(v___x_4808_);
lean_dec(v___x_4808_);
v_sz_4810_ = lean_array_size(v___x_4809_);
v___x_4811_ = ((size_t)0ULL);
v___x_4812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4810_, v___x_4811_, v___x_4809_);
v___x_4813_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4812_, v___x_4803_, v_p_4798_, v_c_4799_, v_s_4800_);
return v___x_4813_;
}
}
else
{
lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; size_t v_sz_4817_; size_t v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
lean_dec(v___x_4801_);
v___x_4814_ = lean_unsigned_to_nat(0u);
v___x_4815_ = l_Lean_Syntax_getArg(v_openDeclStx_4797_, v___x_4814_);
lean_dec(v_openDeclStx_4797_);
v___x_4816_ = l_Lean_Syntax_getArgs(v___x_4815_);
lean_dec(v___x_4815_);
v_sz_4817_ = lean_array_size(v___x_4816_);
v___x_4818_ = ((size_t)0ULL);
v___x_4819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4817_, v___x_4818_, v___x_4816_);
v___x_4820_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4819_, v___x_4803_, v_p_4798_, v_c_4799_, v_s_4800_);
return v___x_4820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* v_p_4827_, lean_object* v_c_4828_, lean_object* v_s_4829_){
_start:
{
lean_object* v_stxStack_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; uint8_t v___x_4833_; 
v_stxStack_4830_ = lean_ctor_get(v_s_4829_, 0);
v___x_4831_ = lean_unsigned_to_nat(0u);
v___x_4832_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4830_);
v___x_4833_ = lean_nat_dec_lt(v___x_4831_, v___x_4832_);
lean_dec(v___x_4832_);
if (v___x_4833_ == 0)
{
lean_object* v___x_4834_; 
v___x_4834_ = lean_apply_2(v_p_4827_, v_c_4828_, v_s_4829_);
return v___x_4834_;
}
else
{
lean_object* v_stx_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; uint8_t v___x_4838_; 
v_stx_4835_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4830_);
lean_inc(v_stx_4835_);
v___x_4836_ = l_Lean_Syntax_getKind(v_stx_4835_);
v___x_4837_ = ((lean_object*)(l_Lean_Parser_withOpenFn___closed__1));
v___x_4838_ = lean_name_eq(v___x_4836_, v___x_4837_);
lean_dec(v___x_4836_);
if (v___x_4838_ == 0)
{
lean_object* v___x_4839_; 
lean_dec(v_stx_4835_);
v___x_4839_ = lean_apply_2(v_p_4827_, v_c_4828_, v_s_4829_);
return v___x_4839_;
}
else
{
lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4840_ = lean_unsigned_to_nat(1u);
v___x_4841_ = l_Lean_Syntax_getArg(v_stx_4835_, v___x_4840_);
lean_dec(v_stx_4835_);
v___x_4842_ = l_Lean_Parser_withOpenDeclFnCore(v___x_4841_, v_p_4827_, v_c_4828_, v_s_4829_);
return v___x_4842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* v_p_4843_){
_start:
{
lean_object* v_info_4844_; lean_object* v_fn_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4853_; 
v_info_4844_ = lean_ctor_get(v_p_4843_, 0);
v_fn_4845_ = lean_ctor_get(v_p_4843_, 1);
v_isSharedCheck_4853_ = !lean_is_exclusive(v_p_4843_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4847_ = v_p_4843_;
v_isShared_4848_ = v_isSharedCheck_4853_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_fn_4845_);
lean_inc(v_info_4844_);
lean_dec(v_p_4843_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4853_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4849_; lean_object* v___x_4851_; 
v___x_4849_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(v___x_4849_, 0, v_fn_4845_);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 1, v___x_4849_);
v___x_4851_ = v___x_4847_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_info_4844_);
lean_ctor_set(v_reuseFailAlloc_4852_, 1, v___x_4849_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* v_p_4854_, lean_object* v_c_4855_, lean_object* v_s_4856_){
_start:
{
lean_object* v_stxStack_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; uint8_t v___x_4860_; 
v_stxStack_4857_ = lean_ctor_get(v_s_4856_, 0);
v___x_4858_ = lean_unsigned_to_nat(0u);
v___x_4859_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4857_);
v___x_4860_ = lean_nat_dec_lt(v___x_4858_, v___x_4859_);
lean_dec(v___x_4859_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4861_; 
v___x_4861_ = lean_apply_2(v_p_4854_, v_c_4855_, v_s_4856_);
return v___x_4861_;
}
else
{
lean_object* v_stx_4862_; lean_object* v___x_4863_; 
v_stx_4862_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4857_);
v___x_4863_ = l_Lean_Parser_withOpenDeclFnCore(v_stx_4862_, v_p_4854_, v_c_4855_, v_s_4856_);
return v___x_4863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* v_p_4864_){
_start:
{
lean_object* v_info_4865_; lean_object* v_fn_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4874_; 
v_info_4865_ = lean_ctor_get(v_p_4864_, 0);
v_fn_4866_ = lean_ctor_get(v_p_4864_, 1);
v_isSharedCheck_4874_ = !lean_is_exclusive(v_p_4864_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4868_ = v_p_4864_;
v_isShared_4869_ = v_isSharedCheck_4874_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_fn_4866_);
lean_inc(v_info_4865_);
lean_dec(v_p_4864_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4874_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___x_4870_; lean_object* v___x_4872_; 
v___x_4870_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(v___x_4870_, 0, v_fn_4866_);
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 1, v___x_4870_);
v___x_4872_ = v___x_4868_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_info_4865_);
lean_ctor_set(v_reuseFailAlloc_4873_, 1, v___x_4870_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object* v_val_4881_){
_start:
{
lean_object* v___x_4889_; 
v___x_4889_ = l_Lean_Syntax_isStrLit_x3f(v_val_4881_);
if (lean_obj_tag(v___x_4889_) == 1)
{
lean_object* v_val_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4898_; 
v_val_4890_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4892_ = v___x_4889_;
v_isShared_4893_ = v_isSharedCheck_4898_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_val_4890_);
lean_dec(v___x_4889_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4898_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4894_; lean_object* v___x_4896_; 
v___x_4894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4894_, 0, v_val_4890_);
if (v_isShared_4893_ == 0)
{
lean_ctor_set(v___x_4892_, 0, v___x_4894_);
v___x_4896_ = v___x_4892_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v___x_4894_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
else
{
lean_object* v___x_4899_; 
lean_dec(v___x_4889_);
v___x_4899_ = l_Lean_Syntax_isNatLit_x3f(v_val_4881_);
if (lean_obj_tag(v___x_4899_) == 1)
{
lean_object* v_val_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4908_; 
v_val_4900_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4902_ = v___x_4899_;
v_isShared_4903_ = v_isSharedCheck_4908_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_val_4900_);
lean_dec(v___x_4899_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4908_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4904_; lean_object* v___x_4906_; 
v___x_4904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4904_, 0, v_val_4900_);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 0, v___x_4904_);
v___x_4906_ = v___x_4902_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v___x_4904_);
v___x_4906_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
return v___x_4906_;
}
}
}
else
{
lean_dec(v___x_4899_);
if (lean_obj_tag(v_val_4881_) == 2)
{
lean_object* v_val_4909_; lean_object* v___x_4910_; uint8_t v___x_4911_; 
v_val_4909_ = lean_ctor_get(v_val_4881_, 1);
v___x_4910_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3));
v___x_4911_ = lean_string_dec_eq(v_val_4909_, v___x_4910_);
if (v___x_4911_ == 0)
{
goto v___jp_4882_;
}
else
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4912_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4912_, 0, v___x_4911_);
v___x_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4912_);
return v___x_4913_;
}
}
else
{
goto v___jp_4882_;
}
}
}
v___jp_4882_:
{
if (lean_obj_tag(v_val_4881_) == 2)
{
lean_object* v_val_4883_; lean_object* v___x_4884_; uint8_t v___x_4885_; 
v_val_4883_ = lean_ctor_get(v_val_4881_, 1);
v___x_4884_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0));
v___x_4885_ = lean_string_dec_eq(v_val_4883_, v___x_4884_);
if (v___x_4885_ == 0)
{
lean_object* v___x_4886_; 
v___x_4886_ = lean_box(0);
return v___x_4886_;
}
else
{
lean_object* v___x_4887_; 
v___x_4887_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2));
return v___x_4887_;
}
}
else
{
lean_object* v___x_4888_; 
v___x_4888_ = lean_box(0);
return v___x_4888_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object* v_val_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_val_4914_);
lean_dec(v_val_4914_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object* v_nameStx_4916_, lean_object* v_v_4917_, lean_object* v_c_4918_){
_start:
{
lean_object* v_toParserModuleContext_4919_; lean_object* v_toInputContext_4920_; lean_object* v_toCacheableParserContext_4921_; lean_object* v_tokens_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4959_; 
v_toParserModuleContext_4919_ = lean_ctor_get(v_c_4918_, 1);
v_toInputContext_4920_ = lean_ctor_get(v_c_4918_, 0);
v_toCacheableParserContext_4921_ = lean_ctor_get(v_c_4918_, 2);
v_tokens_4922_ = lean_ctor_get(v_c_4918_, 3);
v_isSharedCheck_4959_ = !lean_is_exclusive(v_c_4918_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4924_ = v_c_4918_;
v_isShared_4925_ = v_isSharedCheck_4959_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_tokens_4922_);
lean_inc(v_toCacheableParserContext_4921_);
lean_inc(v_toParserModuleContext_4919_);
lean_inc(v_toInputContext_4920_);
lean_dec(v_c_4918_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4959_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v_env_4926_; lean_object* v_options_4927_; lean_object* v_currNamespace_4928_; lean_object* v_openDecls_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4958_; 
v_env_4926_ = lean_ctor_get(v_toParserModuleContext_4919_, 0);
v_options_4927_ = lean_ctor_get(v_toParserModuleContext_4919_, 1);
v_currNamespace_4928_ = lean_ctor_get(v_toParserModuleContext_4919_, 2);
v_openDecls_4929_ = lean_ctor_get(v_toParserModuleContext_4919_, 3);
v_isSharedCheck_4958_ = !lean_is_exclusive(v_toParserModuleContext_4919_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4931_ = v_toParserModuleContext_4919_;
v_isShared_4932_ = v_isSharedCheck_4958_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_openDecls_4929_);
lean_inc(v_currNamespace_4928_);
lean_inc(v_options_4927_);
lean_inc(v_env_4926_);
lean_dec(v_toParserModuleContext_4919_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4958_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___y_4934_; lean_object* v_map_4941_; uint8_t v_hasTrace_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4957_; 
v_map_4941_ = lean_ctor_get(v_options_4927_, 0);
v_hasTrace_4942_ = lean_ctor_get_uint8(v_options_4927_, sizeof(void*)*1);
v_isSharedCheck_4957_ = !lean_is_exclusive(v_options_4927_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4944_ = v_options_4927_;
v_isShared_4945_ = v_isSharedCheck_4957_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_map_4941_);
lean_dec(v_options_4927_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4957_;
goto v_resetjp_4943_;
}
v___jp_4933_:
{
lean_object* v___x_4936_; 
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 1, v___y_4934_);
v___x_4936_ = v___x_4931_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_env_4926_);
lean_ctor_set(v_reuseFailAlloc_4940_, 1, v___y_4934_);
lean_ctor_set(v_reuseFailAlloc_4940_, 2, v_currNamespace_4928_);
lean_ctor_set(v_reuseFailAlloc_4940_, 3, v_openDecls_4929_);
v___x_4936_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
lean_object* v___x_4938_; 
if (v_isShared_4925_ == 0)
{
lean_ctor_set(v___x_4924_, 1, v___x_4936_);
v___x_4938_ = v___x_4924_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_toInputContext_4920_);
lean_ctor_set(v_reuseFailAlloc_4939_, 1, v___x_4936_);
lean_ctor_set(v_reuseFailAlloc_4939_, 2, v_toCacheableParserContext_4921_);
lean_ctor_set(v_reuseFailAlloc_4939_, 3, v_tokens_4922_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
return v___x_4938_;
}
}
}
v_resetjp_4943_:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4946_ = l_Lean_Syntax_getId(v_nameStx_4916_);
v___x_4947_ = l_Lean_Name_eraseMacroScopes(v___x_4946_);
lean_dec(v___x_4946_);
lean_inc(v___x_4947_);
v___x_4948_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_4947_, v_v_4917_, v_map_4941_);
if (v_hasTrace_4942_ == 0)
{
lean_object* v___x_4949_; uint8_t v___x_4950_; lean_object* v___x_4952_; 
v___x_4949_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_4950_ = l_Lean_Name_isPrefixOf(v___x_4949_, v___x_4947_);
lean_dec(v___x_4947_);
if (v_isShared_4945_ == 0)
{
lean_ctor_set(v___x_4944_, 0, v___x_4948_);
v___x_4952_ = v___x_4944_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v___x_4948_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
lean_ctor_set_uint8(v___x_4952_, sizeof(void*)*1, v___x_4950_);
v___y_4934_ = v___x_4952_;
goto v___jp_4933_;
}
}
else
{
lean_object* v___x_4955_; 
lean_dec(v___x_4947_);
if (v_isShared_4945_ == 0)
{
lean_ctor_set(v___x_4944_, 0, v___x_4948_);
v___x_4955_ = v___x_4944_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v___x_4948_);
lean_ctor_set_uint8(v_reuseFailAlloc_4956_, sizeof(void*)*1, v_hasTrace_4942_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
v___y_4934_ = v___x_4955_;
goto v___jp_4933_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object* v_nameStx_4960_, lean_object* v_v_4961_, lean_object* v_c_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(v_nameStx_4960_, v_v_4961_, v_c_4962_);
lean_dec(v_nameStx_4960_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object* v_nameStx_4964_, lean_object* v_valStx_4965_, lean_object* v_p_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_){
_start:
{
lean_object* v___x_4969_; 
v___x_4969_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_valStx_4965_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v___x_4970_; 
lean_dec(v_nameStx_4964_);
v___x_4970_ = lean_apply_2(v_p_4966_, v_a_4967_, v_a_4968_);
return v___x_4970_;
}
else
{
lean_object* v_val_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v_val_4971_ = lean_ctor_get(v___x_4969_, 0);
lean_inc(v_val_4971_);
lean_dec_ref_known(v___x_4969_, 1);
v___x_4972_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed), 3, 2);
lean_closure_set(v___x_4972_, 0, v_nameStx_4964_);
lean_closure_set(v___x_4972_, 1, v_val_4971_);
v___x_4973_ = l_Lean_Parser_adaptUncacheableContextFn(v___x_4972_, v_p_4966_, v_a_4967_, v_a_4968_);
return v___x_4973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object* v_nameStx_4974_, lean_object* v_valStx_4975_, lean_object* v_p_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v_nameStx_4974_, v_valStx_4975_, v_p_4976_, v_a_4977_, v_a_4978_);
lean_dec(v_valStx_4975_);
return v_res_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object* v_p_4986_, lean_object* v_c_4987_, lean_object* v_s_4988_){
_start:
{
lean_object* v_stxStack_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; uint8_t v___x_4992_; 
v_stxStack_4989_ = lean_ctor_get(v_s_4988_, 0);
v___x_4990_ = lean_unsigned_to_nat(0u);
v___x_4991_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4989_);
v___x_4992_ = lean_nat_dec_lt(v___x_4990_, v___x_4991_);
lean_dec(v___x_4991_);
if (v___x_4992_ == 0)
{
lean_object* v___x_4993_; 
v___x_4993_ = lean_apply_2(v_p_4986_, v_c_4987_, v_s_4988_);
return v___x_4993_;
}
else
{
lean_object* v_stx_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; uint8_t v___x_4997_; 
v_stx_4994_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4989_);
lean_inc(v_stx_4994_);
v___x_4995_ = l_Lean_Syntax_getKind(v_stx_4994_);
v___x_4996_ = ((lean_object*)(l_Lean_Parser_withSetOptionFn___closed__1));
v___x_4997_ = lean_name_eq(v___x_4995_, v___x_4996_);
lean_dec(v___x_4995_);
if (v___x_4997_ == 0)
{
lean_object* v___x_4998_; 
lean_dec(v_stx_4994_);
v___x_4998_ = lean_apply_2(v_p_4986_, v_c_4987_, v_s_4988_);
return v___x_4998_;
}
else
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_4999_ = lean_unsigned_to_nat(1u);
v___x_5000_ = l_Lean_Syntax_getArg(v_stx_4994_, v___x_4999_);
v___x_5001_ = lean_unsigned_to_nat(3u);
v___x_5002_ = l_Lean_Syntax_getArg(v_stx_4994_, v___x_5001_);
lean_dec(v_stx_4994_);
v___x_5003_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5000_, v___x_5002_, v_p_4986_, v_c_4987_, v_s_4988_);
lean_dec(v___x_5002_);
return v___x_5003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object* v_p_5004_){
_start:
{
lean_object* v_info_5005_; lean_object* v_fn_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5014_; 
v_info_5005_ = lean_ctor_get(v_p_5004_, 0);
v_fn_5006_ = lean_ctor_get(v_p_5004_, 1);
v_isSharedCheck_5014_ = !lean_is_exclusive(v_p_5004_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_5008_ = v_p_5004_;
v_isShared_5009_ = v_isSharedCheck_5014_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_fn_5006_);
lean_inc(v_info_5005_);
lean_dec(v_p_5004_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5014_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5010_; lean_object* v___x_5012_; 
v___x_5010_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionFn), 3, 1);
lean_closure_set(v___x_5010_, 0, v_fn_5006_);
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 1, v___x_5010_);
v___x_5012_ = v___x_5008_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_info_5005_);
lean_ctor_set(v_reuseFailAlloc_5013_, 1, v___x_5010_);
v___x_5012_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
return v___x_5012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object* v_p_5015_, lean_object* v_c_5016_, lean_object* v_s_5017_){
_start:
{
lean_object* v_stxStack_5018_; lean_object* v_sz_5019_; lean_object* v___x_5020_; uint8_t v___x_5021_; 
v_stxStack_5018_ = lean_ctor_get(v_s_5017_, 0);
v_sz_5019_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5018_);
v___x_5020_ = lean_unsigned_to_nat(3u);
v___x_5021_ = lean_nat_dec_le(v___x_5020_, v_sz_5019_);
if (v___x_5021_ == 0)
{
lean_object* v___x_5022_; 
lean_dec(v_sz_5019_);
v___x_5022_ = lean_apply_2(v_p_5015_, v_c_5016_, v_s_5017_);
return v___x_5022_;
}
else
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5023_ = lean_nat_sub(v_sz_5019_, v___x_5020_);
lean_dec(v_sz_5019_);
v___x_5024_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5018_, v___x_5023_);
lean_dec(v___x_5023_);
v___x_5025_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5018_);
v___x_5026_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5024_, v___x_5025_, v_p_5015_, v_c_5016_, v_s_5017_);
lean_dec(v___x_5025_);
return v___x_5026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object* v_p_5027_){
_start:
{
lean_object* v_info_5028_; lean_object* v_fn_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5037_; 
v_info_5028_ = lean_ctor_get(v_p_5027_, 0);
v_fn_5029_ = lean_ctor_get(v_p_5027_, 1);
v_isSharedCheck_5037_ = !lean_is_exclusive(v_p_5027_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5031_ = v_p_5027_;
v_isShared_5032_ = v_isSharedCheck_5037_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_fn_5029_);
lean_inc(v_info_5028_);
lean_dec(v_p_5027_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5037_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5033_; lean_object* v___x_5035_; 
v___x_5033_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionValueFn), 3, 1);
lean_closure_set(v___x_5033_, 0, v_fn_5029_);
if (v_isShared_5032_ == 0)
{
lean_ctor_set(v___x_5031_, 1, v___x_5033_);
v___x_5035_ = v___x_5031_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_info_5028_);
lean_ctor_set(v_reuseFailAlloc_5036_, 1, v___x_5033_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object* v___x_5038_){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5040_ = lean_st_ref_get(v___x_5038_);
v___x_5041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5041_, 0, v___x_5040_);
return v___x_5041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v___x_5042_, lean_object* v___y_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_5042_);
lean_dec(v___x_5042_);
return v_res_5044_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5045_; lean_object* v___f_5046_; 
v___x_5045_ = l_Lean_Parser_parserAliasesRef;
v___f_5046_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5046_, 0, v___x_5045_);
return v___f_5046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___f_5048_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_);
v___x_5049_ = lean_box(0);
v___x_5050_ = lean_box(2);
v___x_5051_ = l_Lean_registerEnvExtension___redArg(v___f_5048_, v___x_5049_, v___x_5050_);
return v___x_5051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v_a_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
return v_res_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx(lean_object* v_x_5054_){
_start:
{
switch(lean_obj_tag(v_x_5054_))
{
case 0:
{
lean_object* v___x_5055_; 
v___x_5055_ = lean_unsigned_to_nat(0u);
return v___x_5055_;
}
case 1:
{
lean_object* v___x_5056_; 
v___x_5056_ = lean_unsigned_to_nat(1u);
return v___x_5056_;
}
default: 
{
lean_object* v___x_5057_; 
v___x_5057_ = lean_unsigned_to_nat(2u);
return v___x_5057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___boxed(lean_object* v_x_5058_){
_start:
{
lean_object* v_res_5059_; 
v_res_5059_ = l_Lean_Parser_ParserResolution_ctorIdx(v_x_5058_);
lean_dec_ref(v_x_5058_);
return v_res_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object* v_t_5060_, lean_object* v_k_5061_){
_start:
{
switch(lean_obj_tag(v_t_5060_))
{
case 0:
{
lean_object* v_cat_5062_; lean_object* v___x_5063_; 
v_cat_5062_ = lean_ctor_get(v_t_5060_, 0);
lean_inc(v_cat_5062_);
lean_dec_ref_known(v_t_5060_, 1);
v___x_5063_ = lean_apply_1(v_k_5061_, v_cat_5062_);
return v___x_5063_;
}
case 1:
{
lean_object* v_decl_5064_; uint8_t v_isDescr_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v_decl_5064_ = lean_ctor_get(v_t_5060_, 0);
lean_inc(v_decl_5064_);
v_isDescr_5065_ = lean_ctor_get_uint8(v_t_5060_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5060_, 1);
v___x_5066_ = lean_box(v_isDescr_5065_);
v___x_5067_ = lean_apply_2(v_k_5061_, v_decl_5064_, v___x_5066_);
return v___x_5067_;
}
default: 
{
lean_object* v_p_5068_; lean_object* v___x_5069_; 
v_p_5068_ = lean_ctor_get(v_t_5060_, 0);
lean_inc_ref(v_p_5068_);
lean_dec_ref_known(v_t_5060_, 1);
v___x_5069_ = lean_apply_1(v_k_5061_, v_p_5068_);
return v___x_5069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object* v_motive_5070_, lean_object* v_ctorIdx_5071_, lean_object* v_t_5072_, lean_object* v_h_5073_, lean_object* v_k_5074_){
_start:
{
lean_object* v___x_5075_; 
v___x_5075_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5072_, v_k_5074_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object* v_motive_5076_, lean_object* v_ctorIdx_5077_, lean_object* v_t_5078_, lean_object* v_h_5079_, lean_object* v_k_5080_){
_start:
{
lean_object* v_res_5081_; 
v_res_5081_ = l_Lean_Parser_ParserResolution_ctorElim(v_motive_5076_, v_ctorIdx_5077_, v_t_5078_, v_h_5079_, v_k_5080_);
lean_dec(v_ctorIdx_5077_);
return v_res_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object* v_t_5082_, lean_object* v_category_5083_){
_start:
{
lean_object* v___x_5084_; 
v___x_5084_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5082_, v_category_5083_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object* v_motive_5085_, lean_object* v_t_5086_, lean_object* v_h_5087_, lean_object* v_category_5088_){
_start:
{
lean_object* v___x_5089_; 
v___x_5089_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5086_, v_category_5088_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object* v_t_5090_, lean_object* v_parser_5091_){
_start:
{
lean_object* v___x_5092_; 
v___x_5092_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5090_, v_parser_5091_);
return v___x_5092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object* v_motive_5093_, lean_object* v_t_5094_, lean_object* v_h_5095_, lean_object* v_parser_5096_){
_start:
{
lean_object* v___x_5097_; 
v___x_5097_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5094_, v_parser_5096_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object* v_t_5098_, lean_object* v_alias_5099_){
_start:
{
lean_object* v___x_5100_; 
v___x_5100_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5098_, v_alias_5099_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object* v_motive_5101_, lean_object* v_t_5102_, lean_object* v_h_5103_, lean_object* v_alias_5104_){
_start:
{
lean_object* v___x_5105_; 
v___x_5105_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5102_, v_alias_5104_);
return v___x_5105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object* v_env_5109_, lean_object* v_name_5110_){
_start:
{
uint8_t v___x_5111_; lean_object* v___x_5112_; 
v___x_5111_ = 0;
v___x_5112_ = l_Lean_Environment_find_x3f(v_env_5109_, v_name_5110_, v___x_5111_);
if (lean_obj_tag(v___x_5112_) == 0)
{
lean_object* v___x_5113_; 
v___x_5113_ = lean_box(0);
return v___x_5113_;
}
else
{
lean_object* v_val_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5161_; 
v_val_5114_ = lean_ctor_get(v___x_5112_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5116_ = v___x_5112_;
v_isShared_5117_ = v_isSharedCheck_5161_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_val_5114_);
lean_dec(v___x_5112_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5161_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5118_; 
v___x_5118_ = l_Lean_ConstantInfo_type(v_val_5114_);
lean_dec(v_val_5114_);
if (lean_obj_tag(v___x_5118_) == 4)
{
lean_object* v_declName_5119_; 
v_declName_5119_ = lean_ctor_get(v___x_5118_, 0);
lean_inc(v_declName_5119_);
lean_dec_ref_known(v___x_5118_, 2);
if (lean_obj_tag(v_declName_5119_) == 1)
{
lean_object* v_pre_5120_; 
v_pre_5120_ = lean_ctor_get(v_declName_5119_, 0);
lean_inc(v_pre_5120_);
if (lean_obj_tag(v_pre_5120_) == 1)
{
lean_object* v_pre_5121_; 
v_pre_5121_ = lean_ctor_get(v_pre_5120_, 0);
switch(lean_obj_tag(v_pre_5121_))
{
case 1:
{
lean_object* v_pre_5122_; 
lean_inc_ref(v_pre_5121_);
lean_del_object(v___x_5116_);
v_pre_5122_ = lean_ctor_get(v_pre_5121_, 0);
if (lean_obj_tag(v_pre_5122_) == 0)
{
lean_object* v_str_5123_; lean_object* v_str_5124_; lean_object* v_str_5125_; lean_object* v___x_5126_; uint8_t v___x_5127_; 
v_str_5123_ = lean_ctor_get(v_declName_5119_, 1);
lean_inc_ref(v_str_5123_);
lean_dec_ref_known(v_declName_5119_, 2);
v_str_5124_ = lean_ctor_get(v_pre_5120_, 1);
lean_inc_ref(v_str_5124_);
lean_dec_ref_known(v_pre_5120_, 2);
v_str_5125_ = lean_ctor_get(v_pre_5121_, 1);
lean_inc_ref(v_str_5125_);
lean_dec_ref_known(v_pre_5121_, 2);
v___x_5126_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5127_ = lean_string_dec_eq(v_str_5125_, v___x_5126_);
lean_dec_ref(v_str_5125_);
if (v___x_5127_ == 0)
{
lean_object* v___x_5128_; 
lean_dec_ref(v_str_5124_);
lean_dec_ref(v_str_5123_);
v___x_5128_ = lean_box(0);
return v___x_5128_;
}
else
{
lean_object* v___x_5129_; uint8_t v___x_5130_; 
v___x_5129_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_5130_ = lean_string_dec_eq(v_str_5124_, v___x_5129_);
lean_dec_ref(v_str_5124_);
if (v___x_5130_ == 0)
{
lean_object* v___x_5131_; 
lean_dec_ref(v_str_5123_);
v___x_5131_ = lean_box(0);
return v___x_5131_;
}
else
{
uint8_t v___x_5132_; 
v___x_5132_ = lean_string_dec_eq(v_str_5123_, v___x_5129_);
if (v___x_5132_ == 0)
{
lean_object* v___x_5133_; uint8_t v___x_5134_; 
v___x_5133_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_5134_ = lean_string_dec_eq(v_str_5123_, v___x_5133_);
lean_dec_ref(v_str_5123_);
if (v___x_5134_ == 0)
{
lean_object* v___x_5135_; 
v___x_5135_ = lean_box(0);
return v___x_5135_;
}
else
{
lean_object* v___x_5136_; 
v___x_5136_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5136_;
}
}
else
{
lean_object* v___x_5137_; 
lean_dec_ref(v_str_5123_);
v___x_5137_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5137_;
}
}
}
}
else
{
lean_object* v___x_5138_; 
lean_dec_ref_known(v_pre_5121_, 2);
lean_dec_ref_known(v_pre_5120_, 2);
lean_dec_ref_known(v_declName_5119_, 2);
v___x_5138_ = lean_box(0);
return v___x_5138_;
}
}
case 0:
{
lean_object* v_str_5139_; lean_object* v_str_5140_; lean_object* v___x_5141_; uint8_t v___x_5142_; 
v_str_5139_ = lean_ctor_get(v_declName_5119_, 1);
lean_inc_ref(v_str_5139_);
lean_dec_ref_known(v_declName_5119_, 2);
v_str_5140_ = lean_ctor_get(v_pre_5120_, 1);
lean_inc_ref(v_str_5140_);
lean_dec_ref_known(v_pre_5120_, 2);
v___x_5141_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5142_ = lean_string_dec_eq(v_str_5140_, v___x_5141_);
lean_dec_ref(v_str_5140_);
if (v___x_5142_ == 0)
{
lean_object* v___x_5143_; 
lean_dec_ref(v_str_5139_);
lean_del_object(v___x_5116_);
v___x_5143_ = lean_box(0);
return v___x_5143_;
}
else
{
lean_object* v___x_5144_; uint8_t v___x_5145_; 
v___x_5144_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_5145_ = lean_string_dec_eq(v_str_5139_, v___x_5144_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; uint8_t v___x_5147_; 
v___x_5146_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_5147_ = lean_string_dec_eq(v_str_5139_, v___x_5146_);
lean_dec_ref(v_str_5139_);
if (v___x_5147_ == 0)
{
lean_object* v___x_5148_; 
lean_del_object(v___x_5116_);
v___x_5148_ = lean_box(0);
return v___x_5148_;
}
else
{
lean_object* v___x_5149_; lean_object* v___x_5151_; 
v___x_5149_ = lean_box(v___x_5142_);
if (v_isShared_5117_ == 0)
{
lean_ctor_set(v___x_5116_, 0, v___x_5149_);
v___x_5151_ = v___x_5116_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v___x_5153_; lean_object* v___x_5155_; 
lean_dec_ref(v_str_5139_);
v___x_5153_ = lean_box(v___x_5142_);
if (v_isShared_5117_ == 0)
{
lean_ctor_set(v___x_5116_, 0, v___x_5153_);
v___x_5155_ = v___x_5116_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5153_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
}
default: 
{
lean_object* v___x_5157_; 
lean_dec_ref_known(v_pre_5120_, 2);
lean_dec_ref_known(v_declName_5119_, 2);
lean_del_object(v___x_5116_);
v___x_5157_ = lean_box(0);
return v___x_5157_;
}
}
}
else
{
lean_object* v___x_5158_; 
lean_dec_ref_known(v_declName_5119_, 2);
lean_dec(v_pre_5120_);
lean_del_object(v___x_5116_);
v___x_5158_ = lean_box(0);
return v___x_5158_;
}
}
else
{
lean_object* v___x_5159_; 
lean_dec(v_declName_5119_);
lean_del_object(v___x_5116_);
v___x_5159_ = lean_box(0);
return v___x_5159_;
}
}
else
{
lean_object* v___x_5160_; 
lean_dec_ref(v___x_5118_);
lean_del_object(v___x_5116_);
v___x_5160_ = lean_box(0);
return v___x_5160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object* v_env_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_){
_start:
{
if (lean_obj_tag(v_a_5163_) == 0)
{
lean_object* v___x_5165_; 
lean_dec_ref(v_env_5162_);
v___x_5165_ = lean_array_to_list(v_a_5164_);
return v___x_5165_;
}
else
{
lean_object* v_head_5166_; lean_object* v_snd_5167_; 
v_head_5166_ = lean_ctor_get(v_a_5163_, 0);
v_snd_5167_ = lean_ctor_get(v_head_5166_, 1);
if (lean_obj_tag(v_snd_5167_) == 0)
{
lean_object* v_tail_5168_; lean_object* v_fst_5169_; lean_object* v___x_5170_; 
lean_inc(v_head_5166_);
v_tail_5168_ = lean_ctor_get(v_a_5163_, 1);
lean_inc(v_tail_5168_);
lean_dec_ref_known(v_a_5163_, 2);
v_fst_5169_ = lean_ctor_get(v_head_5166_, 0);
lean_inc_n(v_fst_5169_, 2);
lean_dec(v_head_5166_);
lean_inc_ref(v_env_5162_);
v___x_5170_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5162_, v_fst_5169_);
if (lean_obj_tag(v___x_5170_) == 0)
{
lean_dec(v_fst_5169_);
v_a_5163_ = v_tail_5168_;
goto _start;
}
else
{
lean_object* v_val_5172_; lean_object* v___x_5173_; uint8_t v___x_5174_; lean_object* v___x_5175_; 
v_val_5172_ = lean_ctor_get(v___x_5170_, 0);
lean_inc(v_val_5172_);
lean_dec_ref_known(v___x_5170_, 1);
v___x_5173_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5173_, 0, v_fst_5169_);
v___x_5174_ = lean_unbox(v_val_5172_);
lean_dec(v_val_5172_);
lean_ctor_set_uint8(v___x_5173_, sizeof(void*)*1, v___x_5174_);
v___x_5175_ = lean_array_push(v_a_5164_, v___x_5173_);
v_a_5163_ = v_tail_5168_;
v_a_5164_ = v___x_5175_;
goto _start;
}
}
else
{
lean_object* v_tail_5177_; 
v_tail_5177_ = lean_ctor_get(v_a_5163_, 1);
lean_inc(v_tail_5177_);
lean_dec_ref_known(v_a_5163_, 2);
v_a_5163_ = v_tail_5177_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object* v_env_5182_, lean_object* v_as_x27_5183_, lean_object* v_b_5184_){
_start:
{
if (lean_obj_tag(v_as_x27_5183_) == 0)
{
lean_dec_ref(v_env_5182_);
lean_inc_ref(v_b_5184_);
return v_b_5184_;
}
else
{
lean_object* v_head_5185_; lean_object* v_tail_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
v_head_5185_ = lean_ctor_get(v_as_x27_5183_, 0);
v_tail_5186_ = lean_ctor_get(v_as_x27_5183_, 1);
v___x_5187_ = lean_box(0);
v___x_5188_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_5185_) == 1)
{
lean_object* v_fields_5189_; 
v_fields_5189_ = lean_ctor_get(v_head_5185_, 1);
if (lean_obj_tag(v_fields_5189_) == 0)
{
lean_object* v_n_5190_; lean_object* v___x_5191_; 
v_n_5190_ = lean_ctor_get(v_head_5185_, 0);
lean_inc(v_n_5190_);
lean_inc_ref(v_env_5182_);
v___x_5191_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5182_, v_n_5190_);
if (lean_obj_tag(v___x_5191_) == 1)
{
lean_object* v_val_5192_; lean_object* v___x_5194_; uint8_t v_isShared_5195_; uint8_t v_isSharedCheck_5204_; 
lean_dec_ref(v_env_5182_);
v_val_5192_ = lean_ctor_get(v___x_5191_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5191_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5194_ = v___x_5191_;
v_isShared_5195_ = v_isSharedCheck_5204_;
goto v_resetjp_5193_;
}
else
{
lean_inc(v_val_5192_);
lean_dec(v___x_5191_);
v___x_5194_ = lean_box(0);
v_isShared_5195_ = v_isSharedCheck_5204_;
goto v_resetjp_5193_;
}
v_resetjp_5193_:
{
lean_object* v___x_5196_; uint8_t v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5201_; 
lean_inc(v_n_5190_);
v___x_5196_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5196_, 0, v_n_5190_);
v___x_5197_ = lean_unbox(v_val_5192_);
lean_dec(v_val_5192_);
lean_ctor_set_uint8(v___x_5196_, sizeof(void*)*1, v___x_5197_);
v___x_5198_ = lean_box(0);
v___x_5199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5196_);
lean_ctor_set(v___x_5199_, 1, v___x_5198_);
if (v_isShared_5195_ == 0)
{
lean_ctor_set(v___x_5194_, 0, v___x_5199_);
v___x_5201_ = v___x_5194_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v___x_5199_);
v___x_5201_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
lean_object* v___x_5202_; 
v___x_5202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5202_, 0, v___x_5201_);
lean_ctor_set(v___x_5202_, 1, v___x_5187_);
return v___x_5202_;
}
}
}
else
{
lean_dec(v___x_5191_);
v_as_x27_5183_ = v_tail_5186_;
v_b_5184_ = v___x_5188_;
goto _start;
}
}
else
{
v_as_x27_5183_ = v_tail_5186_;
v_b_5184_ = v___x_5188_;
goto _start;
}
}
else
{
v_as_x27_5183_ = v_tail_5186_;
v_b_5184_ = v___x_5188_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object* v_env_5208_, lean_object* v_as_x27_5209_, lean_object* v_b_5210_){
_start:
{
lean_object* v_res_5211_; 
v_res_5211_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5208_, v_as_x27_5209_, v_b_5210_);
lean_dec_ref(v_b_5210_);
lean_dec(v_as_x27_5209_);
return v_res_5211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object* v_env_5214_, lean_object* v_opts_5215_, lean_object* v_currNamespace_5216_, lean_object* v_openDecls_5217_, lean_object* v_ident_5218_){
_start:
{
if (lean_obj_tag(v_ident_5218_) == 3)
{
lean_object* v_val_5219_; lean_object* v_preresolved_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v_fst_5223_; lean_object* v___x_5225_; uint8_t v_isShared_5226_; uint8_t v_isSharedCheck_5258_; 
v_val_5219_ = lean_ctor_get(v_ident_5218_, 2);
lean_inc(v_val_5219_);
v_preresolved_5220_ = lean_ctor_get(v_ident_5218_, 3);
lean_inc(v_preresolved_5220_);
lean_dec_ref_known(v_ident_5218_, 4);
v___x_5221_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
lean_inc_ref(v_env_5214_);
v___x_5222_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5214_, v_preresolved_5220_, v___x_5221_);
lean_dec(v_preresolved_5220_);
v_fst_5223_ = lean_ctor_get(v___x_5222_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5222_);
if (v_isSharedCheck_5258_ == 0)
{
lean_object* v_unused_5259_; 
v_unused_5259_ = lean_ctor_get(v___x_5222_, 1);
lean_dec(v_unused_5259_);
v___x_5225_ = v___x_5222_;
v_isShared_5226_ = v_isSharedCheck_5258_;
goto v_resetjp_5224_;
}
else
{
lean_inc(v_fst_5223_);
lean_dec(v___x_5222_);
v___x_5225_ = lean_box(0);
v_isShared_5226_ = v_isSharedCheck_5258_;
goto v_resetjp_5224_;
}
v_resetjp_5224_:
{
if (lean_obj_tag(v_fst_5223_) == 0)
{
lean_object* v___x_5227_; uint8_t v___x_5228_; 
v___x_5227_ = l_Lean_Name_eraseMacroScopes(v_val_5219_);
lean_inc_ref(v_env_5214_);
v___x_5228_ = l_Lean_Parser_isParserCategory(v_env_5214_, v___x_5227_);
if (v___x_5228_ == 0)
{
lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; uint8_t v___x_5232_; 
lean_inc_ref_n(v_env_5214_, 2);
v___x_5229_ = l_Lean_ResolveName_resolveGlobalName(v_env_5214_, v_opts_5215_, v_currNamespace_5216_, v_openDecls_5217_, v_val_5219_);
v___x_5230_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0));
v___x_5231_ = l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(v_env_5214_, v___x_5229_, v___x_5230_);
v___x_5232_ = l_List_isEmpty___redArg(v___x_5231_);
if (v___x_5232_ == 0)
{
lean_dec(v___x_5227_);
lean_del_object(v___x_5225_);
lean_dec_ref(v_env_5214_);
return v___x_5231_;
}
else
{
lean_object* v___x_5233_; lean_object* v_asyncMode_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; 
lean_dec(v___x_5231_);
v___x_5233_ = l_Lean_Parser_aliasExtension;
v_asyncMode_5234_ = lean_ctor_get(v___x_5233_, 2);
v___x_5235_ = lean_box(1);
v___x_5236_ = lean_box(0);
v___x_5237_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5235_, v___x_5233_, v_env_5214_, v_asyncMode_5234_, v___x_5236_);
v___x_5238_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5237_, v___x_5227_);
lean_dec(v___x_5227_);
lean_dec(v___x_5237_);
if (lean_obj_tag(v___x_5238_) == 1)
{
lean_object* v_val_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5250_; 
v_val_5239_ = lean_ctor_get(v___x_5238_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5238_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5241_ = v___x_5238_;
v_isShared_5242_ = v_isSharedCheck_5250_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_val_5239_);
lean_dec(v___x_5238_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5250_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5244_; 
if (v_isShared_5242_ == 0)
{
lean_ctor_set_tag(v___x_5241_, 2);
v___x_5244_ = v___x_5241_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_val_5239_);
v___x_5244_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
lean_object* v___x_5245_; lean_object* v___x_5247_; 
v___x_5245_ = lean_box(0);
if (v_isShared_5226_ == 0)
{
lean_ctor_set_tag(v___x_5225_, 1);
lean_ctor_set(v___x_5225_, 1, v___x_5245_);
lean_ctor_set(v___x_5225_, 0, v___x_5244_);
v___x_5247_ = v___x_5225_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v___x_5244_);
lean_ctor_set(v_reuseFailAlloc_5248_, 1, v___x_5245_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
}
}
}
}
else
{
lean_object* v___x_5251_; 
lean_dec(v___x_5238_);
lean_del_object(v___x_5225_);
v___x_5251_ = lean_box(0);
return v___x_5251_;
}
}
}
else
{
lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5255_; 
lean_dec(v_val_5219_);
lean_dec(v_openDecls_5217_);
lean_dec(v_currNamespace_5216_);
lean_dec_ref(v_env_5214_);
v___x_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5227_);
v___x_5253_ = lean_box(0);
if (v_isShared_5226_ == 0)
{
lean_ctor_set_tag(v___x_5225_, 1);
lean_ctor_set(v___x_5225_, 1, v___x_5253_);
lean_ctor_set(v___x_5225_, 0, v___x_5252_);
v___x_5255_ = v___x_5225_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v___x_5252_);
lean_ctor_set(v_reuseFailAlloc_5256_, 1, v___x_5253_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
else
{
lean_object* v_val_5257_; 
lean_del_object(v___x_5225_);
lean_dec(v_val_5219_);
lean_dec(v_openDecls_5217_);
lean_dec(v_currNamespace_5216_);
lean_dec_ref(v_env_5214_);
v_val_5257_ = lean_ctor_get(v_fst_5223_, 0);
lean_inc(v_val_5257_);
lean_dec_ref_known(v_fst_5223_, 1);
return v_val_5257_;
}
}
}
else
{
lean_object* v___x_5260_; 
lean_dec(v_ident_5218_);
lean_dec(v_openDecls_5217_);
lean_dec(v_currNamespace_5216_);
lean_dec_ref(v_env_5214_);
v___x_5260_ = lean_box(0);
return v___x_5260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object* v_env_5261_, lean_object* v_opts_5262_, lean_object* v_currNamespace_5263_, lean_object* v_openDecls_5264_, lean_object* v_ident_5265_){
_start:
{
lean_object* v_res_5266_; 
v_res_5266_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5261_, v_opts_5262_, v_currNamespace_5263_, v_openDecls_5264_, v_ident_5265_);
lean_dec_ref(v_opts_5262_);
return v_res_5266_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object* v_env_5267_, lean_object* v_as_5268_, lean_object* v_as_x27_5269_, lean_object* v_b_5270_, lean_object* v_a_5271_){
_start:
{
lean_object* v___x_5272_; 
v___x_5272_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5267_, v_as_x27_5269_, v_b_5270_);
return v___x_5272_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object* v_env_5273_, lean_object* v_as_5274_, lean_object* v_as_x27_5275_, lean_object* v_b_5276_, lean_object* v_a_5277_){
_start:
{
lean_object* v_res_5278_; 
v_res_5278_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(v_env_5273_, v_as_5274_, v_as_x27_5275_, v_b_5276_, v_a_5277_);
lean_dec_ref(v_b_5276_);
lean_dec(v_as_x27_5275_);
lean_dec(v_as_5274_);
return v_res_5278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object* v_ctx_5279_, lean_object* v_id_5280_, uint8_t v_unsetExporting_5281_){
_start:
{
lean_object* v___y_5283_; 
if (v_unsetExporting_5281_ == 0)
{
lean_object* v_toParserModuleContext_5289_; lean_object* v_env_5290_; 
v_toParserModuleContext_5289_ = lean_ctor_get(v_ctx_5279_, 1);
v_env_5290_ = lean_ctor_get(v_toParserModuleContext_5289_, 0);
lean_inc_ref(v_env_5290_);
v___y_5283_ = v_env_5290_;
goto v___jp_5282_;
}
else
{
lean_object* v_toParserModuleContext_5291_; lean_object* v_env_5292_; uint8_t v___x_5293_; lean_object* v___x_5294_; 
v_toParserModuleContext_5291_ = lean_ctor_get(v_ctx_5279_, 1);
v_env_5292_ = lean_ctor_get(v_toParserModuleContext_5291_, 0);
v___x_5293_ = 0;
lean_inc_ref(v_env_5292_);
v___x_5294_ = l_Lean_Environment_setExporting(v_env_5292_, v___x_5293_);
v___y_5283_ = v___x_5294_;
goto v___jp_5282_;
}
v___jp_5282_:
{
lean_object* v_toParserModuleContext_5284_; lean_object* v_options_5285_; lean_object* v_currNamespace_5286_; lean_object* v_openDecls_5287_; lean_object* v___x_5288_; 
v_toParserModuleContext_5284_ = lean_ctor_get(v_ctx_5279_, 1);
lean_inc_ref(v_toParserModuleContext_5284_);
lean_dec_ref(v_ctx_5279_);
v_options_5285_ = lean_ctor_get(v_toParserModuleContext_5284_, 1);
lean_inc_ref(v_options_5285_);
v_currNamespace_5286_ = lean_ctor_get(v_toParserModuleContext_5284_, 2);
lean_inc(v_currNamespace_5286_);
v_openDecls_5287_ = lean_ctor_get(v_toParserModuleContext_5284_, 3);
lean_inc(v_openDecls_5287_);
lean_dec_ref(v_toParserModuleContext_5284_);
v___x_5288_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v___y_5283_, v_options_5285_, v_currNamespace_5286_, v_openDecls_5287_, v_id_5280_);
lean_dec_ref(v_options_5285_);
return v___x_5288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object* v_ctx_5295_, lean_object* v_id_5296_, lean_object* v_unsetExporting_5297_){
_start:
{
uint8_t v_unsetExporting_boxed_5298_; lean_object* v_res_5299_; 
v_unsetExporting_boxed_5298_ = lean_unbox(v_unsetExporting_5297_);
v_res_5299_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5295_, v_id_5296_, v_unsetExporting_boxed_5298_);
return v_res_5299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object* v_id_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_){
_start:
{
lean_object* v___x_5304_; lean_object* v_env_5305_; lean_object* v_options_5306_; lean_object* v_currNamespace_5307_; lean_object* v_openDecls_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; 
v___x_5304_ = lean_st_ref_get(v_a_5302_);
v_env_5305_ = lean_ctor_get(v___x_5304_, 0);
lean_inc_ref(v_env_5305_);
lean_dec(v___x_5304_);
v_options_5306_ = lean_ctor_get(v_a_5301_, 2);
v_currNamespace_5307_ = lean_ctor_get(v_a_5301_, 6);
v_openDecls_5308_ = lean_ctor_get(v_a_5301_, 7);
lean_inc(v_openDecls_5308_);
lean_inc(v_currNamespace_5307_);
v___x_5309_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5305_, v_options_5306_, v_currNamespace_5307_, v_openDecls_5308_, v_id_5300_);
v___x_5310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5310_, 0, v___x_5309_);
return v___x_5310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object* v_id_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = l_Lean_Parser_resolveParserName(v_id_5311_, v_a_5312_, v_a_5313_);
lean_dec(v_a_5313_);
lean_dec_ref(v_a_5312_);
return v_res_5315_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object* v_x_5316_, lean_object* v_x_5317_){
_start:
{
if (lean_obj_tag(v_x_5316_) == 0)
{
if (lean_obj_tag(v_x_5317_) == 0)
{
uint8_t v___x_5318_; 
v___x_5318_ = 1;
return v___x_5318_;
}
else
{
uint8_t v___x_5319_; 
v___x_5319_ = 0;
return v___x_5319_;
}
}
else
{
if (lean_obj_tag(v_x_5317_) == 0)
{
uint8_t v___x_5320_; 
v___x_5320_ = 0;
return v___x_5320_;
}
else
{
lean_object* v_val_5321_; lean_object* v_val_5322_; uint8_t v___x_5323_; 
v_val_5321_ = lean_ctor_get(v_x_5316_, 0);
v_val_5322_ = lean_ctor_get(v_x_5317_, 0);
v___x_5323_ = l_Lean_Parser_instBEqError_beq(v_val_5321_, v_val_5322_);
return v___x_5323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object* v_x_5324_, lean_object* v_x_5325_){
_start:
{
uint8_t v_res_5326_; lean_object* v_r_5327_; 
v_res_5326_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5324_, v_x_5325_);
lean_dec(v_x_5325_);
lean_dec(v_x_5324_);
v_r_5327_ = lean_box(v_res_5326_);
return v_r_5327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t v___x_5328_, lean_object* v_ctx_5329_){
_start:
{
lean_object* v_toParserModuleContext_5330_; lean_object* v_toInputContext_5331_; lean_object* v_toCacheableParserContext_5332_; lean_object* v_tokens_5333_; lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5358_; 
v_toParserModuleContext_5330_ = lean_ctor_get(v_ctx_5329_, 1);
v_toInputContext_5331_ = lean_ctor_get(v_ctx_5329_, 0);
v_toCacheableParserContext_5332_ = lean_ctor_get(v_ctx_5329_, 2);
v_tokens_5333_ = lean_ctor_get(v_ctx_5329_, 3);
v_isSharedCheck_5358_ = !lean_is_exclusive(v_ctx_5329_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5335_ = v_ctx_5329_;
v_isShared_5336_ = v_isSharedCheck_5358_;
goto v_resetjp_5334_;
}
else
{
lean_inc(v_tokens_5333_);
lean_inc(v_toCacheableParserContext_5332_);
lean_inc(v_toParserModuleContext_5330_);
lean_inc(v_toInputContext_5331_);
lean_dec(v_ctx_5329_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5358_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v_env_5337_; lean_object* v_options_5338_; lean_object* v_currNamespace_5339_; lean_object* v_openDecls_5340_; lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5357_; 
v_env_5337_ = lean_ctor_get(v_toParserModuleContext_5330_, 0);
v_options_5338_ = lean_ctor_get(v_toParserModuleContext_5330_, 1);
v_currNamespace_5339_ = lean_ctor_get(v_toParserModuleContext_5330_, 2);
v_openDecls_5340_ = lean_ctor_get(v_toParserModuleContext_5330_, 3);
v_isSharedCheck_5357_ = !lean_is_exclusive(v_toParserModuleContext_5330_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5342_ = v_toParserModuleContext_5330_;
v_isShared_5343_ = v_isSharedCheck_5357_;
goto v_resetjp_5341_;
}
else
{
lean_inc(v_openDecls_5340_);
lean_inc(v_currNamespace_5339_);
lean_inc(v_options_5338_);
lean_inc(v_env_5337_);
lean_dec(v_toParserModuleContext_5330_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5357_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
lean_object* v___x_5344_; uint8_t v___y_5346_; lean_object* v___x_5354_; uint8_t v___x_5355_; 
v___x_5344_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_5354_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_5355_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_5338_, v___x_5354_);
if (v___x_5355_ == 0)
{
uint8_t v___x_5356_; 
v___x_5356_ = 1;
v___y_5346_ = v___x_5356_;
goto v___jp_5345_;
}
else
{
v___y_5346_ = v___x_5328_;
goto v___jp_5345_;
}
v___jp_5345_:
{
lean_object* v___x_5347_; lean_object* v___x_5349_; 
v___x_5347_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_5338_, v___x_5344_, v___y_5346_);
if (v_isShared_5343_ == 0)
{
lean_ctor_set(v___x_5342_, 1, v___x_5347_);
v___x_5349_ = v___x_5342_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_env_5337_);
lean_ctor_set(v_reuseFailAlloc_5353_, 1, v___x_5347_);
lean_ctor_set(v_reuseFailAlloc_5353_, 2, v_currNamespace_5339_);
lean_ctor_set(v_reuseFailAlloc_5353_, 3, v_openDecls_5340_);
v___x_5349_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
lean_object* v___x_5351_; 
if (v_isShared_5336_ == 0)
{
lean_ctor_set(v___x_5335_, 1, v___x_5349_);
v___x_5351_ = v___x_5335_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_toInputContext_5331_);
lean_ctor_set(v_reuseFailAlloc_5352_, 1, v___x_5349_);
lean_ctor_set(v_reuseFailAlloc_5352_, 2, v_toCacheableParserContext_5332_);
lean_ctor_set(v_reuseFailAlloc_5352_, 3, v_tokens_5333_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object* v___x_5359_, lean_object* v_ctx_5360_){
_start:
{
uint8_t v___x_1088__boxed_5361_; lean_object* v_res_5362_; 
v___x_1088__boxed_5361_ = lean_unbox(v___x_5359_);
v_res_5362_ = l_Lean_Parser_parserOfStackFn___lam__0(v___x_1088__boxed_5361_, v_ctx_5360_);
return v_res_5362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* v_offset_5370_, lean_object* v_ctx_5371_, lean_object* v_s_5372_){
_start:
{
lean_object* v_stxStack_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; uint8_t v___x_5377_; 
v_stxStack_5373_ = lean_ctor_get(v_s_5372_, 0);
v___x_5374_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5373_);
v___x_5375_ = lean_unsigned_to_nat(1u);
v___x_5376_ = lean_nat_add(v_offset_5370_, v___x_5375_);
v___x_5377_ = lean_nat_dec_lt(v___x_5374_, v___x_5376_);
lean_dec(v___x_5376_);
if (v___x_5377_ == 0)
{
lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; 
v___x_5378_ = lean_nat_sub(v___x_5374_, v_offset_5370_);
lean_dec(v___x_5374_);
v___x_5379_ = lean_nat_sub(v___x_5378_, v___x_5375_);
lean_dec(v___x_5378_);
v___x_5380_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5373_, v___x_5379_);
lean_dec(v___x_5379_);
if (lean_obj_tag(v___x_5380_) == 3)
{
uint8_t v___x_5392_; lean_object* v___x_5393_; 
v___x_5392_ = 1;
lean_inc_ref(v___x_5380_);
lean_inc_ref(v_ctx_5371_);
v___x_5393_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5371_, v___x_5380_, v___x_5392_);
if (lean_obj_tag(v___x_5393_) == 0)
{
lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
lean_dec_ref(v_ctx_5371_);
v___x_5394_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__1));
v___x_5395_ = lean_box(0);
v___x_5396_ = l_Lean_Syntax_formatStx(v___x_5380_, v___x_5395_, v___x_5377_);
v___x_5397_ = l_Std_Format_defWidth;
v___x_5398_ = lean_unsigned_to_nat(0u);
v___x_5399_ = l_Std_Format_pretty(v___x_5396_, v___x_5397_, v___x_5398_, v___x_5398_);
v___x_5400_ = lean_string_append(v___x_5394_, v___x_5399_);
lean_dec_ref(v___x_5399_);
v___x_5401_ = lean_box(0);
v___x_5402_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5372_, v___x_5400_, v___x_5401_, v___x_5392_);
return v___x_5402_;
}
else
{
lean_object* v_head_5403_; lean_object* v_tail_5404_; lean_object* v_iniSz_5405_; lean_object* v_s_5407_; 
v_head_5403_ = lean_ctor_get(v___x_5393_, 0);
lean_inc(v_head_5403_);
v_tail_5404_ = lean_ctor_get(v___x_5393_, 1);
lean_inc(v_tail_5404_);
lean_dec_ref_known(v___x_5393_, 2);
v_iniSz_5405_ = l_Lean_Parser_ParserState_stackSize(v_s_5372_);
switch(lean_obj_tag(v_head_5403_))
{
case 0:
{
if (lean_obj_tag(v_tail_5404_) == 0)
{
lean_object* v_cat_5417_; lean_object* v___x_5418_; 
lean_dec_ref_known(v___x_5380_, 4);
v_cat_5417_ = lean_ctor_get(v_head_5403_, 0);
lean_inc(v_cat_5417_);
lean_dec_ref_known(v_head_5403_, 1);
v___x_5418_ = l_Lean_Parser_categoryParserFn(v_cat_5417_, v_ctx_5371_, v_s_5372_);
v_s_5407_ = v___x_5418_;
goto v___jp_5406_;
}
else
{
lean_dec_ref_known(v_tail_5404_, 2);
lean_dec_ref_known(v_head_5403_, 1);
lean_dec(v_iniSz_5405_);
lean_dec_ref(v_ctx_5371_);
goto v___jp_5381_;
}
}
case 1:
{
if (lean_obj_tag(v_tail_5404_) == 0)
{
lean_object* v_decl_5419_; lean_object* v___x_5420_; lean_object* v___f_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; 
lean_dec_ref_known(v___x_5380_, 4);
v_decl_5419_ = lean_ctor_get(v_head_5403_, 0);
lean_inc(v_decl_5419_);
lean_dec_ref_known(v_head_5403_, 1);
v___x_5420_ = lean_box(v___x_5377_);
v___f_5421_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5421_, 0, v___x_5420_);
v___x_5422_ = lean_box(0);
v___x_5423_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_5423_, 0, v_decl_5419_);
lean_closure_set(v___x_5423_, 1, v___x_5422_);
v___x_5424_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5421_, v___x_5423_, v_ctx_5371_, v_s_5372_);
v_s_5407_ = v___x_5424_;
goto v___jp_5406_;
}
else
{
lean_dec_ref_known(v_tail_5404_, 2);
lean_dec_ref_known(v_head_5403_, 1);
lean_dec(v_iniSz_5405_);
lean_dec_ref(v_ctx_5371_);
goto v___jp_5381_;
}
}
default: 
{
if (lean_obj_tag(v_tail_5404_) == 0)
{
lean_object* v_p_5425_; 
v_p_5425_ = lean_ctor_get(v_head_5403_, 0);
lean_inc_ref(v_p_5425_);
lean_dec_ref_known(v_head_5403_, 1);
if (lean_obj_tag(v_p_5425_) == 0)
{
lean_object* v_p_5426_; lean_object* v_fn_5427_; lean_object* v___x_5428_; 
lean_dec_ref_known(v___x_5380_, 4);
v_p_5426_ = lean_ctor_get(v_p_5425_, 0);
lean_inc(v_p_5426_);
lean_dec_ref_known(v_p_5425_, 1);
v_fn_5427_ = lean_ctor_get(v_p_5426_, 1);
lean_inc_ref(v_fn_5427_);
lean_dec(v_p_5426_);
v___x_5428_ = lean_apply_2(v_fn_5427_, v_ctx_5371_, v_s_5372_);
v_s_5407_ = v___x_5428_;
goto v___jp_5406_;
}
else
{
lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; 
lean_dec_ref(v_p_5425_);
lean_dec(v_iniSz_5405_);
lean_dec_ref(v_ctx_5371_);
v___x_5429_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__3));
v___x_5430_ = lean_box(0);
v___x_5431_ = l_Lean_Syntax_formatStx(v___x_5380_, v___x_5430_, v___x_5377_);
v___x_5432_ = l_Std_Format_defWidth;
v___x_5433_ = lean_unsigned_to_nat(0u);
v___x_5434_ = l_Std_Format_pretty(v___x_5431_, v___x_5432_, v___x_5433_, v___x_5433_);
v___x_5435_ = lean_string_append(v___x_5429_, v___x_5434_);
lean_dec_ref(v___x_5434_);
v___x_5436_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__4));
v___x_5437_ = lean_string_append(v___x_5435_, v___x_5436_);
v___x_5438_ = lean_box(0);
v___x_5439_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5372_, v___x_5437_, v___x_5438_, v___x_5392_);
return v___x_5439_;
}
}
else
{
lean_dec_ref_known(v_tail_5404_, 2);
lean_dec_ref_known(v_head_5403_, 1);
lean_dec(v_iniSz_5405_);
lean_dec_ref(v_ctx_5371_);
goto v___jp_5381_;
}
}
}
v___jp_5406_:
{
lean_object* v_errorMsg_5408_; lean_object* v___x_5409_; uint8_t v___x_5410_; 
v_errorMsg_5408_ = lean_ctor_get(v_s_5407_, 4);
v___x_5409_ = lean_box(0);
v___x_5410_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_errorMsg_5408_, v___x_5409_);
if (v___x_5410_ == 0)
{
lean_dec(v_iniSz_5405_);
return v_s_5407_;
}
else
{
lean_object* v___x_5411_; lean_object* v___x_5412_; uint8_t v___x_5413_; 
v___x_5411_ = l_Lean_Parser_ParserState_stackSize(v_s_5407_);
v___x_5412_ = lean_nat_add(v_iniSz_5405_, v___x_5375_);
lean_dec(v_iniSz_5405_);
v___x_5413_ = lean_nat_dec_eq(v___x_5411_, v___x_5412_);
lean_dec(v___x_5412_);
lean_dec(v___x_5411_);
if (v___x_5413_ == 0)
{
lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; 
v___x_5414_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__2));
v___x_5415_ = lean_box(0);
v___x_5416_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5407_, v___x_5414_, v___x_5415_, v___x_5410_);
return v___x_5416_;
}
else
{
return v_s_5407_;
}
}
}
}
}
else
{
lean_object* v___x_5440_; lean_object* v___x_5441_; uint8_t v___x_5442_; lean_object* v___x_5443_; 
lean_dec(v___x_5380_);
lean_dec_ref(v_ctx_5371_);
v___x_5440_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__5));
v___x_5441_ = lean_box(0);
v___x_5442_ = 1;
v___x_5443_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5372_, v___x_5440_, v___x_5441_, v___x_5442_);
return v___x_5443_;
}
v___jp_5381_:
{
lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; uint8_t v___x_5390_; lean_object* v___x_5391_; 
v___x_5382_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__0));
v___x_5383_ = lean_box(0);
v___x_5384_ = l_Lean_Syntax_formatStx(v___x_5380_, v___x_5383_, v___x_5377_);
v___x_5385_ = l_Std_Format_defWidth;
v___x_5386_ = lean_unsigned_to_nat(0u);
v___x_5387_ = l_Std_Format_pretty(v___x_5384_, v___x_5385_, v___x_5386_, v___x_5386_);
v___x_5388_ = lean_string_append(v___x_5382_, v___x_5387_);
lean_dec_ref(v___x_5387_);
v___x_5389_ = lean_box(0);
v___x_5390_ = 1;
v___x_5391_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5372_, v___x_5388_, v___x_5389_, v___x_5390_);
return v___x_5391_;
}
}
else
{
lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
lean_dec(v___x_5374_);
lean_dec_ref(v_ctx_5371_);
v___x_5444_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__6));
v___x_5445_ = lean_box(0);
v___x_5446_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5372_, v___x_5444_, v___x_5445_, v___x_5377_);
return v___x_5446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* v_offset_5447_, lean_object* v_ctx_5448_, lean_object* v_s_5449_){
_start:
{
lean_object* v_res_5450_; 
v_res_5450_ = l_Lean_Parser_parserOfStackFn(v_offset_5447_, v_ctx_5448_, v_s_5449_);
lean_dec(v_offset_5447_);
return v_res_5450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object* v_prec_5451_, lean_object* v_x_5452_){
_start:
{
lean_object* v_quotDepth_5453_; uint8_t v_suppressInsideQuot_5454_; lean_object* v_savedPos_x3f_5455_; lean_object* v_forbiddenTks_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5463_; 
v_quotDepth_5453_ = lean_ctor_get(v_x_5452_, 1);
v_suppressInsideQuot_5454_ = lean_ctor_get_uint8(v_x_5452_, sizeof(void*)*4);
v_savedPos_x3f_5455_ = lean_ctor_get(v_x_5452_, 2);
v_forbiddenTks_5456_ = lean_ctor_get(v_x_5452_, 3);
v_isSharedCheck_5463_ = !lean_is_exclusive(v_x_5452_);
if (v_isSharedCheck_5463_ == 0)
{
lean_object* v_unused_5464_; 
v_unused_5464_ = lean_ctor_get(v_x_5452_, 0);
lean_dec(v_unused_5464_);
v___x_5458_ = v_x_5452_;
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_forbiddenTks_5456_);
lean_inc(v_savedPos_x3f_5455_);
lean_inc(v_quotDepth_5453_);
lean_dec(v_x_5452_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
lean_object* v___x_5461_; 
if (v_isShared_5459_ == 0)
{
lean_ctor_set(v___x_5458_, 0, v_prec_5451_);
v___x_5461_ = v___x_5458_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_prec_5451_);
lean_ctor_set(v_reuseFailAlloc_5462_, 1, v_quotDepth_5453_);
lean_ctor_set(v_reuseFailAlloc_5462_, 2, v_savedPos_x3f_5455_);
lean_ctor_set(v_reuseFailAlloc_5462_, 3, v_forbiddenTks_5456_);
lean_ctor_set_uint8(v_reuseFailAlloc_5462_, sizeof(void*)*4, v_suppressInsideQuot_5454_);
v___x_5461_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
return v___x_5461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object* v___y_5465_){
_start:
{
lean_inc(v___y_5465_);
return v___y_5465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object* v___y_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = l_Lean_Parser_parserOfStack___lam__1(v___y_5466_);
lean_dec(v___y_5466_);
return v_res_5467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object* v___y_5468_){
_start:
{
lean_inc_ref(v___y_5468_);
return v___y_5468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object* v___y_5469_){
_start:
{
lean_object* v_res_5470_; 
v_res_5470_ = l_Lean_Parser_parserOfStack___lam__2(v___y_5469_);
lean_dec_ref(v___y_5469_);
return v_res_5470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* v_offset_5477_, lean_object* v_prec_5478_){
_start:
{
lean_object* v___f_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; 
v___f_5479_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___lam__0), 2, 1);
lean_closure_set(v___f_5479_, 0, v_prec_5478_);
v___x_5480_ = ((lean_object*)(l_Lean_Parser_parserOfStack___closed__2));
v___x_5481_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___boxed), 3, 1);
lean_closure_set(v___x_5481_, 0, v_offset_5477_);
v___x_5482_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5482_, 0, v___f_5479_);
lean_closure_set(v___x_5482_, 1, v___x_5481_);
v___x_5483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5483_, 0, v___x_5480_);
lean_ctor_set(v___x_5483_, 1, v___x_5482_);
return v___x_5483_;
}
}
lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_BuiltinDocAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_BuiltinDocAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinTokenTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinTokenTable);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinSyntaxNodeKindSetRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinSyntaxNodeKindSetRef);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinParserCategoriesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinParserCategoriesRef);
lean_dec_ref(res);
l_Lean_Parser_ParserExtension_instInhabitedState_default = _init_l_Lean_Parser_ParserExtension_instInhabitedState_default();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedState_default);
l_Lean_Parser_ParserExtension_instInhabitedState = _init_l_Lean_Parser_ParserExtension_instInhabitedState();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedState);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAliasesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAliasesRef);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAlias2kindRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAlias2kindRef);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAliases2infoRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAliases2infoRef);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAttributeHooks = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAttributeHooks);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserExtension);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_internal_parseQuotWithCurrentStage = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_internal_parseQuotWithCurrentStage);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_aliasExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_aliasExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Extension(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Parser_mkInputContext___auto__1 = _init_l_Lean_Parser_mkInputContext___auto__1();
lean_mark_persistent(l_Lean_Parser_mkInputContext___auto__1);
l_Lean_Parser_registerBuiltinParserAttribute___auto__1 = _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1();
lean_mark_persistent(l_Lean_Parser_registerBuiltinParserAttribute___auto__1);
l_Lean_Parser_mkParserAttributeImpl___auto__1 = _init_l_Lean_Parser_mkParserAttributeImpl___auto__1();
lean_mark_persistent(l_Lean_Parser_mkParserAttributeImpl___auto__1);
l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1 = _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1();
lean_mark_persistent(l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1);
l_Lean_Parser_registerParserCategory___auto__1 = _init_l_Lean_Parser_registerParserCategory___auto__1();
lean_mark_persistent(l_Lean_Parser_registerParserCategory___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin);
lean_object* initialize_Lean_BuiltinDocAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Extension(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_BuiltinDocAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Extension(builtin);
}
#ifdef __cplusplus
}
#endif
