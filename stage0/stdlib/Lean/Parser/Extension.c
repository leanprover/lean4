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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_ks_174_; lean_object* v_vs_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_193_; 
v_ks_174_ = lean_ctor_get(v_x_123_, 0);
v_vs_175_ = lean_ctor_get(v_x_123_, 1);
v_isSharedCheck_193_ = !lean_is_exclusive(v_x_123_);
if (v_isSharedCheck_193_ == 0)
{
v___x_177_ = v_x_123_;
v_isShared_178_ = v_isSharedCheck_193_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_vs_175_);
lean_inc(v_ks_174_);
lean_dec(v_x_123_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_193_;
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
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_ks_174_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_vs_175_);
v___x_180_ = v_reuseFailAlloc_192_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v_newNode_181_; size_t v___x_182_; uint8_t v___x_183_; 
v_newNode_181_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v___x_180_, v_x_126_, v_x_127_);
v___x_182_ = ((size_t)7ULL);
v___x_183_ = lean_usize_dec_le(v___x_182_, v_x_125_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_184_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_181_);
v___x_185_ = lean_unsigned_to_nat(4u);
v___x_186_ = lean_nat_dec_lt(v___x_184_, v___x_185_);
lean_dec(v___x_184_);
if (v___x_186_ == 0)
{
lean_object* v_ks_187_; lean_object* v_vs_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_ks_187_ = lean_ctor_get(v_newNode_181_, 0);
lean_inc_ref(v_ks_187_);
v_vs_188_ = lean_ctor_get(v_newNode_181_, 1);
lean_inc_ref(v_vs_188_);
lean_dec_ref(v_newNode_181_);
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0);
v___x_191_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_x_125_, v_ks_187_, v_vs_188_, v___x_189_, v___x_190_);
lean_dec_ref(v_vs_188_);
lean_dec_ref(v_ks_187_);
return v___x_191_;
}
else
{
return v_newNode_181_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(size_t v_depth_194_, lean_object* v_keys_195_, lean_object* v_vals_196_, lean_object* v_i_197_, lean_object* v_entries_198_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_array_get_size(v_keys_195_);
v___x_200_ = lean_nat_dec_lt(v_i_197_, v___x_199_);
if (v___x_200_ == 0)
{
lean_dec(v_i_197_);
return v_entries_198_;
}
else
{
lean_object* v_k_201_; lean_object* v_v_202_; uint64_t v___y_204_; 
v_k_201_ = lean_array_fget_borrowed(v_keys_195_, v_i_197_);
v_v_202_ = lean_array_fget_borrowed(v_vals_196_, v_i_197_);
if (lean_obj_tag(v_k_201_) == 0)
{
uint64_t v___x_215_; 
v___x_215_ = 1723ULL;
v___y_204_ = v___x_215_;
goto v___jp_203_;
}
else
{
uint64_t v_hash_216_; 
v_hash_216_ = lean_ctor_get_uint64(v_k_201_, sizeof(void*)*2);
v___y_204_ = v_hash_216_;
goto v___jp_203_;
}
v___jp_203_:
{
size_t v_h_205_; size_t v___x_206_; lean_object* v___x_207_; size_t v___x_208_; size_t v___x_209_; size_t v___x_210_; size_t v_h_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_h_205_ = lean_uint64_to_usize(v___y_204_);
v___x_206_ = ((size_t)5ULL);
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_sub(v_depth_194_, v___x_208_);
v___x_210_ = lean_usize_mul(v___x_206_, v___x_209_);
v_h_211_ = lean_usize_shift_right(v_h_205_, v___x_210_);
v___x_212_ = lean_nat_add(v_i_197_, v___x_207_);
lean_dec(v_i_197_);
lean_inc(v_v_202_);
lean_inc(v_k_201_);
v___x_213_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_entries_198_, v_h_211_, v_depth_194_, v_k_201_, v_v_202_);
v_i_197_ = v___x_212_;
v_entries_198_ = v___x_213_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_217_, lean_object* v_keys_218_, lean_object* v_vals_219_, lean_object* v_i_220_, lean_object* v_entries_221_){
_start:
{
size_t v_depth_boxed_222_; lean_object* v_res_223_; 
v_depth_boxed_222_ = lean_unbox_usize(v_depth_217_);
lean_dec(v_depth_217_);
v_res_223_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_boxed_222_, v_keys_218_, v_vals_219_, v_i_220_, v_entries_221_);
lean_dec_ref(v_vals_219_);
lean_dec_ref(v_keys_218_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_224_, lean_object* v_x_225_, lean_object* v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
size_t v_x_523__boxed_229_; size_t v_x_524__boxed_230_; lean_object* v_res_231_; 
v_x_523__boxed_229_ = lean_unbox_usize(v_x_225_);
lean_dec(v_x_225_);
v_x_524__boxed_230_ = lean_unbox_usize(v_x_226_);
lean_dec(v_x_226_);
v_res_231_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_224_, v_x_523__boxed_229_, v_x_524__boxed_230_, v_x_227_, v_x_228_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
uint64_t v___y_236_; 
if (lean_obj_tag(v_x_233_) == 0)
{
uint64_t v___x_240_; 
v___x_240_ = 1723ULL;
v___y_236_ = v___x_240_;
goto v___jp_235_;
}
else
{
uint64_t v_hash_241_; 
v_hash_241_ = lean_ctor_get_uint64(v_x_233_, sizeof(void*)*2);
v___y_236_ = v_hash_241_;
goto v___jp_235_;
}
v___jp_235_:
{
size_t v___x_237_; size_t v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_uint64_to_usize(v___y_236_);
v___x_238_ = ((size_t)1ULL);
v___x_239_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_232_, v___x_237_, v___x_238_, v_x_233_, v_x_234_);
return v___x_239_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_242_, lean_object* v_i_243_, lean_object* v_k_244_){
_start:
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_array_get_size(v_keys_242_);
v___x_246_ = lean_nat_dec_lt(v_i_243_, v___x_245_);
if (v___x_246_ == 0)
{
lean_dec(v_i_243_);
return v___x_246_;
}
else
{
lean_object* v_k_x27_247_; uint8_t v___x_248_; 
v_k_x27_247_ = lean_array_fget_borrowed(v_keys_242_, v_i_243_);
v___x_248_ = lean_name_eq(v_k_244_, v_k_x27_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_add(v_i_243_, v___x_249_);
lean_dec(v_i_243_);
v_i_243_ = v___x_250_;
goto _start;
}
else
{
lean_dec(v_i_243_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_252_, lean_object* v_i_253_, lean_object* v_k_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_252_, v_i_253_, v_k_254_);
lean_dec(v_k_254_);
lean_dec_ref(v_keys_252_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(lean_object* v_x_257_, size_t v_x_258_, lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
lean_object* v_es_260_; lean_object* v___x_261_; size_t v___x_262_; size_t v___x_263_; lean_object* v_j_264_; lean_object* v___x_265_; 
v_es_260_ = lean_ctor_get(v_x_257_, 0);
v___x_261_ = lean_box(2);
v___x_262_ = ((size_t)31ULL);
v___x_263_ = lean_usize_land(v_x_258_, v___x_262_);
v_j_264_ = lean_usize_to_nat(v___x_263_);
v___x_265_ = lean_array_get_borrowed(v___x_261_, v_es_260_, v_j_264_);
lean_dec(v_j_264_);
switch(lean_obj_tag(v___x_265_))
{
case 0:
{
lean_object* v_key_266_; uint8_t v___x_267_; 
v_key_266_ = lean_ctor_get(v___x_265_, 0);
v___x_267_ = lean_name_eq(v_x_259_, v_key_266_);
return v___x_267_;
}
case 1:
{
lean_object* v_node_268_; size_t v___x_269_; size_t v___x_270_; 
v_node_268_ = lean_ctor_get(v___x_265_, 0);
v___x_269_ = ((size_t)5ULL);
v___x_270_ = lean_usize_shift_right(v_x_258_, v___x_269_);
v_x_257_ = v_node_268_;
v_x_258_ = v___x_270_;
goto _start;
}
default: 
{
uint8_t v___x_272_; 
v___x_272_ = 0;
return v___x_272_;
}
}
}
else
{
lean_object* v_ks_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_ks_273_ = lean_ctor_get(v_x_257_, 0);
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_ks_273_, v___x_274_, v_x_259_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
size_t v_x_707__boxed_279_; uint8_t v_res_280_; lean_object* v_r_281_; 
v_x_707__boxed_279_ = lean_unbox_usize(v_x_277_);
lean_dec(v_x_277_);
v_res_280_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_276_, v_x_707__boxed_279_, v_x_278_);
lean_dec(v_x_278_);
lean_dec_ref(v_x_276_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
uint64_t v___y_285_; 
if (lean_obj_tag(v_x_283_) == 0)
{
uint64_t v___x_288_; 
v___x_288_ = 1723ULL;
v___y_285_ = v___x_288_;
goto v___jp_284_;
}
else
{
uint64_t v_hash_289_; 
v_hash_289_ = lean_ctor_get_uint64(v_x_283_, sizeof(void*)*2);
v___y_285_ = v_hash_289_;
goto v___jp_284_;
}
v___jp_284_:
{
size_t v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_uint64_to_usize(v___y_285_);
v___x_287_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_282_, v___x_286_, v_x_283_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg___boxed(lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_290_, v_x_291_);
lean_dec(v_x_291_);
lean_dec_ref(v_x_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object* v_categories_294_, lean_object* v_catName_295_, lean_object* v_initial_296_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_294_, v_catName_295_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_294_, v_catName_295_, v_initial_296_);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; 
lean_dec_ref(v_initial_296_);
lean_dec_ref(v_categories_294_);
v___x_300_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_295_);
return v___x_300_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(lean_object* v_00_u03b2_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_302_, v_x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___boxed(lean_object* v_00_u03b2_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
uint8_t v_res_308_; lean_object* v_r_309_; 
v_res_308_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(v_00_u03b2_305_, v_x_306_, v_x_307_);
lean_dec(v_x_307_);
lean_dec_ref(v_x_306_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1(lean_object* v_00_u03b2_310_, lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_x_311_, v_x_312_, v_x_313_);
return v___x_314_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(lean_object* v_00_u03b2_315_, lean_object* v_x_316_, size_t v_x_317_, lean_object* v_x_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_316_, v_x_317_, v_x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
size_t v_x_788__boxed_324_; uint8_t v_res_325_; lean_object* v_r_326_; 
v_x_788__boxed_324_ = lean_unbox_usize(v_x_322_);
lean_dec(v_x_322_);
v_res_325_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(v_00_u03b2_320_, v_x_321_, v_x_788__boxed_324_, v_x_323_);
lean_dec(v_x_323_);
lean_dec_ref(v_x_321_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(lean_object* v_00_u03b2_327_, lean_object* v_x_328_, size_t v_x_329_, size_t v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_328_, v_x_329_, v_x_330_, v_x_331_, v_x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_334_, lean_object* v_x_335_, lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
size_t v_x_799__boxed_340_; size_t v_x_800__boxed_341_; lean_object* v_res_342_; 
v_x_799__boxed_340_ = lean_unbox_usize(v_x_336_);
lean_dec(v_x_336_);
v_x_800__boxed_341_ = lean_unbox_usize(v_x_337_);
lean_dec(v_x_337_);
v_res_342_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(v_00_u03b2_334_, v_x_335_, v_x_799__boxed_340_, v_x_800__boxed_341_, v_x_338_, v_x_339_);
return v_res_342_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_343_, lean_object* v_keys_344_, lean_object* v_vals_345_, lean_object* v_heq_346_, lean_object* v_i_347_, lean_object* v_k_348_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_344_, v_i_347_, v_k_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_350_, lean_object* v_keys_351_, lean_object* v_vals_352_, lean_object* v_heq_353_, lean_object* v_i_354_, lean_object* v_k_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(v_00_u03b2_350_, v_keys_351_, v_vals_352_, v_heq_353_, v_i_354_, v_k_355_);
lean_dec(v_k_355_);
lean_dec_ref(v_vals_352_);
lean_dec_ref(v_keys_351_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_358_, lean_object* v_n_359_, lean_object* v_k_360_, lean_object* v_v_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v_n_359_, v_k_360_, v_v_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_363_, size_t v_depth_364_, lean_object* v_keys_365_, lean_object* v_vals_366_, lean_object* v_heq_367_, lean_object* v_i_368_, lean_object* v_entries_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_364_, v_keys_365_, v_vals_366_, v_i_368_, v_entries_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_371_, lean_object* v_depth_372_, lean_object* v_keys_373_, lean_object* v_vals_374_, lean_object* v_heq_375_, lean_object* v_i_376_, lean_object* v_entries_377_){
_start:
{
size_t v_depth_boxed_378_; lean_object* v_res_379_; 
v_depth_boxed_378_ = lean_unbox_usize(v_depth_372_);
lean_dec(v_depth_372_);
v_res_379_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(v_00_u03b2_371_, v_depth_boxed_378_, v_keys_373_, v_vals_374_, v_heq_375_, v_i_376_, v_entries_377_);
lean_dec_ref(v_vals_374_);
lean_dec_ref(v_keys_373_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_380_, lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_x_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_x_381_, v_x_382_, v_x_383_, v_x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(lean_object* v_e_386_){
_start:
{
if (lean_obj_tag(v_e_386_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
v_a_388_ = lean_ctor_get(v_e_386_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_e_386_);
if (v_isSharedCheck_396_ == 0)
{
v___x_390_ = v_e_386_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v_e_386_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_mk_io_user_error(v_a_388_);
if (v_isShared_391_ == 0)
{
lean_ctor_set_tag(v___x_390_, 1);
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
v_a_397_ = lean_ctor_get(v_e_386_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v_e_386_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v_e_386_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v_e_386_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 0);
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg___boxed(lean_object* v_e_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(lean_object* v_00_u03b1_408_, lean_object* v_e_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___boxed(lean_object* v_00_u03b1_412_, lean_object* v_e_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(v_00_u03b1_412_, v_e_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object* v_catName_419_, lean_object* v_declName_420_, uint8_t v_behavior_421_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_423_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_424_ = lean_st_ref_get(v___x_423_);
v___x_425_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_426_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_427_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_427_, 0, v_declName_420_);
lean_ctor_set(v___x_427_, 1, v___x_425_);
lean_ctor_set(v___x_427_, 2, v___x_426_);
lean_ctor_set_uint8(v___x_427_, sizeof(void*)*3, v_behavior_421_);
v___x_428_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(v___x_424_, v_catName_419_, v___x_427_);
v___x_429_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_439_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_439_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_434_ = lean_st_ref_swap(v___x_423_, v_a_430_);
lean_dec(v___x_434_);
v___x_435_ = lean_box(0);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_435_);
v___x_437_ = v___x_432_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_a_440_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_429_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_429_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object* v_catName_448_, lean_object* v_declName_449_, lean_object* v_behavior_450_, lean_object* v_a_451_){
_start:
{
uint8_t v_behavior_boxed_452_; lean_object* v_res_453_; 
v_behavior_boxed_452_ = lean_unbox(v_behavior_450_);
v_res_453_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_448_, v_declName_449_, v_behavior_boxed_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(lean_object* v_x_454_){
_start:
{
switch(lean_obj_tag(v_x_454_))
{
case 0:
{
lean_object* v___x_455_; 
v___x_455_ = lean_unsigned_to_nat(0u);
return v___x_455_;
}
case 1:
{
lean_object* v___x_456_; 
v___x_456_ = lean_unsigned_to_nat(1u);
return v___x_456_;
}
case 2:
{
lean_object* v___x_457_; 
v___x_457_ = lean_unsigned_to_nat(2u);
return v___x_457_;
}
default: 
{
lean_object* v___x_458_; 
v___x_458_ = lean_unsigned_to_nat(3u);
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___boxed(lean_object* v_x_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(v_x_459_);
lean_dec_ref(v_x_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(lean_object* v_t_461_, lean_object* v_k_462_){
_start:
{
switch(lean_obj_tag(v_t_461_))
{
case 0:
{
lean_object* v_val_463_; lean_object* v___x_464_; 
v_val_463_ = lean_ctor_get(v_t_461_, 0);
lean_inc_ref(v_val_463_);
lean_dec_ref_known(v_t_461_, 1);
v___x_464_ = lean_apply_1(v_k_462_, v_val_463_);
return v___x_464_;
}
case 1:
{
lean_object* v_val_465_; lean_object* v___x_466_; 
v_val_465_ = lean_ctor_get(v_t_461_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v_t_461_, 1);
v___x_466_ = lean_apply_1(v_k_462_, v_val_465_);
return v___x_466_;
}
case 2:
{
lean_object* v_catName_467_; lean_object* v_declName_468_; uint8_t v_behavior_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_catName_467_ = lean_ctor_get(v_t_461_, 0);
lean_inc(v_catName_467_);
v_declName_468_ = lean_ctor_get(v_t_461_, 1);
lean_inc(v_declName_468_);
v_behavior_469_ = lean_ctor_get_uint8(v_t_461_, sizeof(void*)*2);
lean_dec_ref_known(v_t_461_, 2);
v___x_470_ = lean_box(v_behavior_469_);
v___x_471_ = lean_apply_3(v_k_462_, v_catName_467_, v_declName_468_, v___x_470_);
return v___x_471_;
}
default: 
{
lean_object* v_catName_472_; lean_object* v_declName_473_; lean_object* v_prio_474_; lean_object* v___x_475_; 
v_catName_472_ = lean_ctor_get(v_t_461_, 0);
lean_inc(v_catName_472_);
v_declName_473_ = lean_ctor_get(v_t_461_, 1);
lean_inc(v_declName_473_);
v_prio_474_ = lean_ctor_get(v_t_461_, 2);
lean_inc(v_prio_474_);
lean_dec_ref_known(v_t_461_, 3);
v___x_475_ = lean_apply_3(v_k_462_, v_catName_472_, v_declName_473_, v_prio_474_);
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(lean_object* v_motive_476_, lean_object* v_ctorIdx_477_, lean_object* v_t_478_, lean_object* v_h_479_, lean_object* v_k_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_478_, v_k_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___boxed(lean_object* v_motive_482_, lean_object* v_ctorIdx_483_, lean_object* v_t_484_, lean_object* v_h_485_, lean_object* v_k_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(v_motive_482_, v_ctorIdx_483_, v_t_484_, v_h_485_, v_k_486_);
lean_dec(v_ctorIdx_483_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim___redArg(lean_object* v_t_488_, lean_object* v_token_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_488_, v_token_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim(lean_object* v_motive_491_, lean_object* v_t_492_, lean_object* v_h_493_, lean_object* v_token_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_492_, v_token_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim___redArg(lean_object* v_t_496_, lean_object* v_kind_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_496_, v_kind_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim(lean_object* v_motive_499_, lean_object* v_t_500_, lean_object* v_h_501_, lean_object* v_kind_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_500_, v_kind_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim___redArg(lean_object* v_t_504_, lean_object* v_category_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_504_, v_category_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim(lean_object* v_motive_507_, lean_object* v_t_508_, lean_object* v_h_509_, lean_object* v_category_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_508_, v_category_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim___redArg(lean_object* v_t_512_, lean_object* v_parser_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_512_, v_parser_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim(lean_object* v_motive_515_, lean_object* v_t_516_, lean_object* v_h_517_, lean_object* v_parser_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_516_, v_parser_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx(lean_object* v_x_525_){
_start:
{
switch(lean_obj_tag(v_x_525_))
{
case 0:
{
lean_object* v___x_526_; 
v___x_526_ = lean_unsigned_to_nat(0u);
return v___x_526_;
}
case 1:
{
lean_object* v___x_527_; 
v___x_527_ = lean_unsigned_to_nat(1u);
return v___x_527_;
}
case 2:
{
lean_object* v___x_528_; 
v___x_528_ = lean_unsigned_to_nat(2u);
return v___x_528_;
}
default: 
{
lean_object* v___x_529_; 
v___x_529_ = lean_unsigned_to_nat(3u);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___boxed(lean_object* v_x_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Parser_ParserExtension_Entry_ctorIdx(v_x_530_);
lean_dec_ref(v_x_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(lean_object* v_t_532_, lean_object* v_k_533_){
_start:
{
switch(lean_obj_tag(v_t_532_))
{
case 0:
{
lean_object* v_val_534_; lean_object* v___x_535_; 
v_val_534_ = lean_ctor_get(v_t_532_, 0);
lean_inc_ref(v_val_534_);
lean_dec_ref_known(v_t_532_, 1);
v___x_535_ = lean_apply_1(v_k_533_, v_val_534_);
return v___x_535_;
}
case 1:
{
lean_object* v_val_536_; lean_object* v___x_537_; 
v_val_536_ = lean_ctor_get(v_t_532_, 0);
lean_inc(v_val_536_);
lean_dec_ref_known(v_t_532_, 1);
v___x_537_ = lean_apply_1(v_k_533_, v_val_536_);
return v___x_537_;
}
case 2:
{
lean_object* v_catName_538_; lean_object* v_declName_539_; uint8_t v_behavior_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_catName_538_ = lean_ctor_get(v_t_532_, 0);
lean_inc(v_catName_538_);
v_declName_539_ = lean_ctor_get(v_t_532_, 1);
lean_inc(v_declName_539_);
v_behavior_540_ = lean_ctor_get_uint8(v_t_532_, sizeof(void*)*2);
lean_dec_ref_known(v_t_532_, 2);
v___x_541_ = lean_box(v_behavior_540_);
v___x_542_ = lean_apply_3(v_k_533_, v_catName_538_, v_declName_539_, v___x_541_);
return v___x_542_;
}
default: 
{
lean_object* v_catName_543_; lean_object* v_declName_544_; uint8_t v_leading_545_; lean_object* v_p_546_; lean_object* v_prio_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_catName_543_ = lean_ctor_get(v_t_532_, 0);
lean_inc(v_catName_543_);
v_declName_544_ = lean_ctor_get(v_t_532_, 1);
lean_inc(v_declName_544_);
v_leading_545_ = lean_ctor_get_uint8(v_t_532_, sizeof(void*)*4);
v_p_546_ = lean_ctor_get(v_t_532_, 2);
lean_inc_ref(v_p_546_);
v_prio_547_ = lean_ctor_get(v_t_532_, 3);
lean_inc(v_prio_547_);
lean_dec_ref_known(v_t_532_, 4);
v___x_548_ = lean_box(v_leading_545_);
v___x_549_ = lean_apply_5(v_k_533_, v_catName_543_, v_declName_544_, v___x_548_, v_p_546_, v_prio_547_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim(lean_object* v_motive_550_, lean_object* v_ctorIdx_551_, lean_object* v_t_552_, lean_object* v_h_553_, lean_object* v_k_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_552_, v_k_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___boxed(lean_object* v_motive_556_, lean_object* v_ctorIdx_557_, lean_object* v_t_558_, lean_object* v_h_559_, lean_object* v_k_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Parser_ParserExtension_Entry_ctorElim(v_motive_556_, v_ctorIdx_557_, v_t_558_, v_h_559_, v_k_560_);
lean_dec(v_ctorIdx_557_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim___redArg(lean_object* v_t_562_, lean_object* v_token_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_562_, v_token_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim(lean_object* v_motive_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_token_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_566_, v_token_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim___redArg(lean_object* v_t_570_, lean_object* v_kind_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_570_, v_kind_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim(lean_object* v_motive_573_, lean_object* v_t_574_, lean_object* v_h_575_, lean_object* v_kind_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_574_, v_kind_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim___redArg(lean_object* v_t_578_, lean_object* v_category_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_578_, v_category_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim(lean_object* v_motive_581_, lean_object* v_t_582_, lean_object* v_h_583_, lean_object* v_category_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_582_, v_category_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim___redArg(lean_object* v_t_586_, lean_object* v_parser_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_586_, v_parser_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim(lean_object* v_motive_589_, lean_object* v_t_590_, lean_object* v_h_591_, lean_object* v_parser_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_590_, v_parser_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object* v_x_598_){
_start:
{
switch(lean_obj_tag(v_x_598_))
{
case 0:
{
lean_object* v_val_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_val_599_ = lean_ctor_get(v_x_598_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v_x_598_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_val_599_);
lean_dec(v_x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_val_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
case 1:
{
lean_object* v_val_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_val_607_ = lean_ctor_get(v_x_598_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v_x_598_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_val_607_);
lean_dec(v_x_598_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_val_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
case 2:
{
lean_object* v_catName_615_; lean_object* v_declName_616_; uint8_t v_behavior_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_catName_615_ = lean_ctor_get(v_x_598_, 0);
v_declName_616_ = lean_ctor_get(v_x_598_, 1);
v_behavior_617_ = lean_ctor_get_uint8(v_x_598_, sizeof(void*)*2);
v_isSharedCheck_624_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v_x_598_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_declName_616_);
lean_inc(v_catName_615_);
lean_dec(v_x_598_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_catName_615_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_declName_616_);
lean_ctor_set_uint8(v_reuseFailAlloc_623_, sizeof(void*)*2, v_behavior_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
default: 
{
lean_object* v_catName_625_; lean_object* v_declName_626_; lean_object* v_prio_627_; lean_object* v___x_628_; 
v_catName_625_ = lean_ctor_get(v_x_598_, 0);
lean_inc(v_catName_625_);
v_declName_626_ = lean_ctor_get(v_x_598_, 1);
lean_inc(v_declName_626_);
v_prio_627_ = lean_ctor_get(v_x_598_, 3);
lean_inc(v_prio_627_);
lean_dec_ref_known(v_x_598_, 4);
v___x_628_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_628_, 0, v_catName_625_);
lean_ctor_set(v___x_628_, 1, v_declName_626_);
lean_ctor_set(v___x_628_, 2, v_prio_627_);
return v___x_628_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_630_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___x_629_);
lean_ctor_set(v___x_631_, 2, v___x_629_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default(void){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_obj_once(&l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0, &l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0_once, _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState(void){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_635_ = l_Lean_Parser_builtinTokenTable;
v___x_636_ = lean_st_ref_get(v___x_635_);
v___x_637_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_638_ = lean_st_ref_get(v___x_637_);
v___x_639_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_640_ = lean_st_ref_get(v___x_639_);
v___x_641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_641_, 0, v___x_636_);
lean_ctor_set(v___x_641_, 1, v___x_638_);
lean_ctor_set(v___x_641_, 2, v___x_640_);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object* v_tokens_648_, lean_object* v_tk_649_){
_start:
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0));
v___x_651_ = lean_string_dec_eq(v_tk_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Data_Trie_find_x3f___redArg(v_tokens_648_, v_tk_649_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_inc_ref(v_tk_649_);
v___x_653_ = l_Lean_Data_Trie_insert___redArg(v_tokens_648_, v_tk_649_, v_tk_649_);
lean_dec_ref(v_tk_649_);
v___x_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
else
{
lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v_tk_649_);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v___x_652_, 0);
lean_dec(v_unused_662_);
v___x_656_ = v___x_652_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_dec(v___x_652_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v_tokens_648_);
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_tokens_648_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v___x_663_; 
lean_dec_ref(v_tk_649_);
lean_dec_ref(v_tokens_648_);
v___x_663_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1));
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg(lean_object* v_catName_666_){
_start:
{
lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_667_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0));
v___x_668_ = 1;
v___x_669_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_666_, v___x_668_);
v___x_670_ = lean_string_append(v___x_667_, v___x_669_);
lean_dec_ref(v___x_669_);
v___x_671_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_672_ = lean_string_append(v___x_670_, v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object* v_00_u03b1_674_, lean_object* v_catName_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object* v_categories_679_, lean_object* v_catName_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__0));
v___x_682_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__1));
v___x_683_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_681_, v___x_682_, v_categories_679_, v_catName_680_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory___boxed(lean_object* v_categories_684_, lean_object* v_catName_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Parser_getCategory(v_categories_684_, v_catName_685_);
lean_dec_ref(v_categories_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(lean_object* v_as_688_){
_start:
{
lean_object* v___f_689_; lean_object* v___x_690_; 
v___f_689_ = ((lean_object*)(l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0));
v___x_690_ = l_List_eraseDupsBy___redArg(v___f_689_, v_as_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(lean_object* v_p_691_, lean_object* v_prio_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
if (lean_obj_tag(v_x_694_) == 0)
{
lean_dec(v_prio_692_);
lean_dec_ref(v_p_691_);
return v_x_693_;
}
else
{
lean_object* v_head_695_; lean_object* v_tail_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_716_; 
v_head_695_ = lean_ctor_get(v_x_694_, 0);
v_tail_696_ = lean_ctor_get(v_x_694_, 1);
v_isSharedCheck_716_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_716_ == 0)
{
v___x_698_ = v_x_694_;
v_isShared_699_ = v_isSharedCheck_716_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_tail_696_);
lean_inc(v_head_695_);
lean_dec(v_x_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_716_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_leadingTable_700_; lean_object* v_leadingParsers_701_; lean_object* v_trailingTable_702_; lean_object* v_trailingParsers_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_715_; 
v_leadingTable_700_ = lean_ctor_get(v_x_693_, 0);
v_leadingParsers_701_ = lean_ctor_get(v_x_693_, 1);
v_trailingTable_702_ = lean_ctor_get(v_x_693_, 2);
v_trailingParsers_703_ = lean_ctor_get(v_x_693_, 3);
v_isSharedCheck_715_ = !lean_is_exclusive(v_x_693_);
if (v_isSharedCheck_715_ == 0)
{
v___x_705_ = v_x_693_;
v_isShared_706_ = v_isSharedCheck_715_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_trailingParsers_703_);
lean_inc(v_trailingTable_702_);
lean_inc(v_leadingParsers_701_);
lean_inc(v_leadingTable_700_);
lean_dec(v_x_693_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_715_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
lean_inc(v_prio_692_);
lean_inc_ref(v_p_691_);
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 0);
lean_ctor_set(v___x_698_, 1, v_prio_692_);
lean_ctor_set(v___x_698_, 0, v_p_691_);
v___x_708_ = v___x_698_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_p_691_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_prio_692_);
v___x_708_ = v_reuseFailAlloc_714_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = l_Lean_Parser_TokenMap_insert___redArg(v_leadingTable_700_, v_head_695_, v___x_708_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_709_);
v___x_711_ = v___x_705_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_leadingParsers_701_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_trailingTable_702_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_trailingParsers_703_);
v___x_711_ = v_reuseFailAlloc_713_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
v_x_693_ = v___x_711_;
v_x_694_ = v_tail_696_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_717_, lean_object* v_vals_718_, lean_object* v_i_719_, lean_object* v_k_720_){
_start:
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_array_get_size(v_keys_717_);
v___x_722_ = lean_nat_dec_lt(v_i_719_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_dec(v_i_719_);
v___x_723_ = lean_box(0);
return v___x_723_;
}
else
{
lean_object* v_k_x27_724_; uint8_t v___x_725_; 
v_k_x27_724_ = lean_array_fget_borrowed(v_keys_717_, v_i_719_);
v___x_725_ = lean_name_eq(v_k_720_, v_k_x27_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_nat_add(v_i_719_, v___x_726_);
lean_dec(v_i_719_);
v_i_719_ = v___x_727_;
goto _start;
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_array_fget_borrowed(v_vals_718_, v_i_719_);
lean_dec(v_i_719_);
lean_inc(v___x_729_);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_731_, lean_object* v_vals_732_, lean_object* v_i_733_, lean_object* v_k_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_731_, v_vals_732_, v_i_733_, v_k_734_);
lean_dec(v_k_734_);
lean_dec_ref(v_vals_732_);
lean_dec_ref(v_keys_731_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(lean_object* v_x_736_, size_t v_x_737_, lean_object* v_x_738_){
_start:
{
if (lean_obj_tag(v_x_736_) == 0)
{
lean_object* v_es_739_; lean_object* v___x_740_; size_t v___x_741_; size_t v___x_742_; lean_object* v_j_743_; lean_object* v___x_744_; 
v_es_739_ = lean_ctor_get(v_x_736_, 0);
v___x_740_ = lean_box(2);
v___x_741_ = ((size_t)31ULL);
v___x_742_ = lean_usize_land(v_x_737_, v___x_741_);
v_j_743_ = lean_usize_to_nat(v___x_742_);
v___x_744_ = lean_array_get_borrowed(v___x_740_, v_es_739_, v_j_743_);
lean_dec(v_j_743_);
switch(lean_obj_tag(v___x_744_))
{
case 0:
{
lean_object* v_key_745_; lean_object* v_val_746_; uint8_t v___x_747_; 
v_key_745_ = lean_ctor_get(v___x_744_, 0);
v_val_746_ = lean_ctor_get(v___x_744_, 1);
v___x_747_ = lean_name_eq(v_x_738_, v_key_745_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
v___x_748_ = lean_box(0);
return v___x_748_;
}
else
{
lean_object* v___x_749_; 
lean_inc(v_val_746_);
v___x_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_749_, 0, v_val_746_);
return v___x_749_;
}
}
case 1:
{
lean_object* v_node_750_; size_t v___x_751_; size_t v___x_752_; 
v_node_750_ = lean_ctor_get(v___x_744_, 0);
v___x_751_ = ((size_t)5ULL);
v___x_752_ = lean_usize_shift_right(v_x_737_, v___x_751_);
v_x_736_ = v_node_750_;
v_x_737_ = v___x_752_;
goto _start;
}
default: 
{
lean_object* v___x_754_; 
v___x_754_ = lean_box(0);
return v___x_754_;
}
}
}
else
{
lean_object* v_ks_755_; lean_object* v_vs_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_ks_755_ = lean_ctor_get(v_x_736_, 0);
v_vs_756_ = lean_ctor_get(v_x_736_, 1);
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_ks_755_, v_vs_756_, v___x_757_, v_x_738_);
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg___boxed(lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
size_t v_x_490__boxed_762_; lean_object* v_res_763_; 
v_x_490__boxed_762_ = lean_unbox_usize(v_x_760_);
lean_dec(v_x_760_);
v_res_763_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_759_, v_x_490__boxed_762_, v_x_761_);
lean_dec(v_x_761_);
lean_dec_ref(v_x_759_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
uint64_t v___y_767_; 
if (lean_obj_tag(v_x_765_) == 0)
{
uint64_t v___x_770_; 
v___x_770_ = 1723ULL;
v___y_767_ = v___x_770_;
goto v___jp_766_;
}
else
{
uint64_t v_hash_771_; 
v_hash_771_ = lean_ctor_get_uint64(v_x_765_, sizeof(void*)*2);
v___y_767_ = v_hash_771_;
goto v___jp_766_;
}
v___jp_766_:
{
size_t v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_uint64_to_usize(v___y_767_);
v___x_769_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_764_, v___x_768_, v_x_765_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg___boxed(lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_772_, v_x_773_);
lean_dec(v_x_773_);
lean_dec_ref(v_x_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
if (lean_obj_tag(v_a_775_) == 0)
{
lean_object* v___x_777_; 
v___x_777_ = l_List_reverse___redArg(v_a_776_);
return v___x_777_;
}
else
{
lean_object* v_head_778_; lean_object* v_tail_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_789_; 
v_head_778_ = lean_ctor_get(v_a_775_, 0);
v_tail_779_ = lean_ctor_get(v_a_775_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_a_775_);
if (v_isSharedCheck_789_ == 0)
{
v___x_781_ = v_a_775_;
v_isShared_782_ = v_isSharedCheck_789_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_tail_779_);
lean_inc(v_head_778_);
lean_dec(v_a_775_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_789_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_783_ = lean_box(0);
v___x_784_ = l_Lean_Name_str___override(v___x_783_, v_head_778_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v_a_776_);
lean_ctor_set(v___x_781_, 0, v___x_784_);
v___x_786_ = v___x_781_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_a_776_);
v___x_786_ = v_reuseFailAlloc_788_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
v_a_775_ = v_tail_779_;
v_a_776_ = v___x_786_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object* v_categories_790_, lean_object* v_catName_791_, lean_object* v_declName_792_, lean_object* v_p_793_, lean_object* v_prio_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_790_, v_catName_791_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; 
lean_dec(v_prio_794_);
lean_dec_ref(v_p_793_);
lean_dec(v_declName_792_);
lean_dec_ref(v_categories_790_);
v___x_796_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_791_);
return v___x_796_;
}
else
{
lean_object* v_val_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_843_; 
v_val_797_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_843_ == 0)
{
v___x_799_ = v___x_795_;
v_isShared_800_ = v_isSharedCheck_843_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_val_797_);
lean_dec(v___x_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_843_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_info_801_; lean_object* v_declName_802_; lean_object* v_kinds_803_; lean_object* v_tables_804_; uint8_t v_behavior_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_842_; 
v_info_801_ = lean_ctor_get(v_p_793_, 0);
v_declName_802_ = lean_ctor_get(v_val_797_, 0);
v_kinds_803_ = lean_ctor_get(v_val_797_, 1);
v_tables_804_ = lean_ctor_get(v_val_797_, 2);
v_behavior_805_ = lean_ctor_get_uint8(v_val_797_, sizeof(void*)*3);
v_isSharedCheck_842_ = !lean_is_exclusive(v_val_797_);
if (v_isSharedCheck_842_ == 0)
{
v___x_807_ = v_val_797_;
v_isShared_808_ = v_isSharedCheck_842_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_tables_804_);
lean_inc(v_kinds_803_);
lean_inc(v_declName_802_);
lean_dec(v_val_797_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_842_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v_firstTokens_809_; lean_object* v_kinds_810_; lean_object* v_tks_812_; 
v_firstTokens_809_ = lean_ctor_get(v_info_801_, 2);
v_kinds_810_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_803_, v_declName_792_);
switch(lean_obj_tag(v_firstTokens_809_))
{
case 2:
{
lean_object* v_a_824_; 
v_a_824_ = lean_ctor_get(v_firstTokens_809_, 0);
lean_inc(v_a_824_);
v_tks_812_ = v_a_824_;
goto v___jp_811_;
}
case 3:
{
lean_object* v_a_825_; 
v_a_825_ = lean_ctor_get(v_firstTokens_809_, 0);
lean_inc(v_a_825_);
v_tks_812_ = v_a_825_;
goto v___jp_811_;
}
default: 
{
lean_object* v_leadingTable_826_; lean_object* v_leadingParsers_827_; lean_object* v_trailingTable_828_; lean_object* v_trailingParsers_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_841_; 
lean_del_object(v___x_807_);
lean_del_object(v___x_799_);
v_leadingTable_826_ = lean_ctor_get(v_tables_804_, 0);
v_leadingParsers_827_ = lean_ctor_get(v_tables_804_, 1);
v_trailingTable_828_ = lean_ctor_get(v_tables_804_, 2);
v_trailingParsers_829_ = lean_ctor_get(v_tables_804_, 3);
v_isSharedCheck_841_ = !lean_is_exclusive(v_tables_804_);
if (v_isSharedCheck_841_ == 0)
{
v___x_831_ = v_tables_804_;
v_isShared_832_ = v_isSharedCheck_841_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_trailingParsers_829_);
lean_inc(v_trailingTable_828_);
lean_inc(v_leadingParsers_827_);
lean_inc(v_leadingTable_826_);
lean_dec(v_tables_804_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_841_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_tables_836_; 
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v_p_793_);
lean_ctor_set(v___x_833_, 1, v_prio_794_);
v___x_834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v_leadingParsers_827_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_834_);
v_tables_836_ = v___x_831_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_leadingTable_826_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_trailingTable_828_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_trailingParsers_829_);
v_tables_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_837_, 0, v_declName_802_);
lean_ctor_set(v___x_837_, 1, v_kinds_810_);
lean_ctor_set(v___x_837_, 2, v_tables_836_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*3, v_behavior_805_);
v___x_838_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_790_, v_catName_791_, v___x_837_);
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
}
}
}
v___jp_811_:
{
lean_object* v___x_813_; lean_object* v_tks_814_; lean_object* v___x_815_; lean_object* v_tables_816_; lean_object* v___x_818_; 
v___x_813_ = lean_box(0);
v_tks_814_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_812_, v___x_813_);
v___x_815_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_814_);
v_tables_816_ = l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(v_p_793_, v_prio_794_, v_tables_804_, v___x_815_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 2, v_tables_816_);
lean_ctor_set(v___x_807_, 1, v_kinds_810_);
v___x_818_ = v___x_807_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_declName_802_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_kinds_810_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_tables_816_);
lean_ctor_set_uint8(v_reuseFailAlloc_823_, sizeof(void*)*3, v_behavior_805_);
v___x_818_ = v_reuseFailAlloc_823_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_790_, v_catName_791_, v___x_818_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_819_);
v___x_821_ = v___x_799_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(lean_object* v_00_u03b2_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_845_, v_x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___boxed(lean_object* v_00_u03b2_848_, lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(v_00_u03b2_848_, v_x_849_, v_x_850_);
lean_dec(v_x_850_);
lean_dec_ref(v_x_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_object* v_00_u03b2_852_, lean_object* v_x_853_, size_t v_x_854_, lean_object* v_x_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_853_, v_x_854_, v_x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___boxed(lean_object* v_00_u03b2_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
size_t v_x_659__boxed_861_; lean_object* v_res_862_; 
v_x_659__boxed_861_ = lean_unbox_usize(v_x_859_);
lean_dec(v_x_859_);
v_res_862_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(v_00_u03b2_857_, v_x_858_, v_x_659__boxed_861_, v_x_860_);
lean_dec(v_x_860_);
lean_dec_ref(v_x_858_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_863_, lean_object* v_keys_864_, lean_object* v_vals_865_, lean_object* v_heq_866_, lean_object* v_i_867_, lean_object* v_k_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_864_, v_vals_865_, v_i_867_, v_k_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_870_, lean_object* v_keys_871_, lean_object* v_vals_872_, lean_object* v_heq_873_, lean_object* v_i_874_, lean_object* v_k_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(v_00_u03b2_870_, v_keys_871_, v_vals_872_, v_heq_873_, v_i_874_, v_k_875_);
lean_dec(v_k_875_);
lean_dec_ref(v_vals_872_);
lean_dec_ref(v_keys_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(lean_object* v_p_877_, lean_object* v_prio_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
if (lean_obj_tag(v_x_880_) == 0)
{
lean_dec(v_prio_878_);
lean_dec_ref(v_p_877_);
return v_x_879_;
}
else
{
lean_object* v_head_881_; lean_object* v_tail_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_902_; 
v_head_881_ = lean_ctor_get(v_x_880_, 0);
v_tail_882_ = lean_ctor_get(v_x_880_, 1);
v_isSharedCheck_902_ = !lean_is_exclusive(v_x_880_);
if (v_isSharedCheck_902_ == 0)
{
v___x_884_ = v_x_880_;
v_isShared_885_ = v_isSharedCheck_902_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_tail_882_);
lean_inc(v_head_881_);
lean_dec(v_x_880_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_902_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_leadingTable_886_; lean_object* v_leadingParsers_887_; lean_object* v_trailingTable_888_; lean_object* v_trailingParsers_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_901_; 
v_leadingTable_886_ = lean_ctor_get(v_x_879_, 0);
v_leadingParsers_887_ = lean_ctor_get(v_x_879_, 1);
v_trailingTable_888_ = lean_ctor_get(v_x_879_, 2);
v_trailingParsers_889_ = lean_ctor_get(v_x_879_, 3);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_879_);
if (v_isSharedCheck_901_ == 0)
{
v___x_891_ = v_x_879_;
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_trailingParsers_889_);
lean_inc(v_trailingTable_888_);
lean_inc(v_leadingParsers_887_);
lean_inc(v_leadingTable_886_);
lean_dec(v_x_879_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
lean_inc(v_prio_878_);
lean_inc_ref(v_p_877_);
if (v_isShared_885_ == 0)
{
lean_ctor_set_tag(v___x_884_, 0);
lean_ctor_set(v___x_884_, 1, v_prio_878_);
lean_ctor_set(v___x_884_, 0, v_p_877_);
v___x_894_ = v___x_884_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_p_877_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_prio_878_);
v___x_894_ = v_reuseFailAlloc_900_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = l_Lean_Parser_TokenMap_insert___redArg(v_trailingTable_888_, v_head_881_, v___x_894_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 2, v___x_895_);
v___x_897_ = v___x_891_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_leadingTable_886_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_leadingParsers_887_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_trailingParsers_889_);
v___x_897_ = v_reuseFailAlloc_899_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
v_x_879_ = v___x_897_;
v_x_880_ = v_tail_882_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object* v_tables_903_, lean_object* v_p_904_, lean_object* v_prio_905_){
_start:
{
lean_object* v_tks_907_; lean_object* v_info_912_; lean_object* v_firstTokens_913_; 
v_info_912_ = lean_ctor_get(v_p_904_, 0);
v_firstTokens_913_ = lean_ctor_get(v_info_912_, 2);
switch(lean_obj_tag(v_firstTokens_913_))
{
case 2:
{
lean_object* v_a_914_; 
v_a_914_ = lean_ctor_get(v_firstTokens_913_, 0);
lean_inc(v_a_914_);
v_tks_907_ = v_a_914_;
goto v___jp_906_;
}
case 3:
{
lean_object* v_a_915_; 
v_a_915_ = lean_ctor_get(v_firstTokens_913_, 0);
lean_inc(v_a_915_);
v_tks_907_ = v_a_915_;
goto v___jp_906_;
}
default: 
{
lean_object* v_leadingTable_916_; lean_object* v_leadingParsers_917_; lean_object* v_trailingTable_918_; lean_object* v_trailingParsers_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_928_; 
v_leadingTable_916_ = lean_ctor_get(v_tables_903_, 0);
v_leadingParsers_917_ = lean_ctor_get(v_tables_903_, 1);
v_trailingTable_918_ = lean_ctor_get(v_tables_903_, 2);
v_trailingParsers_919_ = lean_ctor_get(v_tables_903_, 3);
v_isSharedCheck_928_ = !lean_is_exclusive(v_tables_903_);
if (v_isSharedCheck_928_ == 0)
{
v___x_921_ = v_tables_903_;
v_isShared_922_ = v_isSharedCheck_928_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_trailingParsers_919_);
lean_inc(v_trailingTable_918_);
lean_inc(v_leadingParsers_917_);
lean_inc(v_leadingTable_916_);
lean_dec(v_tables_903_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_928_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v_p_904_);
lean_ctor_set(v___x_923_, 1, v_prio_905_);
v___x_924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v_trailingParsers_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 3, v___x_924_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_leadingTable_916_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_leadingParsers_917_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_trailingTable_918_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
v___jp_906_:
{
lean_object* v___x_908_; lean_object* v_tks_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_908_ = lean_box(0);
v_tks_909_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_907_, v___x_908_);
v___x_910_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_909_);
v___x_911_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(v_p_904_, v_prio_905_, v_tables_903_, v___x_910_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object* v_categories_929_, lean_object* v_catName_930_, lean_object* v_declName_931_, lean_object* v_p_932_, lean_object* v_prio_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_929_, v_catName_930_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v___x_935_; 
lean_dec(v_prio_933_);
lean_dec_ref(v_p_932_);
lean_dec(v_declName_931_);
lean_dec_ref(v_categories_929_);
v___x_935_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_930_);
return v___x_935_;
}
else
{
lean_object* v_val_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_957_; 
v_val_936_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_957_ == 0)
{
v___x_938_ = v___x_934_;
v_isShared_939_ = v_isSharedCheck_957_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_val_936_);
lean_dec(v___x_934_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_957_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_declName_940_; lean_object* v_kinds_941_; lean_object* v_tables_942_; uint8_t v_behavior_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_956_; 
v_declName_940_ = lean_ctor_get(v_val_936_, 0);
v_kinds_941_ = lean_ctor_get(v_val_936_, 1);
v_tables_942_ = lean_ctor_get(v_val_936_, 2);
v_behavior_943_ = lean_ctor_get_uint8(v_val_936_, sizeof(void*)*3);
v_isSharedCheck_956_ = !lean_is_exclusive(v_val_936_);
if (v_isSharedCheck_956_ == 0)
{
v___x_945_ = v_val_936_;
v_isShared_946_ = v_isSharedCheck_956_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_tables_942_);
lean_inc(v_kinds_941_);
lean_inc(v_declName_940_);
lean_dec(v_val_936_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_956_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_kinds_947_; lean_object* v_tables_948_; lean_object* v___x_950_; 
v_kinds_947_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_941_, v_declName_931_);
v_tables_948_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(v_tables_942_, v_p_932_, v_prio_933_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 2, v_tables_948_);
lean_ctor_set(v___x_945_, 1, v_kinds_947_);
v___x_950_ = v___x_945_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_declName_940_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_kinds_947_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_tables_948_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, sizeof(void*)*3, v_behavior_943_);
v___x_950_ = v_reuseFailAlloc_955_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_929_, v_catName_930_, v___x_950_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_951_);
v___x_953_ = v___x_938_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object* v_categories_958_, lean_object* v_catName_959_, lean_object* v_declName_960_, uint8_t v_leading_961_, lean_object* v_p_962_, lean_object* v_prio_963_){
_start:
{
if (v_leading_961_ == 0)
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_Parser_addTrailingParser(v_categories_958_, v_catName_959_, v_declName_960_, v_p_962_, v_prio_963_);
return v___x_964_;
}
else
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Parser_addLeadingParser(v_categories_958_, v_catName_959_, v_declName_960_, v_p_962_, v_prio_963_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object* v_categories_966_, lean_object* v_catName_967_, lean_object* v_declName_968_, lean_object* v_leading_969_, lean_object* v_p_970_, lean_object* v_prio_971_){
_start:
{
uint8_t v_leading_boxed_972_; lean_object* v_res_973_; 
v_leading_boxed_972_ = lean_unbox(v_leading_969_);
v_res_973_ = l_Lean_Parser_addParser(v_categories_966_, v_catName_967_, v_declName_968_, v_leading_boxed_972_, v_p_970_, v_prio_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
if (lean_obj_tag(v_x_975_) == 0)
{
lean_object* v___x_976_; 
v___x_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_976_, 0, v_x_974_);
return v___x_976_;
}
else
{
lean_object* v_head_977_; lean_object* v_tail_978_; lean_object* v___x_979_; 
v_head_977_ = lean_ctor_get(v_x_975_, 0);
lean_inc(v_head_977_);
v_tail_978_ = lean_ctor_get(v_x_975_, 1);
lean_inc(v_tail_978_);
lean_dec_ref_known(v_x_975_, 2);
v___x_979_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_x_974_, v_head_977_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_dec(v_tail_978_);
return v___x_979_;
}
else
{
lean_object* v_a_980_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v_x_974_ = v_a_980_;
v_x_975_ = v_tail_978_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object* v_tokenTable_982_, lean_object* v_info_983_){
_start:
{
lean_object* v_collectTokens_984_; lean_object* v___x_985_; lean_object* v_newTokens_986_; lean_object* v___x_987_; 
v_collectTokens_984_ = lean_ctor_get(v_info_983_, 0);
lean_inc_ref(v_collectTokens_984_);
lean_dec_ref(v_info_983_);
v___x_985_ = lean_box(0);
v_newTokens_986_ = lean_apply_1(v_collectTokens_984_, v___x_985_);
v___x_987_ = l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(v_tokenTable_982_, v_newTokens_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object* v_info_990_, lean_object* v_declName_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_993_ = l_Lean_Parser_builtinTokenTable;
v___x_994_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_995_ = lean_st_ref_swap(v___x_993_, v___x_994_);
v___x_996_ = l_Lean_Parser_addParserTokens(v___x_995_, v_info_990_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1013_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1013_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1013_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1001_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0));
v___x_1002_ = l_Lean_privateToUserName(v_declName_991_);
v___x_1003_ = 1;
v___x_1004_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1002_, v___x_1003_);
v___x_1005_ = lean_string_append(v___x_1001_, v___x_1004_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_1007_ = lean_string_append(v___x_1005_, v___x_1006_);
v___x_1008_ = lean_string_append(v___x_1007_, v_a_997_);
lean_dec(v_a_997_);
v___x_1009_ = lean_mk_io_user_error(v___x_1008_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 1);
lean_ctor_set(v___x_999_, 0, v___x_1009_);
v___x_1011_ = v___x_999_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_declName_991_);
v_a_1014_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1016_ = v___x_996_;
v_isShared_1017_ = v_isSharedCheck_1023_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_996_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1023_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1018_ = lean_st_ref_swap(v___x_993_, v_a_1014_);
lean_dec(v___x_1018_);
v___x_1019_ = lean_box(0);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1019_);
v___x_1021_ = v___x_1016_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___boxed(lean_object* v_info_1024_, lean_object* v_declName_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_1024_, v_declName_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(lean_object* v_msg_1028_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1030_ = lean_panic_fn_borrowed(v___x_1029_, v_msg_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object* v_s_1034_, lean_object* v_e_1035_){
_start:
{
switch(lean_obj_tag(v_e_1035_))
{
case 0:
{
lean_object* v_val_1036_; lean_object* v_tokens_1037_; lean_object* v_kinds_1038_; lean_object* v_categories_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1057_; 
v_val_1036_ = lean_ctor_get(v_e_1035_, 0);
lean_inc_ref(v_val_1036_);
lean_dec_ref_known(v_e_1035_, 1);
v_tokens_1037_ = lean_ctor_get(v_s_1034_, 0);
v_kinds_1038_ = lean_ctor_get(v_s_1034_, 1);
v_categories_1039_ = lean_ctor_get(v_s_1034_, 2);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_s_1034_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1041_ = v_s_1034_;
v_isShared_1042_ = v_isSharedCheck_1057_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_categories_1039_);
lean_inc(v_kinds_1038_);
lean_inc(v_tokens_1037_);
lean_dec(v_s_1034_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1057_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; 
v___x_1043_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_1037_, v_val_1036_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_del_object(v___x_1041_);
lean_dec_ref(v_categories_1039_);
lean_dec_ref(v_kinds_1038_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1046_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1047_ = lean_unsigned_to_nat(163u);
v___x_1048_ = lean_unsigned_to_nat(26u);
v___x_1049_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1050_ = lean_string_append(v___x_1049_, v_a_1044_);
lean_dec(v_a_1044_);
v___x_1051_ = l_mkPanicMessageWithDecl(v___x_1045_, v___x_1046_, v___x_1047_, v___x_1048_, v___x_1050_);
lean_dec_ref(v___x_1050_);
v___x_1052_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1051_);
return v___x_1052_;
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; 
v_a_1053_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1043_, 1);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v_a_1053_);
v___x_1055_ = v___x_1041_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1053_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_kinds_1038_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_categories_1039_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
case 1:
{
lean_object* v_val_1058_; lean_object* v_tokens_1059_; lean_object* v_kinds_1060_; lean_object* v_categories_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1069_; 
v_val_1058_ = lean_ctor_get(v_e_1035_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v_e_1035_, 1);
v_tokens_1059_ = lean_ctor_get(v_s_1034_, 0);
v_kinds_1060_ = lean_ctor_get(v_s_1034_, 1);
v_categories_1061_ = lean_ctor_get(v_s_1034_, 2);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_s_1034_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1063_ = v_s_1034_;
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_categories_1061_);
lean_inc(v_kinds_1060_);
lean_inc(v_tokens_1059_);
lean_dec(v_s_1034_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_1060_, v_val_1058_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v___x_1065_);
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_tokens_1059_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_categories_1061_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
case 2:
{
lean_object* v_catName_1070_; lean_object* v_declName_1071_; uint8_t v_behavior_1072_; lean_object* v_tokens_1073_; lean_object* v_kinds_1074_; lean_object* v_categories_1075_; uint8_t v___x_1076_; 
v_catName_1070_ = lean_ctor_get(v_e_1035_, 0);
lean_inc(v_catName_1070_);
v_declName_1071_ = lean_ctor_get(v_e_1035_, 1);
lean_inc(v_declName_1071_);
v_behavior_1072_ = lean_ctor_get_uint8(v_e_1035_, sizeof(void*)*2);
lean_dec_ref_known(v_e_1035_, 2);
v_tokens_1073_ = lean_ctor_get(v_s_1034_, 0);
v_kinds_1074_ = lean_ctor_get(v_s_1034_, 1);
v_categories_1075_ = lean_ctor_get(v_s_1034_, 2);
v___x_1076_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_1075_, v_catName_1070_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1087_; 
lean_inc_ref(v_categories_1075_);
lean_inc_ref(v_kinds_1074_);
lean_inc_ref(v_tokens_1073_);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_s_1034_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; lean_object* v_unused_1089_; lean_object* v_unused_1090_; 
v_unused_1088_ = lean_ctor_get(v_s_1034_, 2);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v_s_1034_, 1);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_s_1034_, 0);
lean_dec(v_unused_1090_);
v___x_1078_ = v_s_1034_;
v_isShared_1079_ = v_isSharedCheck_1087_;
goto v_resetjp_1077_;
}
else
{
lean_dec(v_s_1034_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1087_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1080_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_1081_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_1082_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1082_, 0, v_declName_1071_);
lean_ctor_set(v___x_1082_, 1, v___x_1080_);
lean_ctor_set(v___x_1082_, 2, v___x_1081_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*3, v_behavior_1072_);
v___x_1083_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_1075_, v_catName_1070_, v___x_1082_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 2, v___x_1083_);
v___x_1085_ = v___x_1078_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_tokens_1073_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_kinds_1074_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_dec(v_declName_1071_);
lean_dec(v_catName_1070_);
return v_s_1034_;
}
}
default: 
{
lean_object* v_catName_1091_; lean_object* v_declName_1092_; uint8_t v_leading_1093_; lean_object* v_p_1094_; lean_object* v_prio_1095_; lean_object* v_tokens_1096_; lean_object* v_kinds_1097_; lean_object* v_categories_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1116_; 
v_catName_1091_ = lean_ctor_get(v_e_1035_, 0);
lean_inc(v_catName_1091_);
v_declName_1092_ = lean_ctor_get(v_e_1035_, 1);
lean_inc(v_declName_1092_);
v_leading_1093_ = lean_ctor_get_uint8(v_e_1035_, sizeof(void*)*4);
v_p_1094_ = lean_ctor_get(v_e_1035_, 2);
lean_inc_ref(v_p_1094_);
v_prio_1095_ = lean_ctor_get(v_e_1035_, 3);
lean_inc(v_prio_1095_);
lean_dec_ref_known(v_e_1035_, 4);
v_tokens_1096_ = lean_ctor_get(v_s_1034_, 0);
v_kinds_1097_ = lean_ctor_get(v_s_1034_, 1);
v_categories_1098_ = lean_ctor_get(v_s_1034_, 2);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_s_1034_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1100_ = v_s_1034_;
v_isShared_1101_ = v_isSharedCheck_1116_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_categories_1098_);
lean_inc(v_kinds_1097_);
lean_inc(v_tokens_1096_);
lean_dec(v_s_1034_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1116_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_Parser_addParser(v_categories_1098_, v_catName_1091_, v_declName_1092_, v_leading_1093_, v_p_1094_, v_prio_1095_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_del_object(v___x_1100_);
lean_dec_ref(v_kinds_1097_);
lean_dec_ref(v_tokens_1096_);
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1102_, 1);
v___x_1104_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1105_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1106_ = lean_unsigned_to_nat(173u);
v___x_1107_ = lean_unsigned_to_nat(30u);
v___x_1108_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1109_ = lean_string_append(v___x_1108_, v_a_1103_);
lean_dec(v_a_1103_);
v___x_1110_ = l_mkPanicMessageWithDecl(v___x_1104_, v___x_1105_, v___x_1106_, v___x_1107_, v___x_1109_);
lean_dec_ref(v___x_1109_);
v___x_1111_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1110_);
return v___x_1111_;
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; 
v_a_1112_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1102_, 1);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 2, v_a_1112_);
v___x_1114_ = v___x_1100_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_tokens_1096_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_kinds_1097_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_a_1112_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg(lean_object* v_x_1117_){
_start:
{
switch(lean_obj_tag(v_x_1117_))
{
case 0:
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_unsigned_to_nat(0u);
return v___x_1118_;
}
case 1:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_unsigned_to_nat(1u);
return v___x_1119_;
}
default: 
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_unsigned_to_nat(2u);
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg___boxed(lean_object* v_x_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Parser_AliasValue_ctorIdx___redArg(v_x_1121_);
lean_dec_ref(v_x_1121_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx(lean_object* v_00_u03b1_1123_, lean_object* v_x_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_Parser_AliasValue_ctorIdx___redArg(v_x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___boxed(lean_object* v_00_u03b1_1126_, lean_object* v_x_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Parser_AliasValue_ctorIdx(v_00_u03b1_1126_, v_x_1127_);
lean_dec_ref(v_x_1127_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___redArg(lean_object* v_t_1129_, lean_object* v_k_1130_){
_start:
{
lean_object* v_p_1131_; lean_object* v___x_1132_; 
v_p_1131_ = lean_ctor_get(v_t_1129_, 0);
lean_inc(v_p_1131_);
lean_dec_ref(v_t_1129_);
v___x_1132_ = lean_apply_1(v_k_1130_, v_p_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim(lean_object* v_00_u03b1_1133_, lean_object* v_motive_1134_, lean_object* v_ctorIdx_1135_, lean_object* v_t_1136_, lean_object* v_h_1137_, lean_object* v_k_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1136_, v_k_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___boxed(lean_object* v_00_u03b1_1140_, lean_object* v_motive_1141_, lean_object* v_ctorIdx_1142_, lean_object* v_t_1143_, lean_object* v_h_1144_, lean_object* v_k_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Parser_AliasValue_ctorElim(v_00_u03b1_1140_, v_motive_1141_, v_ctorIdx_1142_, v_t_1143_, v_h_1144_, v_k_1145_);
lean_dec(v_ctorIdx_1142_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim___redArg(lean_object* v_t_1147_, lean_object* v_const_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1147_, v_const_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim(lean_object* v_00_u03b1_1150_, lean_object* v_motive_1151_, lean_object* v_t_1152_, lean_object* v_h_1153_, lean_object* v_const_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1152_, v_const_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim___redArg(lean_object* v_t_1156_, lean_object* v_unary_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1156_, v_unary_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim(lean_object* v_00_u03b1_1159_, lean_object* v_motive_1160_, lean_object* v_t_1161_, lean_object* v_h_1162_, lean_object* v_unary_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1161_, v_unary_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim___redArg(lean_object* v_t_1165_, lean_object* v_binary_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1165_, v_binary_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim(lean_object* v_00_u03b1_1168_, lean_object* v_motive_1169_, lean_object* v_t_1170_, lean_object* v_h_1171_, lean_object* v_binary_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1170_, v_binary_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_Parser_registerAliasCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__0));
v___x_1176_ = lean_mk_io_user_error(v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg(lean_object* v_mapRef_1179_, lean_object* v_aliasName_1180_, lean_object* v_value_1181_){
_start:
{
uint8_t v___x_1183_; 
v___x_1183_ = l_Lean_initializing();
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref(v_value_1181_);
lean_dec(v_aliasName_1180_);
v___x_1184_ = lean_obj_once(&l_Lean_Parser_registerAliasCore___redArg___closed__1, &l_Lean_Parser_registerAliasCore___redArg___closed__1_once, _init_l_Lean_Parser_registerAliasCore___redArg___closed__1);
v___x_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
else
{
lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = lean_st_ref_get(v_mapRef_1179_);
v___x_1187_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_aliasName_1180_, v___x_1186_);
lean_dec(v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1188_ = lean_st_ref_take(v_mapRef_1179_);
v___x_1189_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1180_, v_value_1181_, v___x_1188_);
v___x_1190_ = lean_st_ref_put(v_mapRef_1179_, v___x_1189_);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec_ref(v_value_1181_);
v___x_1192_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__2));
v___x_1193_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1180_, v___x_1187_);
v___x_1194_ = lean_string_append(v___x_1192_, v___x_1193_);
lean_dec_ref(v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__3));
v___x_1196_ = lean_string_append(v___x_1194_, v___x_1195_);
v___x_1197_ = lean_mk_io_user_error(v___x_1196_);
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg___boxed(lean_object* v_mapRef_1199_, lean_object* v_aliasName_1200_, lean_object* v_value_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1199_, v_aliasName_1200_, v_value_1201_);
lean_dec(v_mapRef_1199_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore(lean_object* v_00_u03b1_1204_, lean_object* v_mapRef_1205_, lean_object* v_aliasName_1206_, lean_object* v_value_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1205_, v_aliasName_1206_, v_value_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___boxed(lean_object* v_00_u03b1_1210_, lean_object* v_mapRef_1211_, lean_object* v_aliasName_1212_, lean_object* v_value_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Parser_registerAliasCore(v_00_u03b1_1210_, v_mapRef_1211_, v_aliasName_1212_, v_value_1213_);
lean_dec(v_mapRef_1211_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg(lean_object* v_mapRef_1216_, lean_object* v_aliasName_1217_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_st_ref_get(v_mapRef_1216_);
v___x_1220_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1219_, v_aliasName_1217_);
lean_dec(v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg___boxed(lean_object* v_mapRef_1222_, lean_object* v_aliasName_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1222_, v_aliasName_1223_);
lean_dec(v_aliasName_1223_);
lean_dec(v_mapRef_1222_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias(lean_object* v_00_u03b1_1226_, lean_object* v_mapRef_1227_, lean_object* v_aliasName_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1227_, v_aliasName_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___boxed(lean_object* v_00_u03b1_1231_, lean_object* v_mapRef_1232_, lean_object* v_aliasName_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Parser_getAlias(v_00_u03b1_1231_, v_mapRef_1232_, v_aliasName_1233_);
lean_dec(v_aliasName_1233_);
lean_dec(v_mapRef_1232_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object* v_mapRef_1240_, lean_object* v_aliasName_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1283_; 
v___x_1243_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1240_, v_aliasName_1241_);
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1283_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1283_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
if (lean_obj_tag(v_a_1244_) == 0)
{
lean_object* v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1248_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1249_ = 1;
v___x_1250_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1241_, v___x_1249_);
v___x_1251_ = lean_string_append(v___x_1248_, v___x_1250_);
lean_dec_ref(v___x_1250_);
v___x_1252_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1253_ = lean_string_append(v___x_1251_, v___x_1252_);
v___x_1254_ = lean_mk_io_user_error(v___x_1253_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 1);
lean_ctor_set(v___x_1246_, 0, v___x_1254_);
v___x_1256_ = v___x_1246_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
else
{
lean_object* v_val_1258_; 
v_val_1258_ = lean_ctor_get(v_a_1244_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v_a_1244_, 1);
switch(lean_obj_tag(v_val_1258_))
{
case 0:
{
lean_object* v_p_1259_; lean_object* v___x_1261_; 
lean_dec(v_aliasName_1241_);
v_p_1259_ = lean_ctor_get(v_val_1258_, 0);
lean_inc(v_p_1259_);
lean_dec_ref_known(v_val_1258_, 1);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v_p_1259_);
v___x_1261_ = v___x_1246_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_p_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
case 1:
{
lean_object* v___x_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
lean_dec_ref_known(v_val_1258_, 1);
v___x_1263_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1264_ = 1;
v___x_1265_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1241_, v___x_1264_);
v___x_1266_ = lean_string_append(v___x_1263_, v___x_1265_);
lean_dec_ref(v___x_1265_);
v___x_1267_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__2));
v___x_1268_ = lean_string_append(v___x_1266_, v___x_1267_);
v___x_1269_ = lean_mk_io_user_error(v___x_1268_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 1);
lean_ctor_set(v___x_1246_, 0, v___x_1269_);
v___x_1271_ = v___x_1246_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
default: 
{
lean_object* v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
lean_dec_ref_known(v_val_1258_, 1);
v___x_1273_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1274_ = 1;
v___x_1275_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1241_, v___x_1274_);
v___x_1276_ = lean_string_append(v___x_1273_, v___x_1275_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__3));
v___x_1278_ = lean_string_append(v___x_1276_, v___x_1277_);
v___x_1279_ = lean_mk_io_user_error(v___x_1278_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 1);
lean_ctor_set(v___x_1246_, 0, v___x_1279_);
v___x_1281_ = v___x_1246_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object* v_mapRef_1284_, lean_object* v_aliasName_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1284_, v_aliasName_1285_);
lean_dec(v_mapRef_1284_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object* v_00_u03b1_1288_, lean_object* v_mapRef_1289_, lean_object* v_aliasName_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1289_, v_aliasName_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object* v_00_u03b1_1293_, lean_object* v_mapRef_1294_, lean_object* v_aliasName_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Parser_getConstAlias(v_00_u03b1_1293_, v_mapRef_1294_, v_aliasName_1295_);
lean_dec(v_mapRef_1294_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object* v_mapRef_1299_, lean_object* v_aliasName_1300_){
_start:
{
lean_object* v___x_1302_; lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1332_; 
v___x_1302_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1299_, v_aliasName_1300_);
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1332_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1332_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
if (lean_obj_tag(v_a_1303_) == 0)
{
lean_object* v___x_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1307_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1308_ = 1;
v___x_1309_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1300_, v___x_1308_);
v___x_1310_ = lean_string_append(v___x_1307_, v___x_1309_);
lean_dec_ref(v___x_1309_);
v___x_1311_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1312_ = lean_string_append(v___x_1310_, v___x_1311_);
v___x_1313_ = lean_mk_io_user_error(v___x_1312_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 1);
lean_ctor_set(v___x_1305_, 0, v___x_1313_);
v___x_1315_ = v___x_1305_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
else
{
lean_object* v_val_1317_; 
v_val_1317_ = lean_ctor_get(v_a_1303_, 0);
lean_inc(v_val_1317_);
lean_dec_ref_known(v_a_1303_, 1);
if (lean_obj_tag(v_val_1317_) == 1)
{
lean_object* v_p_1318_; lean_object* v___x_1320_; 
lean_dec(v_aliasName_1300_);
v_p_1318_ = lean_ctor_get(v_val_1317_, 0);
lean_inc(v_p_1318_);
lean_dec_ref_known(v_val_1317_, 1);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v_p_1318_);
v___x_1320_ = v___x_1305_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_p_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
else
{
lean_object* v___x_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
lean_dec(v_val_1317_);
v___x_1322_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1323_ = 1;
v___x_1324_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1300_, v___x_1323_);
v___x_1325_ = lean_string_append(v___x_1322_, v___x_1324_);
lean_dec_ref(v___x_1324_);
v___x_1326_ = ((lean_object*)(l_Lean_Parser_getUnaryAlias___redArg___closed__0));
v___x_1327_ = lean_string_append(v___x_1325_, v___x_1326_);
v___x_1328_ = lean_mk_io_user_error(v___x_1327_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 1);
lean_ctor_set(v___x_1305_, 0, v___x_1328_);
v___x_1330_ = v___x_1305_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object* v_mapRef_1333_, lean_object* v_aliasName_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1333_, v_aliasName_1334_);
lean_dec(v_mapRef_1333_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object* v_00_u03b1_1337_, lean_object* v_mapRef_1338_, lean_object* v_aliasName_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1338_, v_aliasName_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object* v_00_u03b1_1342_, lean_object* v_mapRef_1343_, lean_object* v_aliasName_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Parser_getUnaryAlias(v_00_u03b1_1342_, v_mapRef_1343_, v_aliasName_1344_);
lean_dec(v_mapRef_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object* v_mapRef_1348_, lean_object* v_aliasName_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1381_; 
v___x_1351_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1348_, v_aliasName_1349_);
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1381_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1381_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
if (lean_obj_tag(v_a_1352_) == 0)
{
lean_object* v___x_1356_; uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1356_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1357_ = 1;
v___x_1358_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1349_, v___x_1357_);
v___x_1359_ = lean_string_append(v___x_1356_, v___x_1358_);
lean_dec_ref(v___x_1358_);
v___x_1360_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1361_ = lean_string_append(v___x_1359_, v___x_1360_);
v___x_1362_ = lean_mk_io_user_error(v___x_1361_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set_tag(v___x_1354_, 1);
lean_ctor_set(v___x_1354_, 0, v___x_1362_);
v___x_1364_ = v___x_1354_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
else
{
lean_object* v_val_1366_; 
v_val_1366_ = lean_ctor_get(v_a_1352_, 0);
lean_inc(v_val_1366_);
lean_dec_ref_known(v_a_1352_, 1);
if (lean_obj_tag(v_val_1366_) == 2)
{
lean_object* v_p_1367_; lean_object* v___x_1369_; 
lean_dec(v_aliasName_1349_);
v_p_1367_ = lean_ctor_get(v_val_1366_, 0);
lean_inc(v_p_1367_);
lean_dec_ref_known(v_val_1366_, 1);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v_p_1367_);
v___x_1369_ = v___x_1354_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_p_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
else
{
lean_object* v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
lean_dec(v_val_1366_);
v___x_1371_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1372_ = 1;
v___x_1373_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1349_, v___x_1372_);
v___x_1374_ = lean_string_append(v___x_1371_, v___x_1373_);
lean_dec_ref(v___x_1373_);
v___x_1375_ = ((lean_object*)(l_Lean_Parser_getBinaryAlias___redArg___closed__0));
v___x_1376_ = lean_string_append(v___x_1374_, v___x_1375_);
v___x_1377_ = lean_mk_io_user_error(v___x_1376_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set_tag(v___x_1354_, 1);
lean_ctor_set(v___x_1354_, 0, v___x_1377_);
v___x_1379_ = v___x_1354_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg___boxed(lean_object* v_mapRef_1382_, lean_object* v_aliasName_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1382_, v_aliasName_1383_);
lean_dec(v_mapRef_1382_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object* v_00_u03b1_1386_, lean_object* v_mapRef_1387_, lean_object* v_aliasName_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1387_, v_aliasName_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___boxed(lean_object* v_00_u03b1_1391_, lean_object* v_mapRef_1392_, lean_object* v_aliasName_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Parser_getBinaryAlias(v_00_u03b1_1391_, v_mapRef_1392_, v_aliasName_1393_);
lean_dec(v_mapRef_1392_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = lean_box(1);
v___x_1398_ = lean_st_mk_ref(v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = lean_box(1);
v___x_1404_ = lean_st_mk_ref(v___x_1403_);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_box(1);
v___x_1410_ = lean_st_mk_ref(v___x_1409_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(lean_object* v_t_1414_, lean_object* v_k_1415_, lean_object* v_fallback_1416_){
_start:
{
if (lean_obj_tag(v_t_1414_) == 0)
{
lean_object* v_k_1417_; lean_object* v_v_1418_; lean_object* v_l_1419_; lean_object* v_r_1420_; uint8_t v___x_1421_; 
v_k_1417_ = lean_ctor_get(v_t_1414_, 1);
v_v_1418_ = lean_ctor_get(v_t_1414_, 2);
v_l_1419_ = lean_ctor_get(v_t_1414_, 3);
v_r_1420_ = lean_ctor_get(v_t_1414_, 4);
v___x_1421_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1415_, v_k_1417_);
switch(v___x_1421_)
{
case 0:
{
v_t_1414_ = v_l_1419_;
goto _start;
}
case 1:
{
lean_inc(v_v_1418_);
return v_v_1418_;
}
default: 
{
v_t_1414_ = v_r_1420_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_1416_);
return v_fallback_1416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg___boxed(lean_object* v_t_1424_, lean_object* v_k_1425_, lean_object* v_fallback_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1424_, v_k_1425_, v_fallback_1426_);
lean_dec(v_fallback_1426_);
lean_dec(v_k_1425_);
lean_dec(v_t_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo(lean_object* v_aliasName_1434_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1436_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1437_ = lean_st_ref_get(v___x_1436_);
v___x_1438_ = ((lean_object*)(l_Lean_Parser_getParserAliasInfo___closed__1));
v___x_1439_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v___x_1437_, v_aliasName_1434_, v___x_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo___boxed(lean_object* v_aliasName_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Parser_getParserAliasInfo(v_aliasName_1441_);
lean_dec(v_aliasName_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(lean_object* v_00_u03b4_1444_, lean_object* v_t_1445_, lean_object* v_k_1446_, lean_object* v_fallback_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1445_, v_k_1446_, v_fallback_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___boxed(lean_object* v_00_u03b4_1449_, lean_object* v_t_1450_, lean_object* v_k_1451_, lean_object* v_fallback_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(v_00_u03b4_1449_, v_t_1450_, v_k_1451_, v_fallback_1452_);
lean_dec(v_fallback_1452_);
lean_dec(v_k_1451_);
lean_dec(v_t_1450_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object* v_aliasName_1454_, lean_object* v_declName_1455_, lean_object* v_p_1456_, lean_object* v_kind_x3f_1457_, lean_object* v_info_1458_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = l_Lean_Parser_parserAliasesRef;
lean_inc(v_aliasName_1454_);
v___x_1477_ = l_Lean_Parser_registerAliasCore___redArg(v___x_1476_, v_aliasName_1454_, v_p_1456_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_dec_ref_known(v___x_1477_, 1);
if (lean_obj_tag(v_kind_x3f_1457_) == 1)
{
lean_object* v_val_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_val_1478_ = lean_ctor_get(v_kind_x3f_1457_, 0);
lean_inc(v_val_1478_);
lean_dec_ref_known(v_kind_x3f_1457_, 1);
v___x_1479_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1480_ = lean_st_ref_take(v___x_1479_);
lean_inc(v_aliasName_1454_);
v___x_1481_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1454_, v_val_1478_, v___x_1480_);
v___x_1482_ = lean_st_ref_put(v___x_1479_, v___x_1481_);
goto v___jp_1460_;
}
else
{
lean_dec(v_kind_x3f_1457_);
goto v___jp_1460_;
}
}
else
{
lean_dec_ref(v_info_1458_);
lean_dec(v_kind_x3f_1457_);
lean_dec(v_declName_1455_);
lean_dec(v_aliasName_1454_);
return v___x_1477_;
}
v___jp_1460_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v_stackSz_x3f_1463_; uint8_t v_autoGroupArgs_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1474_; 
v___x_1461_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1462_ = lean_st_ref_take(v___x_1461_);
v_stackSz_x3f_1463_ = lean_ctor_get(v_info_1458_, 1);
v_autoGroupArgs_1464_ = lean_ctor_get_uint8(v_info_1458_, sizeof(void*)*2);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_info_1458_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v_info_1458_, 0);
lean_dec(v_unused_1475_);
v___x_1466_ = v_info_1458_;
v_isShared_1467_ = v_isSharedCheck_1474_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_stackSz_x3f_1463_);
lean_dec(v_info_1458_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1474_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v_declName_1455_);
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_declName_1455_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_stackSz_x3f_1463_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*2, v_autoGroupArgs_1464_);
v___x_1469_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1454_, v___x_1469_, v___x_1462_);
v___x_1471_ = lean_st_ref_put(v___x_1461_, v___x_1470_);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias___boxed(lean_object* v_aliasName_1483_, lean_object* v_declName_1484_, lean_object* v_p_1485_, lean_object* v_kind_x3f_1486_, lean_object* v_info_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Parser_registerAlias(v_aliasName_1483_, v_declName_1484_, v_p_1485_, v_kind_x3f_1486_, v_info_1487_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue___lam__0(lean_object* v_p_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_p_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0(lean_object* v_p_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_p_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0(lean_object* v_p_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_p_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object* v_aliasName_1502_){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1520_; 
v___x_1504_ = l_Lean_Parser_parserAliasesRef;
v___x_1505_ = l_Lean_Parser_getAlias___redArg(v___x_1504_, v_aliasName_1502_);
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1520_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1520_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
if (lean_obj_tag(v_a_1506_) == 1)
{
uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
lean_dec_ref_known(v_a_1506_, 1);
v___x_1510_ = 1;
v___x_1511_ = lean_box(v___x_1510_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1511_);
v___x_1513_ = v___x_1508_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
else
{
uint8_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
lean_dec(v_a_1506_);
v___x_1515_ = 0;
v___x_1516_ = lean_box(v___x_1515_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1516_);
v___x_1518_ = v___x_1508_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object* v_aliasName_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Parser_isParserAlias(v_aliasName_1521_);
lean_dec(v_aliasName_1521_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object* v_aliasName_1524_){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1526_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1527_ = lean_st_ref_get(v___x_1526_);
v___x_1528_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1527_, v_aliasName_1524_);
lean_dec(v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f___boxed(lean_object* v_aliasName_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v_aliasName_1530_);
lean_dec(v_aliasName_1530_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object* v_aliasName_1533_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = l_Lean_Parser_parserAliasesRef;
v___x_1536_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1535_, v_aliasName_1533_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1544_; 
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v___x_1536_, 0);
lean_dec(v_unused_1545_);
v___x_1538_ = v___x_1536_;
v_isShared_1539_ = v_isSharedCheck_1544_;
goto v_resetjp_1537_;
}
else
{
lean_dec(v___x_1536_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1544_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = lean_box(0);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1540_);
v___x_1542_ = v___x_1538_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
v_a_1546_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1536_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1536_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias___boxed(lean_object* v_aliasName_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_Parser_ensureUnaryParserAlias(v_aliasName_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object* v_aliasName_1557_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = l_Lean_Parser_parserAliasesRef;
v___x_1560_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1559_, v_aliasName_1557_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1568_; 
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v___x_1560_, 0);
lean_dec(v_unused_1569_);
v___x_1562_ = v___x_1560_;
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v___x_1560_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = lean_box(0);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1564_);
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
v_a_1570_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1560_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1560_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias___boxed(lean_object* v_aliasName_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_Parser_ensureBinaryParserAlias(v_aliasName_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object* v_aliasName_1581_){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = l_Lean_Parser_parserAliasesRef;
v___x_1584_ = l_Lean_Parser_getConstAlias___redArg(v___x_1583_, v_aliasName_1581_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1592_; 
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v___x_1584_, 0);
lean_dec(v_unused_1593_);
v___x_1586_ = v___x_1584_;
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
else
{
lean_dec(v___x_1584_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = lean_box(0);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1588_);
v___x_1590_ = v___x_1586_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
v_a_1594_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1584_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1584_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias___boxed(lean_object* v_aliasName_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_Parser_ensureConstantParserAlias(v_aliasName_1602_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* v_constName_1613_, lean_object* v_compileParserDescr_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_env_1626_; lean_object* v_opts_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; 
v_env_1626_ = lean_ctor_get(v_a_1615_, 0);
v_opts_1627_ = lean_ctor_get(v_a_1615_, 1);
v___x_1628_ = 0;
lean_inc(v_constName_1613_);
lean_inc_ref(v_env_1626_);
v___x_1629_ = l_Lean_Environment_find_x3f(v_env_1626_, v_constName_1613_, v___x_1628_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v___x_1630_; uint8_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec_ref(v_compileParserDescr_1614_);
v___x_1630_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_1631_ = 1;
v___x_1632_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1613_, v___x_1631_);
v___x_1633_ = lean_string_append(v___x_1630_, v___x_1632_);
lean_dec_ref(v___x_1632_);
v___x_1634_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_1635_ = lean_string_append(v___x_1633_, v___x_1634_);
v___x_1636_ = lean_mk_io_user_error(v___x_1635_);
v___x_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
return v___x_1637_;
}
else
{
lean_object* v_val_1638_; lean_object* v___x_1639_; 
v_val_1638_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_val_1638_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1639_ = l_Lean_ConstantInfo_type(v_val_1638_);
lean_dec(v_val_1638_);
if (lean_obj_tag(v___x_1639_) == 4)
{
lean_object* v_declName_1640_; 
v_declName_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_declName_1640_);
lean_dec_ref_known(v___x_1639_, 2);
if (lean_obj_tag(v_declName_1640_) == 1)
{
lean_object* v_pre_1641_; 
v_pre_1641_ = lean_ctor_get(v_declName_1640_, 0);
lean_inc(v_pre_1641_);
if (lean_obj_tag(v_pre_1641_) == 1)
{
lean_object* v_pre_1642_; 
v_pre_1642_ = lean_ctor_get(v_pre_1641_, 0);
switch(lean_obj_tag(v_pre_1642_))
{
case 1:
{
lean_object* v_pre_1643_; 
lean_inc_ref(v_pre_1642_);
lean_dec_ref(v_compileParserDescr_1614_);
v_pre_1643_ = lean_ctor_get(v_pre_1642_, 0);
if (lean_obj_tag(v_pre_1643_) == 0)
{
lean_object* v_str_1644_; lean_object* v_str_1645_; lean_object* v_str_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v_str_1644_ = lean_ctor_get(v_declName_1640_, 1);
lean_inc_ref(v_str_1644_);
lean_dec_ref_known(v_declName_1640_, 2);
v_str_1645_ = lean_ctor_get(v_pre_1641_, 1);
lean_inc_ref(v_str_1645_);
lean_dec_ref_known(v_pre_1641_, 2);
v_str_1646_ = lean_ctor_get(v_pre_1642_, 1);
lean_inc_ref(v_str_1646_);
lean_dec_ref_known(v_pre_1642_, 2);
v___x_1647_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1648_ = lean_string_dec_eq(v_str_1646_, v___x_1647_);
lean_dec_ref(v_str_1646_);
if (v___x_1648_ == 0)
{
lean_dec_ref(v_str_1645_);
lean_dec_ref(v_str_1644_);
goto v___jp_1617_;
}
else
{
lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_1650_ = lean_string_dec_eq(v_str_1645_, v___x_1649_);
lean_dec_ref(v_str_1645_);
if (v___x_1650_ == 0)
{
lean_dec_ref(v_str_1644_);
goto v___jp_1617_;
}
else
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_1652_ = lean_string_dec_eq(v_str_1644_, v___x_1651_);
if (v___x_1652_ == 0)
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_string_dec_eq(v_str_1644_, v___x_1649_);
lean_dec_ref(v_str_1644_);
if (v___x_1653_ == 0)
{
goto v___jp_1617_;
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = l_Lean_Environment_evalConst___redArg(v_env_1626_, v_opts_1627_, v_constName_1613_, v___x_1653_);
lean_dec(v_constName_1613_);
v___x_1655_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1654_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1665_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1665_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1665_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1660_ = lean_box(v___x_1653_);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v_a_1656_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1661_);
v___x_1663_ = v___x_1658_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_a_1666_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1655_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1655_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec_ref(v_str_1644_);
v___x_1674_ = l_Lean_Environment_evalConst___redArg(v_env_1626_, v_opts_1627_, v_constName_1613_, v___x_1652_);
lean_dec(v_constName_1613_);
v___x_1675_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1674_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1685_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1680_ = lean_box(v___x_1628_);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v_a_1676_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1681_);
v___x_1683_ = v___x_1678_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
v_a_1686_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1675_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1675_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1642_, 2);
lean_dec_ref_known(v_pre_1641_, 2);
lean_dec_ref_known(v_declName_1640_, 2);
goto v___jp_1617_;
}
}
case 0:
{
lean_object* v_str_1694_; lean_object* v_str_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_str_1694_ = lean_ctor_get(v_declName_1640_, 1);
lean_inc_ref(v_str_1694_);
lean_dec_ref_known(v_declName_1640_, 2);
v_str_1695_ = lean_ctor_get(v_pre_1641_, 1);
lean_inc_ref(v_str_1695_);
lean_dec_ref_known(v_pre_1641_, 2);
v___x_1696_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1697_ = lean_string_dec_eq(v_str_1695_, v___x_1696_);
lean_dec_ref(v_str_1695_);
if (v___x_1697_ == 0)
{
lean_dec_ref(v_str_1694_);
lean_dec_ref(v_compileParserDescr_1614_);
goto v___jp_1617_;
}
else
{
lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_1699_ = lean_string_dec_eq(v_str_1694_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_1701_ = lean_string_dec_eq(v_str_1694_, v___x_1700_);
lean_dec_ref(v_str_1694_);
if (v___x_1701_ == 0)
{
lean_dec_ref(v_compileParserDescr_1614_);
goto v___jp_1617_;
}
else
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = l_Lean_Environment_evalConst___redArg(v_env_1626_, v_opts_1627_, v_constName_1613_, v___x_1701_);
lean_dec(v_constName_1613_);
v___x_1703_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1702_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1705_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
lean_inc_ref(v_a_1615_);
v___x_1705_ = lean_apply_3(v_compileParserDescr_1614_, v_a_1704_, v_a_1615_, lean_box(0));
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1715_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1715_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1715_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1710_ = lean_box(v___x_1699_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
lean_ctor_set(v___x_1711_, 1, v_a_1706_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1711_);
v___x_1713_ = v___x_1708_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
v_a_1716_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1705_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1705_);
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
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v_compileParserDescr_1614_);
v_a_1724_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1703_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1703_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
else
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec_ref(v_str_1694_);
v___x_1732_ = l_Lean_Environment_evalConst___redArg(v_env_1626_, v_opts_1627_, v_constName_1613_, v___x_1699_);
lean_dec(v_constName_1613_);
v___x_1733_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1732_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1735_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1733_, 1);
lean_inc_ref(v_a_1615_);
v___x_1735_ = lean_apply_3(v_compileParserDescr_1614_, v_a_1734_, v_a_1615_, lean_box(0));
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1745_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1745_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1745_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1740_ = lean_box(v___x_1699_);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
lean_ctor_set(v___x_1741_, 1, v_a_1736_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1741_);
v___x_1743_ = v___x_1738_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
v_a_1746_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1735_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1735_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v_compileParserDescr_1614_);
v_a_1754_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1733_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1733_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_pre_1641_, 2);
lean_dec_ref_known(v_declName_1640_, 2);
lean_dec_ref(v_compileParserDescr_1614_);
goto v___jp_1617_;
}
}
}
else
{
lean_dec(v_pre_1641_);
lean_dec_ref_known(v_declName_1640_, 2);
lean_dec_ref(v_compileParserDescr_1614_);
goto v___jp_1617_;
}
}
else
{
lean_dec(v_declName_1640_);
lean_dec_ref(v_compileParserDescr_1614_);
goto v___jp_1617_;
}
}
else
{
lean_dec_ref(v___x_1639_);
lean_dec_ref(v_compileParserDescr_1614_);
goto v___jp_1617_;
}
}
v___jp_1617_:
{
lean_object* v___x_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1618_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__0));
v___x_1619_ = 1;
v___x_1620_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1613_, v___x_1619_);
v___x_1621_ = lean_string_append(v___x_1618_, v___x_1620_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1));
v___x_1623_ = lean_string_append(v___x_1621_, v___x_1622_);
v___x_1624_ = lean_mk_io_user_error(v___x_1623_);
v___x_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object* v_constName_1762_, lean_object* v_compileParserDescr_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1762_, v_compileParserDescr_1763_, v_a_1764_);
lean_dec_ref(v_a_1764_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed(lean_object* v_categories_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1767_, v_a_1768_, v_a_1769_);
lean_dec_ref(v_a_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(lean_object* v_categories_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
switch(lean_obj_tag(v_a_1773_))
{
case 0:
{
lean_object* v_name_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_dec_ref(v_categories_1772_);
v_name_1776_ = lean_ctor_get(v_a_1773_, 0);
lean_inc(v_name_1776_);
lean_dec_ref_known(v_a_1773_, 1);
v___x_1777_ = l_Lean_Parser_parserAliasesRef;
v___x_1778_ = l_Lean_Parser_getConstAlias___redArg(v___x_1777_, v_name_1776_);
return v___x_1778_;
}
case 1:
{
lean_object* v_name_1779_; lean_object* v_p_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_name_1779_ = lean_ctor_get(v_a_1773_, 0);
lean_inc(v_name_1779_);
v_p_1780_ = lean_ctor_get(v_a_1773_, 1);
lean_inc_ref(v_p_1780_);
lean_dec_ref_known(v_a_1773_, 2);
v___x_1781_ = l_Lean_Parser_parserAliasesRef;
v___x_1782_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1781_, v_name_1779_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v___x_1784_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1772_, v_p_1780_, v_a_1774_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1793_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1793_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1793_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = lean_apply_1(v_a_1783_, v_a_1785_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1789_);
v___x_1791_ = v___x_1787_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
else
{
lean_dec(v_a_1783_);
return v___x_1784_;
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec_ref(v_p_1780_);
lean_dec_ref(v_categories_1772_);
v_a_1794_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1782_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1782_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
case 2:
{
lean_object* v_name_1802_; lean_object* v_p_u2081_1803_; lean_object* v_p_u2082_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_name_1802_ = lean_ctor_get(v_a_1773_, 0);
lean_inc(v_name_1802_);
v_p_u2081_1803_ = lean_ctor_get(v_a_1773_, 1);
lean_inc_ref(v_p_u2081_1803_);
v_p_u2082_1804_ = lean_ctor_get(v_a_1773_, 2);
lean_inc_ref(v_p_u2082_1804_);
lean_dec_ref_known(v_a_1773_, 3);
v___x_1805_ = l_Lean_Parser_parserAliasesRef;
v___x_1806_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1805_, v_name_1802_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1808_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
lean_dec_ref_known(v___x_1806_, 1);
lean_inc_ref(v_categories_1772_);
v___x_1808_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1772_, v_p_u2081_1803_, v_a_1774_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1772_, v_p_u2082_1804_, v_a_1774_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1819_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_apply_2(v_a_1807_, v_a_1809_, v_a_1811_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
else
{
lean_dec(v_a_1809_);
lean_dec(v_a_1807_);
return v___x_1810_;
}
}
else
{
lean_dec(v_a_1807_);
lean_dec_ref(v_p_u2082_1804_);
lean_dec_ref(v_categories_1772_);
return v___x_1808_;
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec_ref(v_p_u2082_1804_);
lean_dec_ref(v_p_u2081_1803_);
lean_dec_ref(v_categories_1772_);
v_a_1820_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1806_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1806_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
case 3:
{
lean_object* v_kind_1828_; lean_object* v_prec_1829_; lean_object* v_p_1830_; lean_object* v___x_1831_; 
v_kind_1828_ = lean_ctor_get(v_a_1773_, 0);
lean_inc(v_kind_1828_);
v_prec_1829_ = lean_ctor_get(v_a_1773_, 1);
lean_inc(v_prec_1829_);
v_p_1830_ = lean_ctor_get(v_a_1773_, 2);
lean_inc_ref(v_p_1830_);
lean_dec_ref_known(v_a_1773_, 3);
v___x_1831_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1772_, v_p_1830_, v_a_1774_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1840_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1836_ = l_Lean_Parser_leadingNode(v_kind_1828_, v_prec_1829_, v_a_1832_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1836_);
v___x_1838_ = v___x_1834_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
else
{
lean_dec(v_prec_1829_);
lean_dec(v_kind_1828_);
return v___x_1831_;
}
}
case 4:
{
lean_object* v_kind_1841_; lean_object* v_prec_1842_; lean_object* v_lhsPrec_1843_; lean_object* v_p_1844_; lean_object* v___x_1845_; 
v_kind_1841_ = lean_ctor_get(v_a_1773_, 0);
lean_inc(v_kind_1841_);
v_prec_1842_ = lean_ctor_get(v_a_1773_, 1);
lean_inc(v_prec_1842_);
v_lhsPrec_1843_ = lean_ctor_get(v_a_1773_, 2);
lean_inc(v_lhsPrec_1843_);
v_p_1844_ = lean_ctor_get(v_a_1773_, 3);
lean_inc_ref(v_p_1844_);
lean_dec_ref_known(v_a_1773_, 4);
v___x_1845_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1772_, v_p_1844_, v_a_1774_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1854_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = l_Lean_Parser_trailingNode(v_kind_1841_, v_prec_1842_, v_lhsPrec_1843_, v_a_1846_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
else
{
lean_dec(v_lhsPrec_1843_);
lean_dec(v_prec_1842_);
lean_dec(v_kind_1841_);
return v___x_1845_;
}
}
case 5:
{
lean_object* v_val_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1863_; 
lean_dec_ref(v_categories_1772_);
v_val_1855_ = lean_ctor_get(v_a_1773_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_a_1773_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1857_ = v_a_1773_;
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_val_1855_);
lean_dec(v_a_1773_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = l_Lean_Parser_symbol(v_val_1855_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1859_);
v___x_1861_ = v___x_1857_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
case 6:
{
lean_object* v_val_1864_; uint8_t v_includeIdent_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_dec_ref(v_categories_1772_);
v_val_1864_ = lean_ctor_get(v_a_1773_, 0);
lean_inc_ref(v_val_1864_);
v_includeIdent_1865_ = lean_ctor_get_uint8(v_a_1773_, sizeof(void*)*1);
lean_dec_ref_known(v_a_1773_, 1);
v___x_1866_ = l_Lean_Parser_nonReservedSymbol(v_val_1864_, v_includeIdent_1865_);
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
return v___x_1867_;
}
case 7:
{
lean_object* v_catName_1868_; lean_object* v_rbp_1869_; lean_object* v___x_1870_; 
v_catName_1868_ = lean_ctor_get(v_a_1773_, 0);
lean_inc(v_catName_1868_);
v_rbp_1869_ = lean_ctor_get(v_a_1773_, 1);
lean_inc(v_rbp_1869_);
lean_dec_ref_known(v_a_1773_, 2);
v___x_1870_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_1772_, v_catName_1868_);
lean_dec_ref(v_categories_1772_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec(v_rbp_1869_);
v___x_1871_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_1868_);
v___x_1872_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1871_);
return v___x_1872_;
}
else
{
lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1880_; 
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v___x_1870_, 0);
lean_dec(v_unused_1881_);
v___x_1874_ = v___x_1870_;
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
else
{
lean_dec(v___x_1870_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = l_Lean_Parser_categoryParser(v_catName_1868_, v_rbp_1869_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1876_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
case 8:
{
lean_object* v_declName_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_declName_1882_ = lean_ctor_get(v_a_1773_, 0);
lean_inc(v_declName_1882_);
lean_dec_ref_known(v_a_1773_, 1);
v___x_1883_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed), 4, 1);
lean_closure_set(v___x_1883_, 0, v_categories_1772_);
v___x_1884_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_declName_1882_, v___x_1883_, v_a_1774_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1893_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1893_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1893_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v_snd_1889_; lean_object* v___x_1891_; 
v_snd_1889_ = lean_ctor_get(v_a_1885_, 1);
lean_inc(v_snd_1889_);
lean_dec(v_a_1885_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v_snd_1889_);
v___x_1891_ = v___x_1887_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_snd_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
v_a_1894_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1884_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1884_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
case 9:
{
lean_object* v_name_1902_; lean_object* v_kind_1903_; lean_object* v_p_1904_; lean_object* v___x_1905_; 
v_name_1902_ = lean_ctor_get(v_a_1773_, 0);
lean_inc_ref(v_name_1902_);
v_kind_1903_ = lean_ctor_get(v_a_1773_, 1);
lean_inc(v_kind_1903_);
v_p_1904_ = lean_ctor_get(v_a_1773_, 2);
lean_inc_ref(v_p_1904_);
lean_dec_ref_known(v_a_1773_, 3);
v___x_1905_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1772_, v_p_1904_, v_a_1774_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1916_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1916_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1916_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
uint8_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1910_ = 1;
lean_inc(v_kind_1903_);
v___x_1911_ = l_Lean_Parser_nodeWithAntiquot(v_name_1902_, v_kind_1903_, v_a_1906_, v___x_1910_);
v___x_1912_ = l_Lean_Parser_withCache(v_kind_1903_, v___x_1911_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1912_);
v___x_1914_ = v___x_1908_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
else
{
lean_dec(v_kind_1903_);
lean_dec_ref(v_name_1902_);
return v___x_1905_;
}
}
case 10:
{
lean_object* v_p_1917_; lean_object* v_sep_1918_; lean_object* v_psep_1919_; uint8_t v_allowTrailingSep_1920_; lean_object* v___x_1921_; 
v_p_1917_ = lean_ctor_get(v_a_1773_, 0);
lean_inc_ref(v_p_1917_);
v_sep_1918_ = lean_ctor_get(v_a_1773_, 1);
lean_inc_ref(v_sep_1918_);
v_psep_1919_ = lean_ctor_get(v_a_1773_, 2);
lean_inc_ref(v_psep_1919_);
v_allowTrailingSep_1920_ = lean_ctor_get_uint8(v_a_1773_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1773_, 3);
lean_inc_ref(v_categories_1772_);
v___x_1921_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1772_, v_p_1917_, v_a_1774_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1772_, v_psep_1919_, v_a_1774_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1932_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1932_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1932_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = l_Lean_Parser_sepBy(v_a_1922_, v_sep_1918_, v_a_1924_, v_allowTrailingSep_1920_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1928_);
v___x_1930_ = v___x_1926_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
else
{
lean_dec(v_a_1922_);
lean_dec_ref(v_sep_1918_);
return v___x_1923_;
}
}
else
{
lean_dec_ref(v_psep_1919_);
lean_dec_ref(v_sep_1918_);
lean_dec_ref(v_categories_1772_);
return v___x_1921_;
}
}
case 11:
{
lean_object* v_p_1933_; lean_object* v_sep_1934_; lean_object* v_psep_1935_; uint8_t v_allowTrailingSep_1936_; lean_object* v___x_1937_; 
v_p_1933_ = lean_ctor_get(v_a_1773_, 0);
lean_inc_ref(v_p_1933_);
v_sep_1934_ = lean_ctor_get(v_a_1773_, 1);
lean_inc_ref(v_sep_1934_);
v_psep_1935_ = lean_ctor_get(v_a_1773_, 2);
lean_inc_ref(v_psep_1935_);
v_allowTrailingSep_1936_ = lean_ctor_get_uint8(v_a_1773_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1773_, 3);
lean_inc_ref(v_categories_1772_);
v___x_1937_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1772_, v_p_1933_, v_a_1774_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1939_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1939_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1772_, v_psep_1935_, v_a_1774_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1948_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1944_ = l_Lean_Parser_sepBy1(v_a_1938_, v_sep_1934_, v_a_1940_, v_allowTrailingSep_1936_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1944_);
v___x_1946_ = v___x_1942_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
else
{
lean_dec(v_a_1938_);
lean_dec_ref(v_sep_1934_);
return v___x_1939_;
}
}
else
{
lean_dec_ref(v_psep_1935_);
lean_dec_ref(v_sep_1934_);
lean_dec_ref(v_categories_1772_);
return v___x_1937_;
}
}
default: 
{
lean_object* v_val_1949_; lean_object* v_asciiVal_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec_ref(v_categories_1772_);
v_val_1949_ = lean_ctor_get(v_a_1773_, 0);
lean_inc_ref(v_val_1949_);
v_asciiVal_1950_ = lean_ctor_get(v_a_1773_, 1);
lean_inc_ref(v_asciiVal_1950_);
lean_dec_ref_known(v_a_1773_, 2);
v___x_1951_ = l_Lean_Parser_unicodeSymbol___redArg(v_val_1949_, v_asciiVal_1950_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
return v___x_1952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object* v_categories_1953_, lean_object* v_d_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1953_, v_d_1954_, v_a_1955_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object* v_categories_1958_, lean_object* v_d_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_Parser_compileParserDescr(v_categories_1958_, v_d_1959_, v_a_1960_);
lean_dec_ref(v_a_1960_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0(lean_object* v_categories_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1963_, v___y_1964_, v___y_1965_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0___boxed(lean_object* v_categories_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Parser_mkParserOfConstant___lam__0(v_categories_1968_, v___y_1969_, v___y_1970_);
lean_dec_ref(v___y_1970_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* v_categories_1973_, lean_object* v_constName_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___f_1977_; lean_object* v___x_1978_; 
v___f_1977_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserOfConstant___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1977_, 0, v_categories_1973_);
v___x_1978_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1974_, v___f_1977_, v_a_1975_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___boxed(lean_object* v_categories_1979_, lean_object* v_constName_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Parser_mkParserOfConstant(v_categories_1979_, v_constName_1980_, v_a_1981_);
lean_dec_ref(v_a_1981_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = lean_box(0);
v___x_1986_ = lean_st_mk_ref(v___x_1985_);
v___x_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object* v_hook_1990_){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1992_ = l_Lean_Parser_parserAttributeHooks;
v___x_1993_ = lean_st_ref_take(v___x_1992_);
v___x_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1994_, 0, v_hook_1990_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_st_ref_put(v___x_1992_, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook___boxed(lean_object* v_hook_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_Parser_registerParserAttributeHook(v_hook_1997_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(lean_object* v_catName_2000_, lean_object* v_declName_2001_, uint8_t v_builtin_2002_, lean_object* v_as_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
if (lean_obj_tag(v_as_2003_) == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec(v_declName_2001_);
lean_dec(v_catName_2000_);
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
return v___x_2008_;
}
else
{
lean_object* v_head_2009_; lean_object* v_tail_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_head_2009_ = lean_ctor_get(v_as_2003_, 0);
lean_inc(v_head_2009_);
v_tail_2010_ = lean_ctor_get(v_as_2003_, 1);
lean_inc(v_tail_2010_);
lean_dec_ref_known(v_as_2003_, 2);
v___x_2011_ = lean_box(v_builtin_2002_);
lean_inc(v___y_2005_);
lean_inc_ref(v___y_2004_);
lean_inc(v_declName_2001_);
lean_inc(v_catName_2000_);
v___x_2012_ = lean_apply_6(v_head_2009_, v_catName_2000_, v_declName_2001_, v___x_2011_, v___y_2004_, v___y_2005_, lean_box(0));
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_dec_ref_known(v___x_2012_, 1);
v_as_2003_ = v_tail_2010_;
goto _start;
}
else
{
lean_dec(v_tail_2010_);
lean_dec(v_declName_2001_);
lean_dec(v_catName_2000_);
return v___x_2012_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0___boxed(lean_object* v_catName_2014_, lean_object* v_declName_2015_, lean_object* v_builtin_2016_, lean_object* v_as_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
uint8_t v_builtin_boxed_2021_; lean_object* v_res_2022_; 
v_builtin_boxed_2021_ = lean_unbox(v_builtin_2016_);
v_res_2022_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2014_, v_declName_2015_, v_builtin_boxed_2021_, v_as_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object* v_catName_2023_, lean_object* v_declName_2024_, uint8_t v_builtin_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = l_Lean_Parser_parserAttributeHooks;
v___x_2030_ = lean_st_ref_get(v___x_2029_);
v___x_2031_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2023_, v_declName_2024_, v_builtin_2025_, v___x_2030_, v_a_2026_, v_a_2027_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object* v_catName_2032_, lean_object* v_declName_2033_, lean_object* v_builtin_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
uint8_t v_builtin_boxed_2038_; lean_object* v_res_2039_; 
v_builtin_boxed_2038_ = lean_unbox(v_builtin_2034_);
v_res_2039_ = l_Lean_Parser_runParserAttributeHooks(v_catName_2032_, v_declName_2033_, v_builtin_boxed_2038_, v_a_2035_, v_a_2036_);
lean_dec(v_a_2036_);
lean_dec_ref(v_a_2035_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2040_, lean_object* v_decl_2041_, lean_object* v_stx_2042_, uint8_t v_x_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2042_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2047_) == 0)
{
uint8_t v___x_2048_; lean_object* v___x_2049_; 
lean_dec_ref_known(v___x_2047_, 1);
v___x_2048_ = 1;
v___x_2049_ = l_Lean_Parser_runParserAttributeHooks(v___x_2040_, v_decl_2041_, v___x_2048_, v___y_2044_, v___y_2045_);
return v___x_2049_;
}
else
{
lean_dec(v_decl_2041_);
lean_dec(v___x_2040_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2050_, lean_object* v_decl_2051_, lean_object* v_stx_2052_, lean_object* v_x_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
uint8_t v_x_1082__boxed_2057_; lean_object* v_res_2058_; 
v_x_1082__boxed_2057_ = lean_unbox(v_x_2053_);
v_res_2058_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2050_, v_decl_2051_, v_stx_2052_, v_x_1082__boxed_2057_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2058_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
lean_ctor_set(v___x_2064_, 2, v___x_2063_);
lean_ctor_set(v___x_2064_, 3, v___x_2063_);
lean_ctor_set(v___x_2064_, 4, v___x_2062_);
lean_ctor_set(v___x_2064_, 5, v___x_2062_);
lean_ctor_set(v___x_2064_, 6, v___x_2062_);
lean_ctor_set(v___x_2064_, 7, v___x_2062_);
lean_ctor_set(v___x_2064_, 8, v___x_2062_);
lean_ctor_set(v___x_2064_, 9, v___x_2062_);
lean_ctor_set(v___x_2064_, 10, v___x_2062_);
return v___x_2064_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_unsigned_to_nat(32u);
v___x_2066_ = lean_mk_empty_array_with_capacity(v___x_2065_);
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
return v___x_2067_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2068_ = ((size_t)5ULL);
v___x_2069_ = lean_unsigned_to_nat(0u);
v___x_2070_ = lean_unsigned_to_nat(32u);
v___x_2071_ = lean_mk_empty_array_with_capacity(v___x_2070_);
v___x_2072_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2073_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
lean_ctor_set(v___x_2073_, 1, v___x_2071_);
lean_ctor_set(v___x_2073_, 2, v___x_2069_);
lean_ctor_set(v___x_2073_, 3, v___x_2069_);
lean_ctor_set_usize(v___x_2073_, 4, v___x_2068_);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2074_ = lean_box(1);
v___x_2075_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2076_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2077_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v___x_2075_);
lean_ctor_set(v___x_2077_, 2, v___x_2074_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v___x_2082_; lean_object* v_env_2083_; lean_object* v_options_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2082_ = lean_st_ref_get(v___y_2080_);
v_env_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc_ref(v_env_2083_);
lean_dec(v___x_2082_);
v_options_2084_ = lean_ctor_get(v___y_2079_, 2);
v___x_2085_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_2086_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2084_);
v___x_2087_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2087_, 0, v_env_2083_);
lean_ctor_set(v___x_2087_, 1, v___x_2085_);
lean_ctor_set(v___x_2087_, 2, v___x_2086_);
lean_ctor_set(v___x_2087_, 3, v_options_2084_);
v___x_2088_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v_msgData_2078_);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_ref_2099_; lean_object* v___x_2100_; lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2109_; 
v_ref_2099_ = lean_ctor_get(v___y_2096_, 5);
v___x_2100_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msg_2095_, v___y_2096_, v___y_2097_);
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2109_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2109_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
lean_inc(v_ref_2099_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v_ref_2099_);
lean_ctor_set(v___x_2105_, 1, v_a_2101_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set_tag(v___x_2103_, 1);
lean_ctor_set(v___x_2103_, 0, v___x_2105_);
v___x_2107_ = v___x_2103_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
return v_res_2114_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2117_ = l_Lean_stringToMessageData(v___x_2116_);
return v___x_2117_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2120_ = l_Lean_stringToMessageData(v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2121_, lean_object* v_decl_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2126_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2127_ = l_Lean_MessageData_ofName(v___x_2121_);
v___x_2128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2130_, v___y_2123_, v___y_2124_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2132_, lean_object* v_decl_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2132_, v_decl_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v_decl_2133_);
return v_res_2137_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = lean_unsigned_to_nat(3646333153u);
v___x_2181_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2182_ = l_Lean_Name_num___override(v___x_2181_, v___x_2180_);
return v___x_2182_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2185_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2186_ = l_Lean_Name_str___override(v___x_2185_, v___x_2184_);
return v___x_2186_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2189_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2190_ = l_Lean_Name_str___override(v___x_2189_, v___x_2188_);
return v___x_2190_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = lean_unsigned_to_nat(2u);
v___x_2192_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2193_ = l_Lean_Name_num___override(v___x_2192_, v___x_2191_);
return v___x_2193_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2200_ = 0;
v___x_2201_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2202_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2203_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2204_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set(v___x_2204_, 1, v___x_2202_);
lean_ctor_set(v___x_2204_, 2, v___x_2201_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*3, v___x_2200_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2205_; lean_object* v___f_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___f_2205_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___f_2206_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2207_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___f_2206_);
lean_ctor_set(v___x_2208_, 2, v___f_2205_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2211_ = l_Lean_registerBuiltinAttribute(v___x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v_a_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2214_, lean_object* v_msg_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2215_, v___y_2216_, v___y_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2220_, lean_object* v_msg_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(v_00_u03b1_2220_, v_msg_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2226_, lean_object* v_decl_2227_, lean_object* v_stx_2228_, uint8_t v_x_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2228_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2233_) == 0)
{
uint8_t v___x_2234_; lean_object* v___x_2235_; 
lean_dec_ref_known(v___x_2233_, 1);
v___x_2234_ = 0;
v___x_2235_ = l_Lean_Parser_runParserAttributeHooks(v___x_2226_, v_decl_2227_, v___x_2234_, v___y_2230_, v___y_2231_);
return v___x_2235_;
}
else
{
lean_dec(v_decl_2227_);
lean_dec(v___x_2226_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2236_, lean_object* v_decl_2237_, lean_object* v_stx_2238_, lean_object* v_x_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
uint8_t v_x_211__boxed_2243_; lean_object* v_res_2244_; 
v_x_211__boxed_2243_ = lean_unbox(v_x_2239_);
v_res_2244_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2236_, v_decl_2237_, v_stx_2238_, v_x_211__boxed_2243_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2245_, lean_object* v_decl_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2250_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2251_ = l_Lean_MessageData_ofName(v___x_2245_);
v___x_2252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2254_, v___y_2247_, v___y_2248_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2256_, lean_object* v_decl_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2256_, v_decl_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v_decl_2257_);
return v_res_2261_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = lean_unsigned_to_nat(3789407938u);
v___x_2265_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2266_ = l_Lean_Name_num___override(v___x_2265_, v___x_2264_);
return v___x_2266_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2268_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2269_ = l_Lean_Name_str___override(v___x_2268_, v___x_2267_);
return v___x_2269_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2271_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2272_ = l_Lean_Name_str___override(v___x_2271_, v___x_2270_);
return v___x_2272_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2273_ = lean_unsigned_to_nat(2u);
v___x_2274_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2275_ = l_Lean_Name_num___override(v___x_2274_, v___x_2273_);
return v___x_2275_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2282_ = 0;
v___x_2283_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2284_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2285_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2286_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v___x_2284_);
lean_ctor_set(v___x_2286_, 2, v___x_2283_);
lean_ctor_set_uint8(v___x_2286_, sizeof(void*)*3, v___x_2282_);
return v___x_2286_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2287_; lean_object* v___f_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___f_2287_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___f_2288_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2289_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v___f_2288_);
lean_ctor_set(v___x_2290_, 2, v___f_2287_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2293_ = l_Lean_registerBuiltinAttribute(v___x_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object* v_s_2296_, lean_object* v_x_2297_, lean_object* v_a_2298_){
_start:
{
switch(lean_obj_tag(v_x_2297_))
{
case 0:
{
lean_object* v_val_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2308_; 
lean_dec_ref(v_s_2296_);
v_val_2300_ = lean_ctor_get(v_x_2297_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_x_2297_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2302_ = v_x_2297_;
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_val_2300_);
lean_dec(v_x_2297_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_val_2300_);
v___x_2305_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
}
case 1:
{
lean_object* v_val_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_s_2296_);
v_val_2309_ = lean_ctor_get(v_x_2297_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_x_2297_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2311_ = v_x_2297_;
v_isShared_2312_ = v_isSharedCheck_2317_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_val_2309_);
lean_dec(v_x_2297_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2317_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_val_2309_);
v___x_2314_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
return v___x_2315_;
}
}
}
case 2:
{
lean_object* v_catName_2318_; lean_object* v_declName_2319_; uint8_t v_behavior_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v_s_2296_);
v_catName_2318_ = lean_ctor_get(v_x_2297_, 0);
v_declName_2319_ = lean_ctor_get(v_x_2297_, 1);
v_behavior_2320_ = lean_ctor_get_uint8(v_x_2297_, sizeof(void*)*2);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_x_2297_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2322_ = v_x_2297_;
v_isShared_2323_ = v_isSharedCheck_2328_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_declName_2319_);
lean_inc(v_catName_2318_);
lean_dec(v_x_2297_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2328_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_catName_2318_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_declName_2319_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*2, v_behavior_2320_);
v___x_2325_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
}
}
default: 
{
lean_object* v_catName_2329_; lean_object* v_declName_2330_; lean_object* v_prio_2331_; lean_object* v_categories_2332_; lean_object* v___x_2333_; 
v_catName_2329_ = lean_ctor_get(v_x_2297_, 0);
lean_inc(v_catName_2329_);
v_declName_2330_ = lean_ctor_get(v_x_2297_, 1);
lean_inc_n(v_declName_2330_, 2);
v_prio_2331_ = lean_ctor_get(v_x_2297_, 2);
lean_inc(v_prio_2331_);
lean_dec_ref_known(v_x_2297_, 3);
v_categories_2332_ = lean_ctor_get(v_s_2296_, 2);
lean_inc_ref(v_categories_2332_);
lean_dec_ref(v_s_2296_);
v___x_2333_ = l_Lean_Parser_mkParserOfConstant(v_categories_2332_, v_declName_2330_, v_a_2298_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2345_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2345_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2345_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v_fst_2338_; lean_object* v_snd_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; lean_object* v___x_2343_; 
v_fst_2338_ = lean_ctor_get(v_a_2334_, 0);
lean_inc(v_fst_2338_);
v_snd_2339_ = lean_ctor_get(v_a_2334_, 1);
lean_inc(v_snd_2339_);
lean_dec(v_a_2334_);
v___x_2340_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_2340_, 0, v_catName_2329_);
lean_ctor_set(v___x_2340_, 1, v_declName_2330_);
lean_ctor_set(v___x_2340_, 2, v_snd_2339_);
lean_ctor_set(v___x_2340_, 3, v_prio_2331_);
v___x_2341_ = lean_unbox(v_fst_2338_);
lean_dec(v_fst_2338_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*4, v___x_2341_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2340_);
v___x_2343_ = v___x_2336_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2340_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_prio_2331_);
lean_dec(v_declName_2330_);
lean_dec(v_catName_2329_);
v_a_2346_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2333_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2333_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object* v_s_2354_, lean_object* v_x_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(v_s_2354_, v_x_2355_, v_a_2356_);
lean_dec_ref(v_a_2356_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v_x_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2361_, 0, v_a_2360_);
lean_inc_ref_n(v___x_2361_, 2);
v___x_2362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
lean_ctor_set(v___x_2362_, 2, v___x_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_x_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v_x_2363_, v_a_2364_);
lean_dec_ref(v_x_2363_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v___y_2366_){
_start:
{
lean_inc_ref(v___y_2366_);
return v___y_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v___y_2367_);
lean_dec_ref(v___y_2367_);
return v_res_2368_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2379_; lean_object* v___f_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___f_2379_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___f_2380_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2381_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2382_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2383_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2384_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed), 1, 0);
v___x_2385_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2386_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v___x_2384_);
lean_ctor_set(v___x_2386_, 2, v___x_2383_);
lean_ctor_set(v___x_2386_, 3, v___x_2382_);
lean_ctor_set(v___x_2386_, 4, v___x_2381_);
lean_ctor_set(v___x_2386_, 5, v___f_2380_);
lean_ctor_set(v___x_2386_, 6, v___f_2379_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_);
v___x_2389_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object* v_env_2392_, lean_object* v_catName_2393_){
_start:
{
lean_object* v___x_2394_; lean_object* v_ext_2395_; lean_object* v_toEnvExtension_2396_; lean_object* v_asyncMode_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v_categories_2400_; lean_object* v___x_2401_; 
v___x_2394_ = l_Lean_Parser_parserExtension;
v_ext_2395_ = lean_ctor_get(v___x_2394_, 1);
v_toEnvExtension_2396_ = lean_ctor_get(v_ext_2395_, 0);
v_asyncMode_2397_ = lean_ctor_get(v_toEnvExtension_2396_, 2);
v___x_2398_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2399_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2398_, v___x_2394_, v_env_2392_, v_asyncMode_2397_);
v_categories_2400_ = lean_ctor_get(v___x_2399_, 2);
lean_inc_ref(v_categories_2400_);
lean_dec(v___x_2399_);
v___x_2401_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2400_, v_catName_2393_);
lean_dec_ref(v_categories_2400_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object* v_env_2402_, lean_object* v_catName_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Parser_getParserCategory_x3f(v_env_2402_, v_catName_2403_);
lean_dec(v_catName_2403_);
return v_res_2404_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object* v_env_2405_, lean_object* v_catName_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_Parser_getParserCategory_x3f(v_env_2405_, v_catName_2406_);
if (lean_obj_tag(v___x_2407_) == 0)
{
uint8_t v___x_2408_; 
v___x_2408_ = 0;
return v___x_2408_;
}
else
{
uint8_t v___x_2409_; 
lean_dec_ref_known(v___x_2407_, 1);
v___x_2409_ = 1;
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object* v_env_2410_, lean_object* v_catName_2411_){
_start:
{
uint8_t v_res_2412_; lean_object* v_r_2413_; 
v_res_2412_ = l_Lean_Parser_isParserCategory(v_env_2410_, v_catName_2411_);
lean_dec(v_catName_2411_);
v_r_2413_ = lean_box(v_res_2412_);
return v_r_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object* v_env_2414_, lean_object* v_catName_2415_, lean_object* v_declName_2416_, uint8_t v_behavior_2417_){
_start:
{
uint8_t v___x_2418_; 
lean_inc_ref(v_env_2414_);
v___x_2418_ = l_Lean_Parser_isParserCategory(v_env_2414_, v_catName_2415_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2419_ = l_Lean_Parser_parserExtension;
v___x_2420_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2420_, 0, v_catName_2415_);
lean_ctor_set(v___x_2420_, 1, v_declName_2416_);
lean_ctor_set_uint8(v___x_2420_, sizeof(void*)*2, v_behavior_2417_);
v___x_2421_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2419_, v_env_2414_, v___x_2420_);
v___x_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
return v___x_2422_;
}
else
{
lean_object* v___x_2423_; 
lean_dec(v_declName_2416_);
lean_dec_ref(v_env_2414_);
v___x_2423_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_2415_);
return v___x_2423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* v_env_2424_, lean_object* v_catName_2425_, lean_object* v_declName_2426_, lean_object* v_behavior_2427_){
_start:
{
uint8_t v_behavior_boxed_2428_; lean_object* v_res_2429_; 
v_behavior_boxed_2428_ = lean_unbox(v_behavior_2427_);
v_res_2429_ = l_Lean_Parser_addParserCategory(v_env_2424_, v_catName_2425_, v_declName_2426_, v_behavior_boxed_2428_);
return v_res_2429_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object* v_env_2430_, lean_object* v_catName_2431_){
_start:
{
lean_object* v___x_2432_; lean_object* v_ext_2433_; lean_object* v_toEnvExtension_2434_; lean_object* v_asyncMode_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v_categories_2438_; lean_object* v___x_2439_; 
v___x_2432_ = l_Lean_Parser_parserExtension;
v_ext_2433_ = lean_ctor_get(v___x_2432_, 1);
v_toEnvExtension_2434_ = lean_ctor_get(v_ext_2433_, 0);
v_asyncMode_2435_ = lean_ctor_get(v_toEnvExtension_2434_, 2);
v___x_2436_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2437_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2436_, v___x_2432_, v_env_2430_, v_asyncMode_2435_);
v_categories_2438_ = lean_ctor_get(v___x_2437_, 2);
lean_inc_ref(v_categories_2438_);
lean_dec(v___x_2437_);
v___x_2439_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2438_, v_catName_2431_);
lean_dec_ref(v_categories_2438_);
if (lean_obj_tag(v___x_2439_) == 0)
{
uint8_t v___x_2440_; 
v___x_2440_ = 0;
return v___x_2440_;
}
else
{
lean_object* v_val_2441_; uint8_t v_behavior_2442_; 
v_val_2441_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_val_2441_);
lean_dec_ref_known(v___x_2439_, 1);
v_behavior_2442_ = lean_ctor_get_uint8(v_val_2441_, sizeof(void*)*3);
lean_dec(v_val_2441_);
return v_behavior_2442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object* v_env_2443_, lean_object* v_catName_2444_){
_start:
{
uint8_t v_res_2445_; lean_object* v_r_2446_; 
v_res_2445_ = l_Lean_Parser_leadingIdentBehavior(v_env_2443_, v_catName_2444_);
lean_dec(v_catName_2444_);
v_r_2446_ = lean_box(v_res_2445_);
return v_r_2446_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(lean_object* v_x_2447_, lean_object* v_x_2448_){
_start:
{
if (lean_obj_tag(v_x_2448_) == 0)
{
return v_x_2447_;
}
else
{
lean_object* v_head_2449_; lean_object* v_tail_2450_; lean_object* v___x_2451_; 
v_head_2449_ = lean_ctor_get(v_x_2448_, 0);
lean_inc_n(v_head_2449_, 2);
v_tail_2450_ = lean_ctor_get(v_x_2448_, 1);
lean_inc(v_tail_2450_);
lean_dec_ref_known(v_x_2448_, 2);
v___x_2451_ = l_Lean_Data_Trie_insert___redArg(v_x_2447_, v_head_2449_, v_head_2449_);
lean_dec(v_head_2449_);
v_x_2447_ = v___x_2451_;
v_x_2448_ = v_tail_2450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__0(lean_object* v_info_2453_, lean_object* v_ctx_2454_){
_start:
{
lean_object* v_toInputContext_2455_; lean_object* v_toParserModuleContext_2456_; lean_object* v_toCacheableParserContext_2457_; lean_object* v_tokens_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2469_; 
v_toInputContext_2455_ = lean_ctor_get(v_ctx_2454_, 0);
v_toParserModuleContext_2456_ = lean_ctor_get(v_ctx_2454_, 1);
v_toCacheableParserContext_2457_ = lean_ctor_get(v_ctx_2454_, 2);
v_tokens_2458_ = lean_ctor_get(v_ctx_2454_, 3);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_ctx_2454_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2460_ = v_ctx_2454_;
v_isShared_2461_ = v_isSharedCheck_2469_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_tokens_2458_);
lean_inc(v_toCacheableParserContext_2457_);
lean_inc(v_toParserModuleContext_2456_);
lean_inc(v_toInputContext_2455_);
lean_dec(v_ctx_2454_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2469_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v_collectTokens_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
v_collectTokens_2462_ = lean_ctor_get(v_info_2453_, 0);
lean_inc_ref(v_collectTokens_2462_);
lean_dec_ref(v_info_2453_);
v___x_2463_ = lean_box(0);
v___x_2464_ = lean_apply_1(v_collectTokens_2462_, v___x_2463_);
v___x_2465_ = l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(v_tokens_2458_, v___x_2464_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 3, v___x_2465_);
v___x_2467_ = v___x_2460_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_toInputContext_2455_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_toParserModuleContext_2456_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v_toCacheableParserContext_2457_);
lean_ctor_set(v_reuseFailAlloc_2468_, 3, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1(lean_object* v_categories_2470_, lean_object* v_declName_2471_, lean_object* v___x_2472_, lean_object* v_ctx_2473_, lean_object* v_s_2474_, lean_object* v_evalFallback_x3f_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_Parser_mkParserOfConstant(v_categories_2470_, v_declName_2471_, v___x_2472_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v_snd_2479_; lean_object* v_info_2480_; lean_object* v_fn_2481_; lean_object* v___f_2482_; lean_object* v___x_2483_; 
lean_dec(v_evalFallback_x3f_2475_);
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
v_snd_2479_ = lean_ctor_get(v_a_2478_, 1);
lean_inc(v_snd_2479_);
lean_dec(v_a_2478_);
v_info_2480_ = lean_ctor_get(v_snd_2479_, 0);
lean_inc_ref(v_info_2480_);
v_fn_2481_ = lean_ctor_get(v_snd_2479_, 1);
lean_inc_ref(v_fn_2481_);
lean_dec(v_snd_2479_);
v___f_2482_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__0), 2, 1);
lean_closure_set(v___f_2482_, 0, v_info_2480_);
v___x_2483_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2482_, v_fn_2481_, v_ctx_2473_, v_s_2474_);
return v___x_2483_;
}
else
{
if (lean_obj_tag(v_evalFallback_x3f_2475_) == 1)
{
lean_object* v_val_2484_; lean_object* v___x_2485_; 
lean_dec_ref_known(v___x_2477_, 1);
v_val_2484_ = lean_ctor_get(v_evalFallback_x3f_2475_, 0);
lean_inc(v_val_2484_);
lean_dec_ref_known(v_evalFallback_x3f_2475_, 1);
v___x_2485_ = lean_apply_2(v_val_2484_, v_ctx_2473_, v_s_2474_);
return v___x_2485_;
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; lean_object* v___x_2490_; 
lean_dec(v_evalFallback_x3f_2475_);
lean_dec_ref(v_ctx_2473_);
v_a_2486_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2486_);
lean_dec_ref_known(v___x_2477_, 1);
v___x_2487_ = lean_io_error_to_string(v_a_2486_);
v___x_2488_ = lean_box(0);
v___x_2489_ = 1;
v___x_2490_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2474_, v___x_2487_, v___x_2488_, v___x_2489_);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed(lean_object* v_categories_2491_, lean_object* v_declName_2492_, lean_object* v___x_2493_, lean_object* v_ctx_2494_, lean_object* v_s_2495_, lean_object* v_evalFallback_x3f_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_Parser_evalParserConstUnsafe___lam__1(v_categories_2491_, v_declName_2492_, v___x_2493_, v_ctx_2494_, v_s_2495_, v_evalFallback_x3f_2496_);
lean_dec_ref(v___x_2493_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* v_declName_2499_, lean_object* v_evalFallback_x3f_2500_, lean_object* v_ctx_2501_, lean_object* v_s_2502_){
_start:
{
lean_object* v_toParserModuleContext_2503_; lean_object* v_env_2504_; lean_object* v_options_2505_; lean_object* v___x_2506_; lean_object* v_ext_2507_; lean_object* v_toEnvExtension_2508_; lean_object* v_asyncMode_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v_categories_2512_; lean_object* v___x_2513_; lean_object* v___f_2514_; lean_object* v___x_2515_; 
v_toParserModuleContext_2503_ = lean_ctor_get(v_ctx_2501_, 1);
v_env_2504_ = lean_ctor_get(v_toParserModuleContext_2503_, 0);
v_options_2505_ = lean_ctor_get(v_toParserModuleContext_2503_, 1);
v___x_2506_ = l_Lean_Parser_parserExtension;
v_ext_2507_ = lean_ctor_get(v___x_2506_, 1);
v_toEnvExtension_2508_ = lean_ctor_get(v_ext_2507_, 0);
v_asyncMode_2509_ = lean_ctor_get(v_toEnvExtension_2508_, 2);
v___x_2510_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref_n(v_env_2504_, 2);
v___x_2511_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2510_, v___x_2506_, v_env_2504_, v_asyncMode_2509_);
v_categories_2512_ = lean_ctor_get(v___x_2511_, 2);
lean_inc_ref(v_categories_2512_);
lean_dec(v___x_2511_);
lean_inc_ref(v_options_2505_);
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v_env_2504_);
lean_ctor_set(v___x_2513_, 1, v_options_2505_);
v___f_2514_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2514_, 0, v_categories_2512_);
lean_closure_set(v___f_2514_, 1, v_declName_2499_);
lean_closure_set(v___f_2514_, 2, v___x_2513_);
lean_closure_set(v___f_2514_, 3, v_ctx_2501_);
lean_closure_set(v___f_2514_, 4, v_s_2502_);
lean_closure_set(v___f_2514_, 5, v_evalFallback_x3f_2500_);
v___x_2515_ = l_unsafeBaseIO___redArg(v___f_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object* v_name_2516_, lean_object* v_decl_2517_, lean_object* v_ref_2518_){
_start:
{
lean_object* v_defValue_2520_; lean_object* v_descr_2521_; lean_object* v_deprecation_x3f_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v_defValue_2520_ = lean_ctor_get(v_decl_2517_, 0);
v_descr_2521_ = lean_ctor_get(v_decl_2517_, 1);
v_deprecation_x3f_2522_ = lean_ctor_get(v_decl_2517_, 2);
v___x_2523_ = lean_alloc_ctor(1, 0, 1);
v___x_2524_ = lean_unbox(v_defValue_2520_);
lean_ctor_set_uint8(v___x_2523_, 0, v___x_2524_);
lean_inc(v_deprecation_x3f_2522_);
lean_inc_ref(v_descr_2521_);
lean_inc_n(v_name_2516_, 2);
v___x_2525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2525_, 0, v_name_2516_);
lean_ctor_set(v___x_2525_, 1, v_ref_2518_);
lean_ctor_set(v___x_2525_, 2, v___x_2523_);
lean_ctor_set(v___x_2525_, 3, v_descr_2521_);
lean_ctor_set(v___x_2525_, 4, v_deprecation_x3f_2522_);
v___x_2526_ = lean_register_option(v_name_2516_, v___x_2525_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2534_; 
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2526_, 0);
lean_dec(v_unused_2535_);
v___x_2528_ = v___x_2526_;
v_isShared_2529_ = v_isSharedCheck_2534_;
goto v_resetjp_2527_;
}
else
{
lean_dec(v___x_2526_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2534_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2532_; 
lean_inc(v_defValue_2520_);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v_name_2516_);
lean_ctor_set(v___x_2530_, 1, v_defValue_2520_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2530_);
v___x_2532_ = v___x_2528_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v_name_2516_);
v_a_2536_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2526_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2526_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2544_, lean_object* v_decl_2545_, lean_object* v_ref_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v_name_2544_, v_decl_2545_, v_ref_2546_);
lean_dec_ref(v_decl_2545_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2566_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2567_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2568_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2569_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v___x_2566_, v___x_2567_, v___x_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(lean_object* v_o_2575_, lean_object* v_k_2576_, uint8_t v_v_2577_){
_start:
{
lean_object* v_map_2578_; uint8_t v_hasTrace_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2593_; 
v_map_2578_ = lean_ctor_get(v_o_2575_, 0);
v_hasTrace_2579_ = lean_ctor_get_uint8(v_o_2575_, sizeof(void*)*1);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_o_2575_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2581_ = v_o_2575_;
v_isShared_2582_ = v_isSharedCheck_2593_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_map_2578_);
lean_dec(v_o_2575_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2593_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2583_, 0, v_v_2577_);
lean_inc(v_k_2576_);
v___x_2584_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2576_, v___x_2583_, v_map_2578_);
if (v_hasTrace_2579_ == 0)
{
lean_object* v___x_2585_; uint8_t v___x_2586_; lean_object* v___x_2588_; 
v___x_2585_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_2586_ = l_Lean_Name_isPrefixOf(v___x_2585_, v_k_2576_);
lean_dec(v_k_2576_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2584_);
v___x_2588_ = v___x_2581_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2584_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_ctor_set_uint8(v___x_2588_, sizeof(void*)*1, v___x_2586_);
return v___x_2588_;
}
}
else
{
lean_object* v___x_2591_; 
lean_dec(v_k_2576_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2584_);
v___x_2591_ = v___x_2581_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2584_);
lean_ctor_set_uint8(v_reuseFailAlloc_2592_, sizeof(void*)*1, v_hasTrace_2579_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___boxed(lean_object* v_o_2594_, lean_object* v_k_2595_, lean_object* v_v_2596_){
_start:
{
uint8_t v_v_boxed_2597_; lean_object* v_res_2598_; 
v_v_boxed_2597_ = lean_unbox(v_v_2596_);
v_res_2598_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_o_2594_, v_k_2595_, v_v_boxed_2597_);
return v_res_2598_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(lean_object* v_opts_2599_, lean_object* v_opt_2600_){
_start:
{
lean_object* v_name_2601_; lean_object* v_defValue_2602_; lean_object* v_map_2603_; lean_object* v___x_2604_; 
v_name_2601_ = lean_ctor_get(v_opt_2600_, 0);
v_defValue_2602_ = lean_ctor_get(v_opt_2600_, 1);
v_map_2603_ = lean_ctor_get(v_opts_2599_, 0);
v___x_2604_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2603_, v_name_2601_);
if (lean_obj_tag(v___x_2604_) == 0)
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_unbox(v_defValue_2602_);
return v___x_2605_;
}
else
{
lean_object* v_val_2606_; 
v_val_2606_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_val_2606_);
lean_dec_ref_known(v___x_2604_, 1);
if (lean_obj_tag(v_val_2606_) == 1)
{
uint8_t v_v_2607_; 
v_v_2607_ = lean_ctor_get_uint8(v_val_2606_, 0);
lean_dec_ref_known(v_val_2606_, 0);
return v_v_2607_;
}
else
{
uint8_t v___x_2608_; 
lean_dec(v_val_2606_);
v___x_2608_ = lean_unbox(v_defValue_2602_);
return v___x_2608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1___boxed(lean_object* v_opts_2609_, lean_object* v_opt_2610_){
_start:
{
uint8_t v_res_2611_; lean_object* v_r_2612_; 
v_res_2611_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_opts_2609_, v_opt_2610_);
lean_dec_ref(v_opt_2610_);
lean_dec_ref(v_opts_2609_);
v_r_2612_ = lean_box(v_res_2611_);
return v_r_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0(uint8_t v_suppressInsideQuot_2618_, lean_object* v_ctx_2619_){
_start:
{
lean_object* v_toParserModuleContext_2620_; lean_object* v_toInputContext_2621_; lean_object* v_toCacheableParserContext_2622_; lean_object* v_tokens_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2643_; 
v_toParserModuleContext_2620_ = lean_ctor_get(v_ctx_2619_, 1);
v_toInputContext_2621_ = lean_ctor_get(v_ctx_2619_, 0);
v_toCacheableParserContext_2622_ = lean_ctor_get(v_ctx_2619_, 2);
v_tokens_2623_ = lean_ctor_get(v_ctx_2619_, 3);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_ctx_2619_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2625_ = v_ctx_2619_;
v_isShared_2626_ = v_isSharedCheck_2643_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_tokens_2623_);
lean_inc(v_toCacheableParserContext_2622_);
lean_inc(v_toParserModuleContext_2620_);
lean_inc(v_toInputContext_2621_);
lean_dec(v_ctx_2619_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2643_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v_env_2627_; lean_object* v_options_2628_; lean_object* v_currNamespace_2629_; lean_object* v_openDecls_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2642_; 
v_env_2627_ = lean_ctor_get(v_toParserModuleContext_2620_, 0);
v_options_2628_ = lean_ctor_get(v_toParserModuleContext_2620_, 1);
v_currNamespace_2629_ = lean_ctor_get(v_toParserModuleContext_2620_, 2);
v_openDecls_2630_ = lean_ctor_get(v_toParserModuleContext_2620_, 3);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_toParserModuleContext_2620_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2632_ = v_toParserModuleContext_2620_;
v_isShared_2633_ = v_isSharedCheck_2642_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_openDecls_2630_);
lean_inc(v_currNamespace_2629_);
lean_inc(v_options_2628_);
lean_inc(v_env_2627_);
lean_dec(v_toParserModuleContext_2620_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2642_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
v___x_2634_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_2635_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_2628_, v___x_2634_, v_suppressInsideQuot_2618_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 1, v___x_2635_);
v___x_2637_ = v___x_2632_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_env_2627_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_currNamespace_2629_);
lean_ctor_set(v_reuseFailAlloc_2641_, 3, v_openDecls_2630_);
v___x_2637_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_object* v___x_2639_; 
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 1, v___x_2637_);
v___x_2639_ = v___x_2625_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_toInputContext_2621_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2640_, 2, v_toCacheableParserContext_2622_);
lean_ctor_set(v_reuseFailAlloc_2640_, 3, v_tokens_2623_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0___boxed(lean_object* v_suppressInsideQuot_2644_, lean_object* v_ctx_2645_){
_start:
{
uint8_t v_suppressInsideQuot_boxed_2646_; lean_object* v_res_2647_; 
v_suppressInsideQuot_boxed_2646_ = lean_unbox(v_suppressInsideQuot_2644_);
v_res_2647_ = l_Lean_Parser_evalInsideQuot___lam__0(v_suppressInsideQuot_boxed_2646_, v_ctx_2645_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object* v_fn_2648_, lean_object* v_declName_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_toCacheableParserContext_2652_; lean_object* v_toParserModuleContext_2653_; lean_object* v_quotDepth_2654_; uint8_t v_suppressInsideQuot_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; 
v_toCacheableParserContext_2652_ = lean_ctor_get(v___y_2650_, 2);
v_toParserModuleContext_2653_ = lean_ctor_get(v___y_2650_, 1);
v_quotDepth_2654_ = lean_ctor_get(v_toCacheableParserContext_2652_, 1);
v_suppressInsideQuot_2655_ = lean_ctor_get_uint8(v_toCacheableParserContext_2652_, sizeof(void*)*4);
v___x_2656_ = lean_unsigned_to_nat(0u);
v___x_2657_ = lean_nat_dec_lt(v___x_2656_, v_quotDepth_2654_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; 
lean_dec(v_declName_2649_);
v___x_2658_ = lean_apply_2(v_fn_2648_, v___y_2650_, v___y_2651_);
return v___x_2658_;
}
else
{
if (v_suppressInsideQuot_2655_ == 0)
{
lean_object* v_env_2659_; lean_object* v_options_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v_env_2659_ = lean_ctor_get(v_toParserModuleContext_2653_, 0);
v_options_2660_ = lean_ctor_get(v_toParserModuleContext_2653_, 1);
v___x_2661_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_2662_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_2660_, v___x_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; 
lean_dec(v_declName_2649_);
v___x_2663_ = lean_apply_2(v_fn_2648_, v___y_2650_, v___y_2651_);
return v___x_2663_;
}
else
{
uint8_t v___x_2664_; 
lean_inc(v_declName_2649_);
lean_inc_ref(v_env_2659_);
v___x_2664_ = l_Lean_Environment_contains(v_env_2659_, v_declName_2649_, v___x_2662_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; 
lean_dec(v_declName_2649_);
v___x_2665_ = lean_apply_2(v_fn_2648_, v___y_2650_, v___y_2651_);
return v___x_2665_;
}
else
{
lean_object* v___x_2666_; lean_object* v___f_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2666_ = lean_box(v_suppressInsideQuot_2655_);
v___f_2667_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2667_, 0, v___x_2666_);
v___x_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_fn_2648_);
v___x_2669_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_2669_, 0, v_declName_2649_);
lean_closure_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2667_, v___x_2669_, v___y_2650_, v___y_2651_);
return v___x_2670_;
}
}
}
else
{
lean_object* v___x_2671_; 
lean_dec(v_declName_2649_);
v___x_2671_ = lean_apply_2(v_fn_2648_, v___y_2650_, v___y_2651_);
return v___x_2671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object* v_declName_2672_, lean_object* v_p_2673_){
_start:
{
lean_object* v_info_2674_; lean_object* v_fn_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2683_; 
v_info_2674_ = lean_ctor_get(v_p_2673_, 0);
v_fn_2675_ = lean_ctor_get(v_p_2673_, 1);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_p_2673_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2677_ = v_p_2673_;
v_isShared_2678_ = v_isSharedCheck_2683_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_fn_2675_);
lean_inc(v_info_2674_);
lean_dec(v_p_2673_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2683_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___f_2679_; lean_object* v___x_2681_; 
v___f_2679_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__1), 4, 2);
lean_closure_set(v___f_2679_, 0, v_fn_2675_);
lean_closure_set(v___f_2679_, 1, v_declName_2672_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 1, v___f_2679_);
v___x_2681_ = v___x_2677_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_info_2674_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___f_2679_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object* v_catName_2684_, lean_object* v_declName_2685_, uint8_t v_leading_2686_, lean_object* v_p_2687_, lean_object* v_prio_2688_){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v_p_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2690_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_2691_ = lean_st_ref_get(v___x_2690_);
lean_inc_n(v_declName_2685_, 2);
v_p_2692_ = l_Lean_Parser_evalInsideQuot(v_declName_2685_, v_p_2687_);
lean_inc_ref(v_p_2692_);
v___x_2693_ = l_Lean_Parser_addParser(v___x_2691_, v_catName_2684_, v_declName_2685_, v_leading_2686_, v_p_2692_, v_prio_2688_);
v___x_2694_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_2693_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v_info_2699_; lean_object* v_collectKinds_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
v___x_2696_ = lean_st_ref_swap(v___x_2690_, v_a_2695_);
lean_dec(v___x_2696_);
v___x_2697_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_2698_ = lean_st_ref_take(v___x_2697_);
v_info_2699_ = lean_ctor_get(v_p_2692_, 0);
lean_inc_ref(v_info_2699_);
lean_dec_ref(v_p_2692_);
v_collectKinds_2700_ = lean_ctor_get(v_info_2699_, 1);
lean_inc_ref(v_collectKinds_2700_);
v___x_2701_ = lean_apply_1(v_collectKinds_2700_, v___x_2698_);
v___x_2702_ = lean_st_ref_put(v___x_2697_, v___x_2701_);
v___x_2703_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_2699_, v_declName_2685_);
return v___x_2703_;
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v_p_2692_);
lean_dec(v_declName_2685_);
v_a_2704_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2694_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2694_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* v_catName_2712_, lean_object* v_declName_2713_, lean_object* v_leading_2714_, lean_object* v_p_2715_, lean_object* v_prio_2716_, lean_object* v_a_2717_){
_start:
{
uint8_t v_leading_boxed_2718_; lean_object* v_res_2719_; 
v_leading_boxed_2718_ = lean_unbox(v_leading_2714_);
v_res_2719_ = l_Lean_Parser_addBuiltinParser(v_catName_2712_, v_declName_2713_, v_leading_boxed_2718_, v_p_2715_, v_prio_2716_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* v_catName_2720_, lean_object* v_declName_2721_, lean_object* v_p_2722_, lean_object* v_prio_2723_){
_start:
{
uint8_t v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = 1;
v___x_2726_ = l_Lean_Parser_addBuiltinParser(v_catName_2720_, v_declName_2721_, v___x_2725_, v_p_2722_, v_prio_2723_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object* v_catName_2727_, lean_object* v_declName_2728_, lean_object* v_p_2729_, lean_object* v_prio_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_Parser_addBuiltinLeadingParser(v_catName_2727_, v_declName_2728_, v_p_2729_, v_prio_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* v_catName_2733_, lean_object* v_declName_2734_, lean_object* v_p_2735_, lean_object* v_prio_2736_){
_start:
{
uint8_t v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = 0;
v___x_2739_ = l_Lean_Parser_addBuiltinParser(v_catName_2733_, v_declName_2734_, v___x_2738_, v_p_2735_, v_prio_2736_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object* v_catName_2740_, lean_object* v_declName_2741_, lean_object* v_p_2742_, lean_object* v_prio_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_Parser_addBuiltinTrailingParser(v_catName_2740_, v_declName_2741_, v_p_2742_, v_prio_2743_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object* v_kind_2746_){
_start:
{
uint8_t v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = 1;
lean_inc(v_kind_2746_);
v___x_2748_ = l_Lean_Name_toString(v_kind_2746_, v___x_2747_);
v___x_2749_ = l_Lean_Parser_mkAntiquot(v___x_2748_, v_kind_2746_, v___x_2747_, v___x_2747_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object* v_kind_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v___x_2753_; lean_object* v_fn_2754_; lean_object* v___x_2755_; 
v___x_2753_ = l_Lean_Parser_mkCategoryAntiquotParser(v_kind_2750_);
v_fn_2754_ = lean_ctor_get(v___x_2753_, 1);
lean_inc_ref(v_fn_2754_);
lean_dec_ref(v___x_2753_);
v___x_2755_ = lean_apply_2(v_fn_2754_, v_a_2751_, v_a_2752_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl___lam__0(lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2759_; lean_object* v_fn_2760_; lean_object* v___x_2761_; 
v___x_2759_ = l_Lean_Parser_mkCategoryAntiquotParser(v___y_2756_);
v_fn_2760_ = lean_ctor_get(v___x_2759_, 1);
lean_inc_ref(v_fn_2760_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = lean_apply_2(v_fn_2760_, v___y_2757_, v___y_2758_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* v_catName_2770_, lean_object* v_ctx_2771_, lean_object* v_s_2772_){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; uint8_t v___x_2776_; lean_object* v___y_2778_; 
v___x_2773_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2774_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__1));
v___x_2775_ = lean_name_eq(v_catName_2770_, v___x_2774_);
v___x_2776_ = 1;
if (v___x_2775_ == 0)
{
v___y_2778_ = v_catName_2770_;
goto v___jp_2777_;
}
else
{
lean_object* v___x_2800_; 
lean_dec(v_catName_2770_);
v___x_2800_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__5));
v___y_2778_ = v___x_2800_;
goto v___jp_2777_;
}
v___jp_2777_:
{
lean_object* v_toParserModuleContext_2779_; lean_object* v_env_2780_; lean_object* v___x_2781_; lean_object* v_ext_2782_; lean_object* v_toEnvExtension_2783_; lean_object* v_asyncMode_2784_; lean_object* v___x_2785_; lean_object* v_categories_2786_; lean_object* v___x_2787_; 
v_toParserModuleContext_2779_ = lean_ctor_get(v_ctx_2771_, 1);
v_env_2780_ = lean_ctor_get(v_toParserModuleContext_2779_, 0);
v___x_2781_ = l_Lean_Parser_parserExtension;
v_ext_2782_ = lean_ctor_get(v___x_2781_, 1);
v_toEnvExtension_2783_ = lean_ctor_get(v_ext_2782_, 0);
v_asyncMode_2784_ = lean_ctor_get(v_toEnvExtension_2783_, 2);
lean_inc_ref(v_env_2780_);
v___x_2785_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2773_, v___x_2781_, v_env_2780_, v_asyncMode_2784_);
v_categories_2786_ = lean_ctor_get(v___x_2785_, 2);
lean_inc_ref(v_categories_2786_);
lean_dec(v___x_2785_);
v___x_2787_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2786_, v___y_2778_);
lean_dec_ref(v_categories_2786_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec_ref(v_ctx_2771_);
v___x_2788_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__2));
v___x_2789_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2778_, v___x_2776_);
v___x_2790_ = lean_string_append(v___x_2788_, v___x_2789_);
lean_dec_ref(v___x_2789_);
v___x_2791_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__3));
v___x_2792_ = lean_string_append(v___x_2790_, v___x_2791_);
v___x_2793_ = lean_box(0);
v___x_2794_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2772_, v___x_2792_, v___x_2793_, v___x_2776_);
return v___x_2794_;
}
else
{
lean_object* v_val_2795_; lean_object* v_tables_2796_; uint8_t v_behavior_2797_; lean_object* v___f_2798_; lean_object* v___x_2799_; 
v_val_2795_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_val_2795_);
lean_dec_ref_known(v___x_2787_, 1);
v_tables_2796_ = lean_ctor_get(v_val_2795_, 2);
lean_inc_ref(v_tables_2796_);
v_behavior_2797_ = lean_ctor_get_uint8(v_val_2795_, sizeof(void*)*3);
lean_dec(v_val_2795_);
lean_inc(v___y_2778_);
v___f_2798_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl___lam__0), 3, 1);
lean_closure_set(v___f_2798_, 0, v___y_2778_);
v___x_2799_ = l_Lean_Parser_prattParser(v___y_2778_, v_tables_2796_, v_behavior_2797_, v___f_2798_, v_ctx_2771_, v_s_2772_);
return v___x_2799_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2803_ = l_Lean_Parser_categoryParserFnRef;
v___x_2804_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_));
v___x_2805_ = lean_st_ref_swap(v___x_2803_, v___x_2804_);
lean_dec(v___x_2805_);
v___x_2806_ = lean_box(0);
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object* v_a_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
return v_res_2809_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2810_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0);
v___x_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
return v___x_2812_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object* v_ext_2815_, lean_object* v_b_2816_, uint8_t v_kind_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_currNamespace_2821_; lean_object* v___x_2822_; lean_object* v_env_2823_; lean_object* v_nextMacroScope_2824_; lean_object* v_ngen_2825_; lean_object* v_auxDeclNGen_2826_; lean_object* v_traceState_2827_; lean_object* v_messages_2828_; lean_object* v_infoState_2829_; lean_object* v_snapshotTasks_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2842_; 
v_currNamespace_2821_ = lean_ctor_get(v___y_2818_, 6);
v___x_2822_ = lean_st_ref_take(v___y_2819_);
v_env_2823_ = lean_ctor_get(v___x_2822_, 0);
v_nextMacroScope_2824_ = lean_ctor_get(v___x_2822_, 1);
v_ngen_2825_ = lean_ctor_get(v___x_2822_, 2);
v_auxDeclNGen_2826_ = lean_ctor_get(v___x_2822_, 3);
v_traceState_2827_ = lean_ctor_get(v___x_2822_, 4);
v_messages_2828_ = lean_ctor_get(v___x_2822_, 6);
v_infoState_2829_ = lean_ctor_get(v___x_2822_, 7);
v_snapshotTasks_2830_ = lean_ctor_get(v___x_2822_, 8);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v___x_2822_, 5);
lean_dec(v_unused_2843_);
v___x_2832_ = v___x_2822_;
v_isShared_2833_ = v_isSharedCheck_2842_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_snapshotTasks_2830_);
lean_inc(v_infoState_2829_);
lean_inc(v_messages_2828_);
lean_inc(v_traceState_2827_);
lean_inc(v_auxDeclNGen_2826_);
lean_inc(v_ngen_2825_);
lean_inc(v_nextMacroScope_2824_);
lean_inc(v_env_2823_);
lean_dec(v___x_2822_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2842_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
lean_inc(v_currNamespace_2821_);
v___x_2834_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2823_, v_ext_2815_, v_b_2816_, v_kind_2817_, v_currNamespace_2821_);
v___x_2835_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 5, v___x_2835_);
lean_ctor_set(v___x_2832_, 0, v___x_2834_);
v___x_2837_ = v___x_2832_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_nextMacroScope_2824_);
lean_ctor_set(v_reuseFailAlloc_2841_, 2, v_ngen_2825_);
lean_ctor_set(v_reuseFailAlloc_2841_, 3, v_auxDeclNGen_2826_);
lean_ctor_set(v_reuseFailAlloc_2841_, 4, v_traceState_2827_);
lean_ctor_set(v_reuseFailAlloc_2841_, 5, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2841_, 6, v_messages_2828_);
lean_ctor_set(v_reuseFailAlloc_2841_, 7, v_infoState_2829_);
lean_ctor_set(v_reuseFailAlloc_2841_, 8, v_snapshotTasks_2830_);
v___x_2837_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2838_ = lean_st_ref_put(v___y_2819_, v___x_2837_);
v___x_2839_ = lean_box(0);
v___x_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
return v___x_2840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object* v_ext_2844_, lean_object* v_b_2845_, lean_object* v_kind_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
uint8_t v_kind_boxed_2850_; lean_object* v_res_2851_; 
v_kind_boxed_2850_ = lean_unbox(v_kind_2846_);
v_res_2851_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2844_, v_b_2845_, v_kind_boxed_2850_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object* v_00_u03b1_2852_, lean_object* v_00_u03b2_2853_, lean_object* v_00_u03c3_2854_, lean_object* v_ext_2855_, lean_object* v_b_2856_, uint8_t v_kind_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2855_, v_b_2856_, v_kind_2857_, v___y_2858_, v___y_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object* v_00_u03b1_2862_, lean_object* v_00_u03b2_2863_, lean_object* v_00_u03c3_2864_, lean_object* v_ext_2865_, lean_object* v_b_2866_, lean_object* v_kind_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
uint8_t v_kind_boxed_2871_; lean_object* v_res_2872_; 
v_kind_boxed_2871_ = lean_unbox(v_kind_2867_);
v_res_2872_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(v_00_u03b1_2862_, v_00_u03b2_2863_, v_00_u03c3_2864_, v_ext_2865_, v_b_2866_, v_kind_boxed_2871_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object* v_x_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
if (lean_obj_tag(v_x_2873_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_a_2877_ = lean_ctor_get(v_x_2873_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v_x_2873_, 1);
v___x_2878_ = l_Lean_stringToMessageData(v_a_2877_);
v___x_2879_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2878_, v___y_2874_, v___y_2875_);
return v___x_2879_;
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
v_a_2880_ = lean_ctor_get(v_x_2873_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_x_2873_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v_x_2873_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v_x_2873_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set_tag(v___x_2882_, 0);
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object* v_x_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object* v_tk_2893_, uint8_t v_kind_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v_env_2899_; lean_object* v___x_2900_; lean_object* v_ext_2901_; lean_object* v_toEnvExtension_2902_; lean_object* v_asyncMode_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v_tokens_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2898_ = lean_st_ref_get(v_a_2896_);
v_env_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc_ref(v_env_2899_);
lean_dec(v___x_2898_);
v___x_2900_ = l_Lean_Parser_parserExtension;
v_ext_2901_ = lean_ctor_get(v___x_2900_, 1);
v_toEnvExtension_2902_ = lean_ctor_get(v_ext_2901_, 0);
v_asyncMode_2903_ = lean_ctor_get(v_toEnvExtension_2902_, 2);
v___x_2904_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2905_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2904_, v___x_2900_, v_env_2899_, v_asyncMode_2903_);
v_tokens_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc_ref(v_tokens_2906_);
lean_dec(v___x_2905_);
lean_inc_ref(v_tk_2893_);
v___x_2907_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_2906_, v_tk_2893_);
v___x_2908_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v___x_2907_, v_a_2895_, v_a_2896_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_dec_ref_known(v___x_2908_, 1);
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_tk_2893_);
v___x_2910_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_2900_, v___x_2909_, v_kind_2894_, v_a_2895_, v_a_2896_);
return v___x_2910_;
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec_ref(v_tk_2893_);
v_a_2911_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2908_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2908_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object* v_tk_2919_, lean_object* v_kind_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
uint8_t v_kind_boxed_2924_; lean_object* v_res_2925_; 
v_kind_boxed_2924_ = lean_unbox(v_kind_2920_);
v_res_2925_ = l_Lean_Parser_addToken(v_tk_2919_, v_kind_boxed_2924_, v_a_2921_, v_a_2922_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_object* v_00_u03b1_2926_, lean_object* v_x_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2927_, v___y_2928_, v___y_2929_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___boxed(lean_object* v_00_u03b1_2932_, lean_object* v_x_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(v_00_u03b1_2932_, v_x_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object* v_env_2938_, lean_object* v_k_2939_){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = l_Lean_Parser_parserExtension;
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_k_2939_);
v___x_2942_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2940_, v_env_2938_, v___x_2941_);
return v___x_2942_;
}
}
static uint8_t _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0(void){
_start:
{
lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2943_ = lean_box(0);
v___x_2944_ = lean_internal_is_stage0(v___x_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object* v_env_2945_, lean_object* v_k_2946_){
_start:
{
lean_object* v___x_2947_; lean_object* v_ext_2948_; lean_object* v_toEnvExtension_2949_; lean_object* v_asyncMode_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v_kinds_2953_; uint8_t v___x_2954_; 
v___x_2947_ = l_Lean_Parser_parserExtension;
v_ext_2948_ = lean_ctor_get(v___x_2947_, 1);
v_toEnvExtension_2949_ = lean_ctor_get(v_ext_2948_, 0);
v_asyncMode_2950_ = lean_ctor_get(v_toEnvExtension_2949_, 2);
v___x_2951_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_2945_);
v___x_2952_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2951_, v___x_2947_, v_env_2945_, v_asyncMode_2950_);
v_kinds_2953_ = lean_ctor_get(v___x_2952_, 1);
lean_inc_ref(v_kinds_2953_);
lean_dec(v___x_2952_);
v___x_2954_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_2953_, v_k_2946_);
lean_dec_ref(v_kinds_2953_);
if (v___x_2954_ == 0)
{
uint8_t v___x_2955_; 
v___x_2955_ = lean_uint8_once(&l_Lean_Parser_isValidSyntaxNodeKind___closed__0, &l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once, _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0);
if (v___x_2955_ == 0)
{
lean_dec(v_k_2946_);
lean_dec_ref(v_env_2945_);
return v___x_2955_;
}
else
{
uint8_t v___x_2956_; 
v___x_2956_ = l_Lean_Environment_contains(v_env_2945_, v_k_2946_, v___x_2955_);
return v___x_2956_;
}
}
else
{
lean_dec(v_k_2946_);
lean_dec_ref(v_env_2945_);
return v___x_2954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* v_env_2957_, lean_object* v_k_2958_){
_start:
{
uint8_t v_res_2959_; lean_object* v_r_2960_; 
v_res_2959_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_2957_, v_k_2958_);
v_r_2960_ = lean_box(v_res_2959_);
return v_r_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds___lam__0(lean_object* v_ks_2961_, lean_object* v_k_2962_, lean_object* v_x_2963_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2964_, 0, v_k_2962_);
lean_ctor_set(v___x_2964_, 1, v_ks_2961_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2965_, lean_object* v_keys_2966_, lean_object* v_vals_2967_, lean_object* v_i_2968_, lean_object* v_acc_2969_){
_start:
{
lean_object* v___x_2970_; uint8_t v___x_2971_; 
v___x_2970_ = lean_array_get_size(v_keys_2966_);
v___x_2971_ = lean_nat_dec_lt(v_i_2968_, v___x_2970_);
if (v___x_2971_ == 0)
{
lean_dec(v_i_2968_);
lean_dec(v_f_2965_);
return v_acc_2969_;
}
else
{
lean_object* v_k_2972_; lean_object* v_v_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v_k_2972_ = lean_array_fget_borrowed(v_keys_2966_, v_i_2968_);
v_v_2973_ = lean_array_fget_borrowed(v_vals_2967_, v_i_2968_);
lean_inc(v_f_2965_);
lean_inc(v_v_2973_);
lean_inc(v_k_2972_);
v___x_2974_ = lean_apply_3(v_f_2965_, v_acc_2969_, v_k_2972_, v_v_2973_);
v___x_2975_ = lean_unsigned_to_nat(1u);
v___x_2976_ = lean_nat_add(v_i_2968_, v___x_2975_);
lean_dec(v_i_2968_);
v_i_2968_ = v___x_2976_;
v_acc_2969_ = v___x_2974_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2978_, lean_object* v_keys_2979_, lean_object* v_vals_2980_, lean_object* v_i_2981_, lean_object* v_acc_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2978_, v_keys_2979_, v_vals_2980_, v_i_2981_, v_acc_2982_);
lean_dec_ref(v_vals_2980_);
lean_dec_ref(v_keys_2979_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2984_, lean_object* v_as_2985_, size_t v_i_2986_, size_t v_stop_2987_, lean_object* v_b_2988_){
_start:
{
lean_object* v___y_2990_; uint8_t v___x_2994_; 
v___x_2994_ = lean_usize_dec_eq(v_i_2986_, v_stop_2987_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_array_uget_borrowed(v_as_2985_, v_i_2986_);
switch(lean_obj_tag(v___x_2995_))
{
case 0:
{
lean_object* v_key_2996_; lean_object* v_val_2997_; lean_object* v___x_2998_; 
v_key_2996_ = lean_ctor_get(v___x_2995_, 0);
v_val_2997_ = lean_ctor_get(v___x_2995_, 1);
lean_inc(v_f_2984_);
lean_inc(v_val_2997_);
lean_inc(v_key_2996_);
v___x_2998_ = lean_apply_3(v_f_2984_, v_b_2988_, v_key_2996_, v_val_2997_);
v___y_2990_ = v___x_2998_;
goto v___jp_2989_;
}
case 1:
{
lean_object* v_node_2999_; lean_object* v___x_3000_; 
v_node_2999_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_f_2984_);
v___x_3000_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_2984_, v_node_2999_, v_b_2988_);
v___y_2990_ = v___x_3000_;
goto v___jp_2989_;
}
default: 
{
v___y_2990_ = v_b_2988_;
goto v___jp_2989_;
}
}
}
else
{
lean_dec(v_f_2984_);
return v_b_2988_;
}
v___jp_2989_:
{
size_t v___x_2991_; size_t v___x_2992_; 
v___x_2991_ = ((size_t)1ULL);
v___x_2992_ = lean_usize_add(v_i_2986_, v___x_2991_);
v_i_2986_ = v___x_2992_;
v_b_2988_ = v___y_2990_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3001_, lean_object* v_x_3002_, lean_object* v_x_3003_){
_start:
{
if (lean_obj_tag(v_x_3002_) == 0)
{
lean_object* v_es_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v_es_3004_ = lean_ctor_get(v_x_3002_, 0);
v___x_3005_ = lean_unsigned_to_nat(0u);
v___x_3006_ = lean_array_get_size(v_es_3004_);
v___x_3007_ = lean_nat_dec_lt(v___x_3005_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_dec(v_f_3001_);
return v_x_3003_;
}
else
{
size_t v___x_3008_; size_t v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = ((size_t)0ULL);
v___x_3009_ = lean_usize_of_nat(v___x_3006_);
v___x_3010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3001_, v_es_3004_, v___x_3008_, v___x_3009_, v_x_3003_);
return v___x_3010_;
}
}
else
{
lean_object* v_ks_3011_; lean_object* v_vs_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_ks_3011_ = lean_ctor_get(v_x_3002_, 0);
v_vs_3012_ = lean_ctor_get(v_x_3002_, 1);
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3001_, v_ks_3011_, v_vs_3012_, v___x_3013_, v_x_3003_);
return v___x_3014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3015_, lean_object* v_x_3016_, lean_object* v_x_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3015_, v_x_3016_, v_x_3017_);
lean_dec_ref(v_x_3016_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3019_, lean_object* v_as_3020_, lean_object* v_i_3021_, lean_object* v_stop_3022_, lean_object* v_b_3023_){
_start:
{
size_t v_i_boxed_3024_; size_t v_stop_boxed_3025_; lean_object* v_res_3026_; 
v_i_boxed_3024_ = lean_unbox_usize(v_i_3021_);
lean_dec(v_i_3021_);
v_stop_boxed_3025_ = lean_unbox_usize(v_stop_3022_);
lean_dec(v_stop_3022_);
v_res_3026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3019_, v_as_3020_, v_i_boxed_3024_, v_stop_boxed_3025_, v_b_3023_);
lean_dec_ref(v_as_3020_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object* v_f_3027_, lean_object* v_x1_3028_, lean_object* v_x2_3029_, lean_object* v_x3_3030_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_apply_3(v_f_3027_, v_x1_3028_, v_x2_3029_, v_x3_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object* v_map_3032_, lean_object* v_f_3033_, lean_object* v_init_3034_){
_start:
{
lean_object* v___f_3035_; lean_object* v___x_3036_; 
v___f_3035_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3035_, 0, v_f_3033_);
v___x_3036_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v___f_3035_, v_map_3032_, v_init_3034_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object* v_map_3037_, lean_object* v_f_3038_, lean_object* v_init_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3037_, v_f_3038_, v_init_3039_);
lean_dec_ref(v_map_3037_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* v_env_3042_){
_start:
{
lean_object* v___x_3043_; lean_object* v_ext_3044_; lean_object* v_toEnvExtension_3045_; lean_object* v_asyncMode_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v_kinds_3049_; lean_object* v___f_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3043_ = l_Lean_Parser_parserExtension;
v_ext_3044_ = lean_ctor_get(v___x_3043_, 1);
v_toEnvExtension_3045_ = lean_ctor_get(v_ext_3044_, 0);
v_asyncMode_3046_ = lean_ctor_get(v_toEnvExtension_3045_, 2);
v___x_3047_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3048_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3047_, v___x_3043_, v_env_3042_, v_asyncMode_3046_);
v_kinds_3049_ = lean_ctor_get(v___x_3048_, 1);
lean_inc_ref(v_kinds_3049_);
lean_dec(v___x_3048_);
v___f_3050_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKinds___closed__0));
v___x_3051_ = lean_box(0);
v___x_3052_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_kinds_3049_, v___f_3050_, v___x_3051_);
lean_dec_ref(v_kinds_3049_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object* v_00_u03c3_3053_, lean_object* v_00_u03b2_3054_, lean_object* v_map_3055_, lean_object* v_f_3056_, lean_object* v_init_3057_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3055_, v_f_3056_, v_init_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object* v_00_u03c3_3059_, lean_object* v_00_u03b2_3060_, lean_object* v_map_3061_, lean_object* v_f_3062_, lean_object* v_init_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(v_00_u03c3_3059_, v_00_u03b2_3060_, v_map_3061_, v_f_3062_, v_init_3063_);
lean_dec_ref(v_map_3061_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object* v_map_3065_, lean_object* v_f_3066_, lean_object* v_init_3067_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3066_, v_map_3065_, v_init_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object* v_map_3069_, lean_object* v_f_3070_, lean_object* v_init_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(v_map_3069_, v_f_3070_, v_init_3071_);
lean_dec_ref(v_map_3069_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object* v_00_u03c3_3073_, lean_object* v_00_u03b2_3074_, lean_object* v_map_3075_, lean_object* v_f_3076_, lean_object* v_init_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3076_, v_map_3075_, v_init_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3079_, lean_object* v_00_u03b2_3080_, lean_object* v_map_3081_, lean_object* v_f_3082_, lean_object* v_init_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(v_00_u03c3_3079_, v_00_u03b2_3080_, v_map_3081_, v_f_3082_, v_init_3083_);
lean_dec_ref(v_map_3081_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3085_, lean_object* v_00_u03b1_3086_, lean_object* v_00_u03b2_3087_, lean_object* v_f_3088_, lean_object* v_x_3089_, lean_object* v_x_3090_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3088_, v_x_3089_, v_x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3092_, lean_object* v_00_u03b1_3093_, lean_object* v_00_u03b2_3094_, lean_object* v_f_3095_, lean_object* v_x_3096_, lean_object* v_x_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(v_00_u03c3_3092_, v_00_u03b1_3093_, v_00_u03b2_3094_, v_f_3095_, v_x_3096_, v_x_3097_);
lean_dec_ref(v_x_3096_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3099_, lean_object* v_00_u03b2_3100_, lean_object* v_00_u03c3_3101_, lean_object* v_f_3102_, lean_object* v_as_3103_, size_t v_i_3104_, size_t v_stop_3105_, lean_object* v_b_3106_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3102_, v_as_3103_, v_i_3104_, v_stop_3105_, v_b_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3108_, lean_object* v_00_u03b2_3109_, lean_object* v_00_u03c3_3110_, lean_object* v_f_3111_, lean_object* v_as_3112_, lean_object* v_i_3113_, lean_object* v_stop_3114_, lean_object* v_b_3115_){
_start:
{
size_t v_i_boxed_3116_; size_t v_stop_boxed_3117_; lean_object* v_res_3118_; 
v_i_boxed_3116_ = lean_unbox_usize(v_i_3113_);
lean_dec(v_i_3113_);
v_stop_boxed_3117_ = lean_unbox_usize(v_stop_3114_);
lean_dec(v_stop_3114_);
v_res_3118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3108_, v_00_u03b2_3109_, v_00_u03c3_3110_, v_f_3111_, v_as_3112_, v_i_boxed_3116_, v_stop_boxed_3117_, v_b_3115_);
lean_dec_ref(v_as_3112_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3119_, lean_object* v_00_u03b1_3120_, lean_object* v_00_u03b2_3121_, lean_object* v_f_3122_, lean_object* v_keys_3123_, lean_object* v_vals_3124_, lean_object* v_heq_3125_, lean_object* v_i_3126_, lean_object* v_acc_3127_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3122_, v_keys_3123_, v_vals_3124_, v_i_3126_, v_acc_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3129_, lean_object* v_00_u03b1_3130_, lean_object* v_00_u03b2_3131_, lean_object* v_f_3132_, lean_object* v_keys_3133_, lean_object* v_vals_3134_, lean_object* v_heq_3135_, lean_object* v_i_3136_, lean_object* v_acc_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3129_, v_00_u03b1_3130_, v_00_u03b2_3131_, v_f_3132_, v_keys_3133_, v_vals_3134_, v_heq_3135_, v_i_3136_, v_acc_3137_);
lean_dec_ref(v_vals_3134_);
lean_dec_ref(v_keys_3133_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* v_env_3139_){
_start:
{
lean_object* v___x_3140_; lean_object* v_ext_3141_; lean_object* v_toEnvExtension_3142_; lean_object* v_asyncMode_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v_tokens_3146_; 
v___x_3140_ = l_Lean_Parser_parserExtension;
v_ext_3141_ = lean_ctor_get(v___x_3140_, 1);
v_toEnvExtension_3142_ = lean_ctor_get(v_ext_3141_, 0);
v_asyncMode_3143_ = lean_ctor_get(v_toEnvExtension_3142_, 2);
v___x_3144_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3145_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3144_, v___x_3140_, v_env_3139_, v_asyncMode_3143_);
v_tokens_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc_ref(v_tokens_3146_);
lean_dec(v___x_3145_);
return v_tokens_3146_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__8));
v___x_3172_ = l_Lean_mkAtom(v___x_3171_);
return v___x_3172_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__10, &l_Lean_Parser_mkInputContext___auto__1___closed__10_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__10);
v___x_3174_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3175_ = lean_array_push(v___x_3174_, v___x_3173_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3187_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3188_ = lean_array_push(v___x_3187_, v___x_3186_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3189_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__15, &l_Lean_Parser_mkInputContext___auto__1___closed__15_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__15);
v___x_3190_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__13));
v___x_3191_ = lean_box(2);
v___x_3192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v___x_3190_);
lean_ctor_set(v___x_3192_, 2, v___x_3189_);
return v___x_3192_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__16, &l_Lean_Parser_mkInputContext___auto__1___closed__16_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__16);
v___x_3194_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__11, &l_Lean_Parser_mkInputContext___auto__1___closed__11_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__11);
v___x_3195_ = lean_array_push(v___x_3194_, v___x_3193_);
return v___x_3195_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3196_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3197_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__17, &l_Lean_Parser_mkInputContext___auto__1___closed__17_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__17);
v___x_3198_ = lean_array_push(v___x_3197_, v___x_3196_);
return v___x_3198_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3199_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3200_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__18, &l_Lean_Parser_mkInputContext___auto__1___closed__18_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__18);
v___x_3201_ = lean_array_push(v___x_3200_, v___x_3199_);
return v___x_3201_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3202_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3203_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__19, &l_Lean_Parser_mkInputContext___auto__1___closed__19_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__19);
v___x_3204_ = lean_array_push(v___x_3203_, v___x_3202_);
return v___x_3204_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3206_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__20, &l_Lean_Parser_mkInputContext___auto__1___closed__20_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__20);
v___x_3207_ = lean_array_push(v___x_3206_, v___x_3205_);
return v___x_3207_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3208_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__21, &l_Lean_Parser_mkInputContext___auto__1___closed__21_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__21);
v___x_3209_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__9));
v___x_3210_ = lean_box(2);
v___x_3211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
lean_ctor_set(v___x_3211_, 1, v___x_3209_);
lean_ctor_set(v___x_3211_, 2, v___x_3208_);
return v___x_3211_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__22, &l_Lean_Parser_mkInputContext___auto__1___closed__22_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__22);
v___x_3213_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3214_ = lean_array_push(v___x_3213_, v___x_3212_);
return v___x_3214_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3215_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__23, &l_Lean_Parser_mkInputContext___auto__1___closed__23_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__23);
v___x_3216_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3217_ = lean_box(2);
v___x_3218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
lean_ctor_set(v___x_3218_, 1, v___x_3216_);
lean_ctor_set(v___x_3218_, 2, v___x_3215_);
return v___x_3218_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3219_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__24, &l_Lean_Parser_mkInputContext___auto__1___closed__24_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__24);
v___x_3220_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3221_ = lean_array_push(v___x_3220_, v___x_3219_);
return v___x_3221_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3222_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__25, &l_Lean_Parser_mkInputContext___auto__1___closed__25_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__25);
v___x_3223_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3224_ = lean_box(2);
v___x_3225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set(v___x_3225_, 1, v___x_3223_);
lean_ctor_set(v___x_3225_, 2, v___x_3222_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__26, &l_Lean_Parser_mkInputContext___auto__1___closed__26_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__26);
v___x_3227_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3228_ = lean_array_push(v___x_3227_, v___x_3226_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3229_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__27, &l_Lean_Parser_mkInputContext___auto__1___closed__27_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__27);
v___x_3230_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3231_ = lean_box(2);
v___x_3232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v___x_3230_);
lean_ctor_set(v___x_3232_, 2, v___x_3229_);
return v___x_3232_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1(void){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__28, &l_Lean_Parser_mkInputContext___auto__1___closed__28_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__28);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object* v_input_3234_, lean_object* v_fileName_3235_, uint8_t v_normalizeLineEndings_3236_, lean_object* v_endPos_3237_){
_start:
{
lean_object* v_fst_3239_; lean_object* v_snd_3240_; lean_object* v_text_3246_; 
v_text_3246_ = l_Lean_FileMap_ofString(v_input_3234_);
if (v_normalizeLineEndings_3236_ == 0)
{
v_fst_3239_ = v_text_3246_;
v_snd_3240_ = v_endPos_3237_;
goto v___jp_3238_;
}
else
{
lean_object* v_source_3247_; lean_object* v_endPos_x27_3248_; lean_object* v___x_3249_; lean_object* v_text_3250_; lean_object* v___x_3251_; 
v_source_3247_ = lean_ctor_get(v_text_3246_, 0);
lean_inc_ref(v_source_3247_);
v_endPos_x27_3248_ = l_Lean_FileMap_toPosition(v_text_3246_, v_endPos_3237_);
lean_dec(v_endPos_3237_);
v___x_3249_ = l_String_crlfToLf(v_source_3247_);
lean_dec_ref(v_source_3247_);
v_text_3250_ = l_Lean_FileMap_ofString(v___x_3249_);
v___x_3251_ = l_Lean_FileMap_ofPosition(v_text_3250_, v_endPos_x27_3248_);
v_fst_3239_ = v_text_3250_;
v_snd_3240_ = v___x_3251_;
goto v___jp_3238_;
}
v___jp_3238_:
{
lean_object* v_source_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; 
v_source_3241_ = lean_ctor_get(v_fst_3239_, 0);
lean_inc_ref(v_source_3241_);
v___x_3242_ = lean_string_utf8_byte_size(v_source_3241_);
v___x_3243_ = lean_nat_dec_le(v_snd_3240_, v___x_3242_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; 
lean_dec(v_snd_3240_);
v___x_3244_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3244_, 0, v_source_3241_);
lean_ctor_set(v___x_3244_, 1, v_fileName_3235_);
lean_ctor_set(v___x_3244_, 2, v_fst_3239_);
lean_ctor_set(v___x_3244_, 3, v___x_3242_);
return v___x_3244_;
}
else
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3245_, 0, v_source_3241_);
lean_ctor_set(v___x_3245_, 1, v_fileName_3235_);
lean_ctor_set(v___x_3245_, 2, v_fst_3239_);
lean_ctor_set(v___x_3245_, 3, v_snd_3240_);
return v___x_3245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object* v_input_3252_, lean_object* v_fileName_3253_, lean_object* v_normalizeLineEndings_3254_, lean_object* v_endPos_3255_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3256_; lean_object* v_res_3257_; 
v_normalizeLineEndings_boxed_3256_ = lean_unbox(v_normalizeLineEndings_3254_);
v_res_3257_ = l_Lean_Parser_mkInputContext___redArg(v_input_3252_, v_fileName_3253_, v_normalizeLineEndings_boxed_3256_, v_endPos_3255_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object* v_input_3258_, lean_object* v_fileName_3259_, uint8_t v_normalizeLineEndings_3260_, lean_object* v_endPos_3261_, lean_object* v_endPos__valid_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_Parser_mkInputContext___redArg(v_input_3258_, v_fileName_3259_, v_normalizeLineEndings_3260_, v_endPos_3261_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object* v_input_3264_, lean_object* v_fileName_3265_, lean_object* v_normalizeLineEndings_3266_, lean_object* v_endPos_3267_, lean_object* v_endPos__valid_3268_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3269_; lean_object* v_res_3270_; 
v_normalizeLineEndings_boxed_3269_ = lean_unbox(v_normalizeLineEndings_3266_);
v_res_3270_ = l_Lean_Parser_mkInputContext(v_input_3264_, v_fileName_3265_, v_normalizeLineEndings_boxed_3269_, v_endPos_3267_, v_endPos__valid_3268_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* v_input_3273_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3274_ = l_Lean_Parser_SyntaxStack_empty;
v___x_3275_ = lean_unsigned_to_nat(0u);
v___x_3276_ = l_Lean_Parser_initCacheForInput(v_input_3273_);
v___x_3277_ = lean_box(0);
v___x_3278_ = ((lean_object*)(l_Lean_Parser_mkParserState___closed__0));
v___x_3279_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3274_);
lean_ctor_set(v___x_3279_, 1, v___x_3275_);
lean_ctor_set(v___x_3279_, 2, v___x_3275_);
lean_ctor_set(v___x_3279_, 3, v___x_3276_);
lean_ctor_set(v___x_3279_, 4, v___x_3277_);
lean_ctor_set(v___x_3279_, 5, v___x_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* v_input_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_Parser_mkParserState(v_input_3280_);
lean_dec_ref(v_input_3280_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* v_env_3284_, lean_object* v_catName_3285_, lean_object* v_input_3286_, lean_object* v_fileName_3287_){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v_p_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; lean_object* v_ictx_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v_s_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
v___x_3288_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__0));
v___x_3289_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 1);
lean_closure_set(v___x_3289_, 0, v_catName_3285_);
v_p_3290_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_3290_, 0, v___x_3288_);
lean_closure_set(v_p_3290_, 1, v___x_3289_);
v___x_3291_ = 1;
v___x_3292_ = lean_string_utf8_byte_size(v_input_3286_);
lean_inc_ref(v_input_3286_);
v_ictx_3293_ = l_Lean_Parser_mkInputContext___redArg(v_input_3286_, v_fileName_3287_, v___x_3291_, v___x_3292_);
v___x_3294_ = l_Lean_Options_empty;
v___x_3295_ = lean_box(0);
v___x_3296_ = lean_box(0);
lean_inc_ref(v_env_3284_);
v___x_3297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3297_, 0, v_env_3284_);
lean_ctor_set(v___x_3297_, 1, v___x_3294_);
lean_ctor_set(v___x_3297_, 2, v___x_3295_);
lean_ctor_set(v___x_3297_, 3, v___x_3296_);
v___x_3298_ = l_Lean_Parser_getTokenTable(v_env_3284_);
v___x_3299_ = l_Lean_Parser_mkParserState(v_input_3286_);
lean_dec_ref(v_input_3286_);
lean_inc_ref(v_ictx_3293_);
v_s_3300_ = l_Lean_Parser_ParserFn_run(v_p_3290_, v_ictx_3293_, v___x_3297_, v___x_3298_, v___x_3299_);
lean_inc_ref(v_s_3300_);
v___x_3301_ = l_Lean_Parser_ParserState_allErrors(v_s_3300_);
v___x_3302_ = lean_array_get_size(v___x_3301_);
lean_dec_ref(v___x_3301_);
v___x_3303_ = lean_unsigned_to_nat(0u);
v___x_3304_ = lean_nat_dec_eq(v___x_3302_, v___x_3303_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3293_, v_s_3300_);
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
return v___x_3306_;
}
else
{
lean_object* v_stxStack_3307_; lean_object* v_pos_3308_; uint8_t v___x_3309_; 
v_stxStack_3307_ = lean_ctor_get(v_s_3300_, 0);
lean_inc_ref(v_stxStack_3307_);
v_pos_3308_ = lean_ctor_get(v_s_3300_, 2);
lean_inc(v_pos_3308_);
v___x_3309_ = l_Lean_Parser_InputContext_atEnd(v_ictx_3293_, v_pos_3308_);
lean_dec(v_pos_3308_);
if (v___x_3309_ == 0)
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_dec_ref(v_stxStack_3307_);
v___x_3310_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__1));
v___x_3311_ = l_Lean_Parser_ParserState_mkError(v_s_3300_, v___x_3310_);
v___x_3312_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3293_, v___x_3311_);
v___x_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
return v___x_3313_;
}
else
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_dec_ref(v_s_3300_);
lean_dec_ref(v_ictx_3293_);
v___x_3314_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3307_);
lean_dec_ref(v_stxStack_3307_);
v___x_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
return v___x_3315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* v_addFnName_3316_, lean_object* v_catName_3317_, lean_object* v_declName_3318_, lean_object* v_prio_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v_val_3335_; lean_object* v___x_3336_; 
v___x_3323_ = lean_box(0);
v___x_3324_ = l_Lean_mkConst(v_addFnName_3316_, v___x_3323_);
v___x_3325_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_catName_3317_);
lean_inc_n(v_declName_3318_, 2);
v___x_3326_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3318_);
v___x_3327_ = l_Lean_mkConst(v_declName_3318_, v___x_3323_);
v___x_3328_ = l_Lean_mkRawNatLit(v_prio_3319_);
v___x_3329_ = lean_unsigned_to_nat(4u);
v___x_3330_ = lean_mk_empty_array_with_capacity(v___x_3329_);
v___x_3331_ = lean_array_push(v___x_3330_, v___x_3325_);
v___x_3332_ = lean_array_push(v___x_3331_, v___x_3326_);
v___x_3333_ = lean_array_push(v___x_3332_, v___x_3327_);
v___x_3334_ = lean_array_push(v___x_3333_, v___x_3328_);
v_val_3335_ = l_Lean_mkAppN(v___x_3324_, v___x_3334_);
lean_dec_ref(v___x_3334_);
v___x_3336_ = l_Lean_declareBuiltin(v_declName_3318_, v_val_3335_, v_a_3320_, v_a_3321_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object* v_addFnName_3337_, lean_object* v_catName_3338_, lean_object* v_declName_3339_, lean_object* v_prio_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3337_, v_catName_3338_, v_declName_3339_, v_prio_3340_, v_a_3341_, v_a_3342_);
lean_dec(v_a_3342_);
lean_dec_ref(v_a_3341_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* v_catName_3350_, lean_object* v_declName_3351_, lean_object* v_prio_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = ((lean_object*)(l_Lean_Parser_declareLeadingBuiltinParser___closed__1));
v___x_3357_ = l_Lean_Parser_declareBuiltinParser(v___x_3356_, v_catName_3350_, v_declName_3351_, v_prio_3352_, v_a_3353_, v_a_3354_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object* v_catName_3358_, lean_object* v_declName_3359_, lean_object* v_prio_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3358_, v_declName_3359_, v_prio_3360_, v_a_3361_, v_a_3362_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* v_catName_3370_, lean_object* v_declName_3371_, lean_object* v_prio_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = ((lean_object*)(l_Lean_Parser_declareTrailingBuiltinParser___closed__1));
v___x_3377_ = l_Lean_Parser_declareBuiltinParser(v___x_3376_, v_catName_3370_, v_declName_3371_, v_prio_3372_, v_a_3373_, v_a_3374_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object* v_catName_3378_, lean_object* v_declName_3379_, lean_object* v_prio_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3378_, v_declName_3379_, v_prio_3380_, v_a_3381_, v_a_3382_);
lean_dec(v_a_3382_);
lean_dec_ref(v_a_3381_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* v_args_3391_){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; 
v___x_3392_ = l_Lean_Syntax_getNumArgs(v_args_3391_);
v___x_3393_ = lean_unsigned_to_nat(0u);
v___x_3394_ = lean_nat_dec_eq(v___x_3392_, v___x_3393_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3395_ = lean_unsigned_to_nat(1u);
v___x_3396_ = lean_nat_dec_eq(v___x_3392_, v___x_3395_);
lean_dec(v___x_3392_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; 
v___x_3397_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__1));
return v___x_3397_;
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = l_Lean_Syntax_getArg(v_args_3391_, v___x_3393_);
v___x_3399_ = l_Lean_Syntax_isNatLit_x3f(v___x_3398_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3400_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__2));
v___x_3401_ = l_Lean_Syntax_formatStx(v___x_3398_, v___x_3399_, v___x_3394_);
v___x_3402_ = l_Std_Format_defWidth;
v___x_3403_ = l_Std_Format_pretty(v___x_3401_, v___x_3402_, v___x_3393_, v___x_3393_);
v___x_3404_ = lean_string_append(v___x_3400_, v___x_3403_);
lean_dec_ref(v___x_3403_);
v___x_3405_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3406_ = lean_string_append(v___x_3404_, v___x_3405_);
v___x_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
return v___x_3407_;
}
else
{
lean_object* v_val_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec(v___x_3398_);
v_val_3408_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3399_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_val_3408_);
lean_dec(v___x_3399_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_val_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
else
{
lean_object* v___x_3416_; 
lean_dec(v___x_3392_);
v___x_3416_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__3));
return v___x_3416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* v_args_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lean_Parser_getParserPriority(v_args_3417_);
lean_dec(v_args_3417_);
return v_res_3418_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0));
v___x_3421_ = l_Lean_stringToMessageData(v___x_3420_);
return v___x_3421_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2));
v___x_3424_ = l_Lean_stringToMessageData(v___x_3423_);
return v___x_3424_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3426_ = l_Lean_stringToMessageData(v___x_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object* v_name_3430_, uint8_t v_kind_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___y_3441_; 
v___x_3435_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1);
v___x_3436_ = l_Lean_MessageData_ofName(v_name_3430_);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3435_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3);
v___x_3439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3437_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
switch(v_kind_3431_)
{
case 0:
{
lean_object* v___x_3448_; 
v___x_3448_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5));
v___y_3441_ = v___x_3448_;
goto v___jp_3440_;
}
case 1:
{
lean_object* v___x_3449_; 
v___x_3449_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6));
v___y_3441_ = v___x_3449_;
goto v___jp_3440_;
}
default: 
{
lean_object* v___x_3450_; 
v___x_3450_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7));
v___y_3441_ = v___x_3450_;
goto v___jp_3440_;
}
}
v___jp_3440_:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
lean_inc_ref(v___y_3441_);
v___x_3442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___y_3441_);
v___x_3443_ = l_Lean_MessageData_ofFormat(v___x_3442_);
v___x_3444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3439_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v___x_3445_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3444_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___x_3447_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3446_, v___y_3432_, v___y_3433_);
return v___x_3447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object* v_name_3451_, lean_object* v_kind_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
uint8_t v_kind_boxed_3456_; lean_object* v_res_3457_; 
v_kind_boxed_3456_ = lean_unbox(v_kind_3452_);
v_res_3457_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3451_, v_kind_boxed_3456_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3458_, lean_object* v_msg_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v_fileName_3463_; lean_object* v_fileMap_3464_; lean_object* v_options_3465_; lean_object* v_currRecDepth_3466_; lean_object* v_maxRecDepth_3467_; lean_object* v_ref_3468_; lean_object* v_currNamespace_3469_; lean_object* v_openDecls_3470_; lean_object* v_initHeartbeats_3471_; lean_object* v_maxHeartbeats_3472_; lean_object* v_quotContext_3473_; lean_object* v_currMacroScope_3474_; uint8_t v_diag_3475_; lean_object* v_cancelTk_x3f_3476_; uint8_t v_suppressElabErrors_3477_; lean_object* v_inheritedTraceOptions_3478_; lean_object* v_ref_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v_fileName_3463_ = lean_ctor_get(v___y_3460_, 0);
v_fileMap_3464_ = lean_ctor_get(v___y_3460_, 1);
v_options_3465_ = lean_ctor_get(v___y_3460_, 2);
v_currRecDepth_3466_ = lean_ctor_get(v___y_3460_, 3);
v_maxRecDepth_3467_ = lean_ctor_get(v___y_3460_, 4);
v_ref_3468_ = lean_ctor_get(v___y_3460_, 5);
v_currNamespace_3469_ = lean_ctor_get(v___y_3460_, 6);
v_openDecls_3470_ = lean_ctor_get(v___y_3460_, 7);
v_initHeartbeats_3471_ = lean_ctor_get(v___y_3460_, 8);
v_maxHeartbeats_3472_ = lean_ctor_get(v___y_3460_, 9);
v_quotContext_3473_ = lean_ctor_get(v___y_3460_, 10);
v_currMacroScope_3474_ = lean_ctor_get(v___y_3460_, 11);
v_diag_3475_ = lean_ctor_get_uint8(v___y_3460_, sizeof(void*)*14);
v_cancelTk_x3f_3476_ = lean_ctor_get(v___y_3460_, 12);
v_suppressElabErrors_3477_ = lean_ctor_get_uint8(v___y_3460_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3478_ = lean_ctor_get(v___y_3460_, 13);
v_ref_3479_ = l_Lean_replaceRef(v_ref_3458_, v_ref_3468_);
lean_inc_ref(v_inheritedTraceOptions_3478_);
lean_inc(v_cancelTk_x3f_3476_);
lean_inc(v_currMacroScope_3474_);
lean_inc(v_quotContext_3473_);
lean_inc(v_maxHeartbeats_3472_);
lean_inc(v_initHeartbeats_3471_);
lean_inc(v_openDecls_3470_);
lean_inc(v_currNamespace_3469_);
lean_inc(v_maxRecDepth_3467_);
lean_inc(v_currRecDepth_3466_);
lean_inc_ref(v_options_3465_);
lean_inc_ref(v_fileMap_3464_);
lean_inc_ref(v_fileName_3463_);
v___x_3480_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3480_, 0, v_fileName_3463_);
lean_ctor_set(v___x_3480_, 1, v_fileMap_3464_);
lean_ctor_set(v___x_3480_, 2, v_options_3465_);
lean_ctor_set(v___x_3480_, 3, v_currRecDepth_3466_);
lean_ctor_set(v___x_3480_, 4, v_maxRecDepth_3467_);
lean_ctor_set(v___x_3480_, 5, v_ref_3479_);
lean_ctor_set(v___x_3480_, 6, v_currNamespace_3469_);
lean_ctor_set(v___x_3480_, 7, v_openDecls_3470_);
lean_ctor_set(v___x_3480_, 8, v_initHeartbeats_3471_);
lean_ctor_set(v___x_3480_, 9, v_maxHeartbeats_3472_);
lean_ctor_set(v___x_3480_, 10, v_quotContext_3473_);
lean_ctor_set(v___x_3480_, 11, v_currMacroScope_3474_);
lean_ctor_set(v___x_3480_, 12, v_cancelTk_x3f_3476_);
lean_ctor_set(v___x_3480_, 13, v_inheritedTraceOptions_3478_);
lean_ctor_set_uint8(v___x_3480_, sizeof(void*)*14, v_diag_3475_);
lean_ctor_set_uint8(v___x_3480_, sizeof(void*)*14 + 1, v_suppressElabErrors_3477_);
v___x_3481_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_3459_, v___x_3480_, v___y_3461_);
lean_dec_ref_known(v___x_3480_, 14);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3482_, lean_object* v_msg_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3482_, v_msg_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v_ref_3482_);
return v_res_3487_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_3490_ = l_Lean_stringToMessageData(v___x_3489_);
return v___x_3490_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_3493_ = l_Lean_stringToMessageData(v___x_3492_);
return v___x_3493_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_3496_ = l_Lean_stringToMessageData(v___x_3495_);
return v___x_3496_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_3499_ = l_Lean_stringToMessageData(v___x_3498_);
return v___x_3499_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_3502_ = l_Lean_stringToMessageData(v___x_3501_);
return v___x_3502_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_3505_ = l_Lean_stringToMessageData(v___x_3504_);
return v___x_3505_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_3508_ = l_Lean_stringToMessageData(v___x_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_3509_, lean_object* v_declHint_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v___x_3513_; lean_object* v_env_3514_; uint8_t v___x_3515_; 
v___x_3513_ = lean_st_ref_get(v___y_3511_);
v_env_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc_ref(v_env_3514_);
lean_dec(v___x_3513_);
v___x_3515_ = l_Lean_Name_isAnonymous(v_declHint_3510_);
if (v___x_3515_ == 0)
{
uint8_t v_isExporting_3516_; 
v_isExporting_3516_ = lean_ctor_get_uint8(v_env_3514_, sizeof(void*)*8);
if (v_isExporting_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_dec_ref(v_env_3514_);
lean_dec(v_declHint_3510_);
v___x_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_msg_3509_);
return v___x_3517_;
}
else
{
lean_object* v___x_3518_; uint8_t v___x_3519_; 
lean_inc_ref(v_env_3514_);
v___x_3518_ = l_Lean_Environment_setExporting(v_env_3514_, v___x_3515_);
lean_inc(v_declHint_3510_);
lean_inc_ref(v___x_3518_);
v___x_3519_ = l_Lean_Environment_contains(v___x_3518_, v_declHint_3510_, v_isExporting_3516_);
if (v___x_3519_ == 0)
{
lean_object* v___x_3520_; 
lean_dec_ref(v___x_3518_);
lean_dec_ref(v_env_3514_);
lean_dec(v_declHint_3510_);
v___x_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3520_, 0, v_msg_3509_);
return v___x_3520_;
}
else
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v_c_3526_; lean_object* v___x_3527_; 
v___x_3521_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_3522_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_3523_ = l_Lean_Options_empty;
v___x_3524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3518_);
lean_ctor_set(v___x_3524_, 1, v___x_3521_);
lean_ctor_set(v___x_3524_, 2, v___x_3522_);
lean_ctor_set(v___x_3524_, 3, v___x_3523_);
lean_inc(v_declHint_3510_);
v___x_3525_ = l_Lean_MessageData_ofConstName(v_declHint_3510_, v___x_3515_);
v_c_3526_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3526_, 0, v___x_3524_);
lean_ctor_set(v_c_3526_, 1, v___x_3525_);
v___x_3527_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3514_, v_declHint_3510_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
lean_dec_ref(v_env_3514_);
lean_dec(v_declHint_3510_);
v___x_3528_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v_c_3526_);
v___x_3530_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_3531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3529_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = l_Lean_MessageData_note(v___x_3531_);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v_msg_3509_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
return v___x_3534_;
}
else
{
lean_object* v_val_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3570_; 
v_val_3535_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3537_ = v___x_3527_;
v_isShared_3538_ = v_isSharedCheck_3570_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_val_3535_);
lean_dec(v___x_3527_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3570_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v_mod_3542_; uint8_t v___x_3543_; 
v___x_3539_ = lean_box(0);
v___x_3540_ = l_Lean_Environment_header(v_env_3514_);
lean_dec_ref(v_env_3514_);
v___x_3541_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3540_);
v_mod_3542_ = lean_array_get(v___x_3539_, v___x_3541_, v_val_3535_);
lean_dec(v_val_3535_);
lean_dec_ref(v___x_3541_);
v___x_3543_ = l_Lean_isPrivateName(v_declHint_3510_);
lean_dec(v_declHint_3510_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3555_; 
v___x_3544_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_3545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
lean_ctor_set(v___x_3545_, 1, v_c_3526_);
v___x_3546_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_3547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3545_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = l_Lean_MessageData_ofName(v_mod_3542_);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_3551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3549_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = l_Lean_MessageData_note(v___x_3551_);
v___x_3553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3553_, 0, v_msg_3509_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set_tag(v___x_3537_, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3553_);
v___x_3555_ = v___x_3537_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3568_; 
v___x_3557_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
lean_ctor_set(v___x_3558_, 1, v_c_3526_);
v___x_3559_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_3560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3558_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = l_Lean_MessageData_ofName(v_mod_3542_);
v___x_3562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v___x_3563_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_3564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3562_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
v___x_3565_ = l_Lean_MessageData_note(v___x_3564_);
v___x_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3566_, 0, v_msg_3509_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set_tag(v___x_3537_, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3566_);
v___x_3568_ = v___x_3537_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3571_; 
lean_dec_ref(v_env_3514_);
lean_dec(v_declHint_3510_);
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v_msg_3509_);
return v___x_3571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_3572_, lean_object* v_declHint_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3572_, v_declHint_3573_, v___y_3574_);
lean_dec(v___y_3574_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_3577_, lean_object* v_declHint_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v___x_3582_; lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3592_; 
v___x_3582_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3577_, v_declHint_3578_, v___y_3580_);
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3585_ = v___x_3582_;
v_isShared_3586_ = v_isSharedCheck_3592_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3582_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3592_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3590_; 
v___x_3587_ = l_Lean_unknownIdentifierMessageTag;
v___x_3588_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
lean_ctor_set(v___x_3588_, 1, v_a_3583_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v___x_3588_);
v___x_3590_ = v___x_3585_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_3593_, lean_object* v_declHint_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3593_, v_declHint_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3599_, lean_object* v_msg_3600_, lean_object* v_declHint_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v___x_3605_; lean_object* v_a_3606_; lean_object* v___x_3607_; 
v___x_3605_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3600_, v_declHint_3601_, v___y_3602_, v___y_3603_);
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref(v___x_3605_);
v___x_3607_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3599_, v_a_3606_, v___y_3602_, v___y_3603_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3608_, lean_object* v_msg_3609_, lean_object* v_declHint_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3608_, v_msg_3609_, v_declHint_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v_ref_3608_);
return v_res_3614_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_3616_ = l_Lean_stringToMessageData(v___x_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3617_, lean_object* v_constName_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v___x_3622_; uint8_t v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3622_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3623_ = 0;
lean_inc(v_constName_3618_);
v___x_3624_ = l_Lean_MessageData_ofConstName(v_constName_3618_, v___x_3623_);
v___x_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3622_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___x_3626_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3625_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3617_, v___x_3627_, v_constName_3618_, v___y_3619_, v___y_3620_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3629_, lean_object* v_constName_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3629_, v_constName_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v_ref_3629_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object* v_constName_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_ref_3639_; lean_object* v___x_3640_; 
v_ref_3639_ = lean_ctor_get(v___y_3636_, 5);
v___x_3640_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3639_, v_constName_3635_, v___y_3636_, v___y_3637_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3641_, v___y_3642_, v___y_3643_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object* v_constName_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v___x_3650_; lean_object* v_env_3651_; uint8_t v___x_3652_; lean_object* v___x_3653_; 
v___x_3650_ = lean_st_ref_get(v___y_3648_);
v_env_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc_ref(v_env_3651_);
lean_dec(v___x_3650_);
v___x_3652_ = 0;
lean_inc(v_constName_3646_);
v___x_3653_ = l_Lean_Environment_find_x3f(v_env_3651_, v_constName_3646_, v___x_3652_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3646_, v___y_3647_, v___y_3648_);
return v___x_3654_;
}
else
{
lean_object* v_val_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v_constName_3646_);
v_val_3655_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3653_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_val_3655_);
lean_dec(v___x_3653_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
lean_ctor_set_tag(v___x_3657_, 0);
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_val_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object* v_constName_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
return v_res_3667_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1(void){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3669_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0));
v___x_3670_ = l_Lean_stringToMessageData(v___x_3669_);
return v___x_3670_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2));
v___x_3673_ = l_Lean_stringToMessageData(v___x_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* v_attrName_3674_, lean_object* v_catName_3675_, lean_object* v_declName_3676_, lean_object* v_stx_3677_, uint8_t v_kind_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_){
_start:
{
lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___x_3702_; 
v___x_3702_ = l_Lean_Attribute_Builtin_getPrio(v_stx_3677_, v_a_3679_, v_a_3680_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v___y_3705_; lean_object* v___y_3706_; uint8_t v___x_3734_; uint8_t v___x_3735_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_a_3703_);
lean_dec_ref_known(v___x_3702_, 1);
v___x_3734_ = 0;
v___x_3735_ = l_Lean_instBEqAttributeKind_beq(v_kind_3678_, v___x_3734_);
if (v___x_3735_ == 0)
{
lean_object* v___x_3736_; 
lean_dec(v_a_3703_);
lean_dec(v_declName_3676_);
lean_dec(v_catName_3675_);
v___x_3736_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_attrName_3674_, v_kind_3678_, v_a_3679_, v_a_3680_);
return v___x_3736_;
}
else
{
lean_dec(v_attrName_3674_);
v___y_3705_ = v_a_3679_;
v___y_3706_ = v_a_3680_;
goto v___jp_3704_;
}
v___jp_3704_:
{
lean_object* v___x_3707_; 
lean_inc(v_declName_3676_);
v___x_3707_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_declName_3676_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3709_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___x_3707_, 1);
v___x_3709_ = l_Lean_ConstantInfo_type(v_a_3708_);
if (lean_obj_tag(v___x_3709_) == 4)
{
lean_object* v_declName_3710_; 
v_declName_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_declName_3710_);
lean_dec_ref_known(v___x_3709_, 2);
if (lean_obj_tag(v_declName_3710_) == 1)
{
lean_object* v_pre_3711_; 
v_pre_3711_ = lean_ctor_get(v_declName_3710_, 0);
lean_inc(v_pre_3711_);
if (lean_obj_tag(v_pre_3711_) == 1)
{
lean_object* v_pre_3712_; 
v_pre_3712_ = lean_ctor_get(v_pre_3711_, 0);
lean_inc(v_pre_3712_);
if (lean_obj_tag(v_pre_3712_) == 1)
{
lean_object* v_pre_3713_; 
v_pre_3713_ = lean_ctor_get(v_pre_3712_, 0);
if (lean_obj_tag(v_pre_3713_) == 0)
{
lean_object* v_str_3714_; lean_object* v_str_3715_; lean_object* v_str_3716_; lean_object* v___x_3717_; uint8_t v___x_3718_; 
v_str_3714_ = lean_ctor_get(v_declName_3710_, 1);
lean_inc_ref(v_str_3714_);
lean_dec_ref_known(v_declName_3710_, 2);
v_str_3715_ = lean_ctor_get(v_pre_3711_, 1);
lean_inc_ref(v_str_3715_);
lean_dec_ref_known(v_pre_3711_, 2);
v_str_3716_ = lean_ctor_get(v_pre_3712_, 1);
lean_inc_ref(v_str_3716_);
lean_dec_ref_known(v_pre_3712_, 2);
v___x_3717_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3718_ = lean_string_dec_eq(v_str_3716_, v___x_3717_);
lean_dec_ref(v_str_3716_);
if (v___x_3718_ == 0)
{
lean_dec_ref(v_str_3715_);
lean_dec_ref(v_str_3714_);
lean_dec(v_a_3703_);
lean_dec(v_catName_3675_);
v___y_3689_ = v_a_3708_;
v___y_3690_ = v___y_3705_;
v___y_3691_ = v___y_3706_;
goto v___jp_3688_;
}
else
{
lean_object* v___x_3719_; uint8_t v___x_3720_; 
v___x_3719_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3720_ = lean_string_dec_eq(v_str_3715_, v___x_3719_);
lean_dec_ref(v_str_3715_);
if (v___x_3720_ == 0)
{
lean_dec_ref(v_str_3714_);
lean_dec(v_a_3703_);
lean_dec(v_catName_3675_);
v___y_3689_ = v_a_3708_;
v___y_3690_ = v___y_3705_;
v___y_3691_ = v___y_3706_;
goto v___jp_3688_;
}
else
{
lean_object* v___x_3721_; uint8_t v___x_3722_; 
v___x_3721_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_3722_ = lean_string_dec_eq(v_str_3714_, v___x_3721_);
if (v___x_3722_ == 0)
{
uint8_t v___x_3723_; 
v___x_3723_ = lean_string_dec_eq(v_str_3714_, v___x_3719_);
lean_dec_ref(v_str_3714_);
if (v___x_3723_ == 0)
{
lean_dec(v_a_3703_);
lean_dec(v_catName_3675_);
v___y_3689_ = v_a_3708_;
v___y_3690_ = v___y_3705_;
v___y_3691_ = v___y_3706_;
goto v___jp_3688_;
}
else
{
lean_object* v___x_3724_; 
lean_dec(v_a_3708_);
lean_inc(v_declName_3676_);
lean_inc(v_catName_3675_);
v___x_3724_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3675_, v_declName_3676_, v_a_3703_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_dec_ref_known(v___x_3724_, 1);
v___y_3683_ = v___y_3705_;
v___y_3684_ = v___y_3706_;
goto v___jp_3682_;
}
else
{
lean_dec(v_declName_3676_);
lean_dec(v_catName_3675_);
return v___x_3724_;
}
}
}
else
{
lean_object* v___x_3725_; 
lean_dec_ref(v_str_3714_);
lean_dec(v_a_3708_);
lean_inc(v_declName_3676_);
lean_inc(v_catName_3675_);
v___x_3725_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3675_, v_declName_3676_, v_a_3703_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_dec_ref_known(v___x_3725_, 1);
v___y_3683_ = v___y_3705_;
v___y_3684_ = v___y_3706_;
goto v___jp_3682_;
}
else
{
lean_dec(v_declName_3676_);
lean_dec(v_catName_3675_);
return v___x_3725_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3712_, 2);
lean_dec_ref_known(v_pre_3711_, 2);
lean_dec_ref_known(v_declName_3710_, 2);
lean_dec(v_a_3703_);
lean_dec(v_catName_3675_);
v___y_3689_ = v_a_3708_;
v___y_3690_ = v___y_3705_;
v___y_3691_ = v___y_3706_;
goto v___jp_3688_;
}
}
else
{
lean_dec_ref_known(v_pre_3711_, 2);
lean_dec(v_pre_3712_);
lean_dec_ref_known(v_declName_3710_, 2);
lean_dec(v_a_3703_);
lean_dec(v_catName_3675_);
v___y_3689_ = v_a_3708_;
v___y_3690_ = v___y_3705_;
v___y_3691_ = v___y_3706_;
goto v___jp_3688_;
}
}
else
{
lean_dec_ref_known(v_declName_3710_, 2);
lean_dec(v_pre_3711_);
lean_dec(v_a_3703_);
lean_dec(v_catName_3675_);
v___y_3689_ = v_a_3708_;
v___y_3690_ = v___y_3705_;
v___y_3691_ = v___y_3706_;
goto v___jp_3688_;
}
}
else
{
lean_dec(v_declName_3710_);
lean_dec(v_a_3703_);
lean_dec(v_catName_3675_);
v___y_3689_ = v_a_3708_;
v___y_3690_ = v___y_3705_;
v___y_3691_ = v___y_3706_;
goto v___jp_3688_;
}
}
else
{
lean_dec_ref(v___x_3709_);
lean_dec(v_a_3703_);
lean_dec(v_catName_3675_);
v___y_3689_ = v_a_3708_;
v___y_3690_ = v___y_3705_;
v___y_3691_ = v___y_3706_;
goto v___jp_3688_;
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_dec(v_a_3703_);
lean_dec(v_declName_3676_);
lean_dec(v_catName_3675_);
v_a_3726_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3707_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3707_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_dec(v_declName_3676_);
lean_dec(v_catName_3675_);
lean_dec(v_attrName_3674_);
v_a_3737_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3702_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3702_);
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
v___jp_3682_:
{
lean_object* v___x_3685_; 
lean_inc(v_declName_3676_);
v___x_3685_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_3676_, v___y_3683_, v___y_3684_);
if (lean_obj_tag(v___x_3685_) == 0)
{
uint8_t v___x_3686_; lean_object* v___x_3687_; 
lean_dec_ref_known(v___x_3685_, 1);
v___x_3686_ = 1;
v___x_3687_ = l_Lean_Parser_runParserAttributeHooks(v_catName_3675_, v_declName_3676_, v___x_3686_, v___y_3683_, v___y_3684_);
return v___x_3687_;
}
else
{
lean_dec(v_declName_3676_);
lean_dec(v_catName_3675_);
return v___x_3685_;
}
}
v___jp_3688_:
{
lean_object* v___x_3692_; uint8_t v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3692_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
v___x_3693_ = 0;
v___x_3694_ = l_Lean_MessageData_ofConstName(v_declName_3676_, v___x_3693_);
v___x_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3692_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
v___x_3697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3695_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = l_Lean_ConstantInfo_type(v___y_3689_);
lean_dec_ref(v___y_3689_);
v___x_3699_ = l_Lean_indentExpr(v___x_3698_);
v___x_3700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3697_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
v___x_3701_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3700_, v___y_3690_, v___y_3691_);
return v___x_3701_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* v_attrName_3745_, lean_object* v_catName_3746_, lean_object* v_declName_3747_, lean_object* v_stx_3748_, lean_object* v_kind_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_){
_start:
{
uint8_t v_kind_boxed_3753_; lean_object* v_res_3754_; 
v_kind_boxed_3753_ = lean_unbox(v_kind_3749_);
v_res_3754_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3745_, v_catName_3746_, v_declName_3747_, v_stx_3748_, v_kind_boxed_3753_, v_a_3750_, v_a_3751_);
lean_dec(v_a_3751_);
lean_dec_ref(v_a_3750_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object* v_00_u03b1_3755_, lean_object* v_name_3756_, uint8_t v_kind_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3756_, v_kind_3757_, v___y_3758_, v___y_3759_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b1_3762_, lean_object* v_name_3763_, lean_object* v_kind_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
uint8_t v_kind_boxed_3768_; lean_object* v_res_3769_; 
v_kind_boxed_3768_ = lean_unbox(v_kind_3764_);
v_res_3769_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(v_00_u03b1_3762_, v_name_3763_, v_kind_boxed_3768_, v___y_3765_, v___y_3766_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object* v_00_u03b1_3770_, lean_object* v_constName_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3771_, v___y_3772_, v___y_3773_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3776_, lean_object* v_constName_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(v_00_u03b1_3776_, v_constName_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3782_, lean_object* v_ref_3783_, lean_object* v_constName_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3783_, v_constName_3784_, v___y_3785_, v___y_3786_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3789_, lean_object* v_ref_3790_, lean_object* v_constName_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(v_00_u03b1_3789_, v_ref_3790_, v_constName_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v_ref_3790_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3796_, lean_object* v_ref_3797_, lean_object* v_msg_3798_, lean_object* v_declHint_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3797_, v_msg_3798_, v_declHint_3799_, v___y_3800_, v___y_3801_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3804_, lean_object* v_ref_3805_, lean_object* v_msg_3806_, lean_object* v_declHint_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3804_, v_ref_3805_, v_msg_3806_, v_declHint_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v_ref_3805_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_3812_, lean_object* v_declHint_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3812_, v_declHint_3813_, v___y_3815_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_3818_, lean_object* v_declHint_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_3818_, v_declHint_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3824_, lean_object* v_ref_3825_, lean_object* v_msg_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3825_, v_msg_3826_, v___y_3827_, v___y_3828_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3831_, lean_object* v_ref_3832_, lean_object* v_msg_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3831_, v_ref_3832_, v_msg_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v_ref_3832_);
return v_res_3837_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2(void){
_start:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3844_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0));
v___x_3845_ = l_Lean_mkAtom(v___x_3844_);
return v___x_3845_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3846_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2);
v___x_3847_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3848_ = lean_array_push(v___x_3847_, v___x_3846_);
return v___x_3848_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7));
v___x_3858_ = l_Lean_mkAtom(v___x_3857_);
return v___x_3858_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8);
v___x_3860_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3861_ = lean_array_push(v___x_3860_, v___x_3859_);
return v___x_3861_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3862_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9);
v___x_3863_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6));
v___x_3864_ = lean_box(2);
v___x_3865_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
lean_ctor_set(v___x_3865_, 1, v___x_3863_);
lean_ctor_set(v___x_3865_, 2, v___x_3862_);
return v___x_3865_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3866_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10);
v___x_3867_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3);
v___x_3868_ = lean_array_push(v___x_3867_, v___x_3866_);
return v___x_3868_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3869_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11);
v___x_3870_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1));
v___x_3871_ = lean_box(2);
v___x_3872_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3871_);
lean_ctor_set(v___x_3872_, 1, v___x_3870_);
lean_ctor_set(v___x_3872_, 2, v___x_3869_);
return v___x_3872_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3873_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12);
v___x_3874_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3875_ = lean_array_push(v___x_3874_, v___x_3873_);
return v___x_3875_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14(void){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3876_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13);
v___x_3877_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3878_ = lean_box(2);
v___x_3879_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
lean_ctor_set(v___x_3879_, 1, v___x_3877_);
lean_ctor_set(v___x_3879_, 2, v___x_3876_);
return v___x_3879_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14);
v___x_3881_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3882_ = lean_array_push(v___x_3881_, v___x_3880_);
return v___x_3882_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3883_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15);
v___x_3884_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3885_ = lean_box(2);
v___x_3886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
lean_ctor_set(v___x_3886_, 1, v___x_3884_);
lean_ctor_set(v___x_3886_, 2, v___x_3883_);
return v___x_3886_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3887_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16);
v___x_3888_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3889_ = lean_array_push(v___x_3888_, v___x_3887_);
return v___x_3889_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3890_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17);
v___x_3891_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3892_ = lean_box(2);
v___x_3893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
lean_ctor_set(v___x_3893_, 1, v___x_3891_);
lean_ctor_set(v___x_3893_, 2, v___x_3890_);
return v___x_3893_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object* v_attrName_3895_, lean_object* v_decl_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3900_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3901_ = l_Lean_MessageData_ofName(v_attrName_3895_);
v___x_3902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3900_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3902_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
v___x_3905_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3904_, v___y_3897_, v___y_3898_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object* v_attrName_3906_, lean_object* v_decl_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_3906_, v_decl_3907_, v___y_3908_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v_decl_3907_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object* v_attrName_3912_, lean_object* v_catName_3913_, lean_object* v_declName_3914_, lean_object* v_stx_3915_, uint8_t v_kind_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3912_, v_catName_3913_, v_declName_3914_, v_stx_3915_, v_kind_3916_, v___y_3917_, v___y_3918_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object* v_attrName_3921_, lean_object* v_catName_3922_, lean_object* v_declName_3923_, lean_object* v_stx_3924_, lean_object* v_kind_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
uint8_t v_kind_boxed_3929_; lean_object* v_res_3930_; 
v_kind_boxed_3929_ = lean_unbox(v_kind_3925_);
v_res_3930_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_3921_, v_catName_3922_, v_declName_3923_, v_stx_3924_, v_kind_boxed_3929_, v___y_3926_, v___y_3927_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
return v_res_3930_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1(void){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__0));
v___x_3933_ = lean_mk_io_user_error(v___x_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* v_attrName_3936_, lean_object* v_declName_3937_, uint8_t v_behavior_3938_, lean_object* v_ref_3939_){
_start:
{
if (lean_obj_tag(v_declName_3937_) == 1)
{
lean_object* v_pre_3944_; 
v_pre_3944_ = lean_ctor_get(v_declName_3937_, 0);
if (lean_obj_tag(v_pre_3944_) == 1)
{
lean_object* v_pre_3945_; 
v_pre_3945_ = lean_ctor_get(v_pre_3944_, 0);
if (lean_obj_tag(v_pre_3945_) == 1)
{
lean_object* v_pre_3946_; 
v_pre_3946_ = lean_ctor_get(v_pre_3945_, 0);
if (lean_obj_tag(v_pre_3946_) == 1)
{
lean_object* v_pre_3947_; 
v_pre_3947_ = lean_ctor_get(v_pre_3946_, 0);
if (lean_obj_tag(v_pre_3947_) == 0)
{
lean_object* v_str_3948_; lean_object* v_str_3949_; lean_object* v_str_3950_; lean_object* v_str_3951_; lean_object* v___x_3952_; uint8_t v___x_3953_; 
v_str_3948_ = lean_ctor_get(v_declName_3937_, 1);
v_str_3949_ = lean_ctor_get(v_pre_3944_, 1);
v_str_3950_ = lean_ctor_get(v_pre_3945_, 1);
v_str_3951_ = lean_ctor_get(v_pre_3946_, 1);
v___x_3952_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3953_ = lean_string_dec_eq(v_str_3951_, v___x_3952_);
if (v___x_3953_ == 0)
{
lean_dec_ref_known(v_declName_3937_, 2);
lean_dec(v_ref_3939_);
lean_dec(v_attrName_3936_);
goto v___jp_3941_;
}
else
{
lean_object* v___x_3954_; uint8_t v___x_3955_; 
v___x_3954_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3955_ = lean_string_dec_eq(v_str_3950_, v___x_3954_);
if (v___x_3955_ == 0)
{
lean_dec_ref_known(v_declName_3937_, 2);
lean_dec(v_ref_3939_);
lean_dec(v_attrName_3936_);
goto v___jp_3941_;
}
else
{
lean_object* v___x_3956_; uint8_t v___x_3957_; 
v___x_3956_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__2));
v___x_3957_ = lean_string_dec_eq(v_str_3949_, v___x_3956_);
if (v___x_3957_ == 0)
{
lean_dec_ref_known(v_declName_3937_, 2);
lean_dec(v_ref_3939_);
lean_dec(v_attrName_3936_);
goto v___jp_3941_;
}
else
{
lean_object* v___x_3958_; lean_object* v_catName_3959_; lean_object* v___x_3960_; 
v___x_3958_ = lean_box(0);
lean_inc_ref(v_str_3948_);
v_catName_3959_ = l_Lean_Name_str___override(v___x_3958_, v_str_3948_);
lean_inc(v_catName_3959_);
v___x_3960_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_3959_, v_declName_3937_, v_behavior_3938_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v___f_3961_; lean_object* v___f_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
lean_dec_ref_known(v___x_3960_, 1);
lean_inc_n(v_attrName_3936_, 2);
v___f_3961_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3961_, 0, v_attrName_3936_);
v___f_3962_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3962_, 0, v_attrName_3936_);
lean_closure_set(v___f_3962_, 1, v_catName_3959_);
v___x_3963_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__3));
v___x_3964_ = 1;
v___x_3965_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3965_, 0, v_ref_3939_);
lean_ctor_set(v___x_3965_, 1, v_attrName_3936_);
lean_ctor_set(v___x_3965_, 2, v___x_3963_);
lean_ctor_set_uint8(v___x_3965_, sizeof(void*)*3, v___x_3964_);
v___x_3966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
lean_ctor_set(v___x_3966_, 1, v___f_3962_);
lean_ctor_set(v___x_3966_, 2, v___f_3961_);
v___x_3967_ = l_Lean_registerBuiltinAttribute(v___x_3966_);
return v___x_3967_;
}
else
{
lean_dec(v_catName_3959_);
lean_dec(v_ref_3939_);
lean_dec(v_attrName_3936_);
return v___x_3960_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_declName_3937_, 2);
lean_dec(v_ref_3939_);
lean_dec(v_attrName_3936_);
goto v___jp_3941_;
}
}
else
{
lean_dec_ref_known(v_declName_3937_, 2);
lean_dec(v_ref_3939_);
lean_dec(v_attrName_3936_);
goto v___jp_3941_;
}
}
else
{
lean_dec_ref_known(v_declName_3937_, 2);
lean_dec(v_ref_3939_);
lean_dec(v_attrName_3936_);
goto v___jp_3941_;
}
}
else
{
lean_dec_ref_known(v_declName_3937_, 2);
lean_dec(v_ref_3939_);
lean_dec(v_attrName_3936_);
goto v___jp_3941_;
}
}
else
{
lean_dec(v_ref_3939_);
lean_dec(v_declName_3937_);
lean_dec(v_attrName_3936_);
goto v___jp_3941_;
}
v___jp_3941_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3942_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___closed__1, &l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
v___x_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
return v___x_3943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* v_attrName_3968_, lean_object* v_declName_3969_, lean_object* v_behavior_3970_, lean_object* v_ref_3971_, lean_object* v_a_3972_){
_start:
{
uint8_t v_behavior_boxed_3973_; lean_object* v_res_3974_; 
v_behavior_boxed_3973_ = lean_unbox(v_behavior_3970_);
v_res_3974_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_3968_, v_declName_3969_, v_behavior_boxed_3973_, v_ref_3971_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object* v_kind_3975_, lean_object* v_x_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3980_; lean_object* v_env_3981_; lean_object* v_nextMacroScope_3982_; lean_object* v_ngen_3983_; lean_object* v_auxDeclNGen_3984_; lean_object* v_traceState_3985_; lean_object* v_messages_3986_; lean_object* v_infoState_3987_; lean_object* v_snapshotTasks_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_4000_; 
v___x_3980_ = lean_st_ref_take(v___y_3978_);
v_env_3981_ = lean_ctor_get(v___x_3980_, 0);
v_nextMacroScope_3982_ = lean_ctor_get(v___x_3980_, 1);
v_ngen_3983_ = lean_ctor_get(v___x_3980_, 2);
v_auxDeclNGen_3984_ = lean_ctor_get(v___x_3980_, 3);
v_traceState_3985_ = lean_ctor_get(v___x_3980_, 4);
v_messages_3986_ = lean_ctor_get(v___x_3980_, 6);
v_infoState_3987_ = lean_ctor_get(v___x_3980_, 7);
v_snapshotTasks_3988_ = lean_ctor_get(v___x_3980_, 8);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_4000_ == 0)
{
lean_object* v_unused_4001_; 
v_unused_4001_ = lean_ctor_get(v___x_3980_, 5);
lean_dec(v_unused_4001_);
v___x_3990_ = v___x_3980_;
v_isShared_3991_ = v_isSharedCheck_4000_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_snapshotTasks_3988_);
lean_inc(v_infoState_3987_);
lean_inc(v_messages_3986_);
lean_inc(v_traceState_3985_);
lean_inc(v_auxDeclNGen_3984_);
lean_inc(v_ngen_3983_);
lean_inc(v_nextMacroScope_3982_);
lean_inc(v_env_3981_);
lean_dec(v___x_3980_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_4000_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3995_; 
v___x_3992_ = l_Lean_Parser_addSyntaxNodeKind(v_env_3981_, v_kind_3975_);
v___x_3993_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 5, v___x_3993_);
lean_ctor_set(v___x_3990_, 0, v___x_3992_);
v___x_3995_ = v___x_3990_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3992_);
lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_nextMacroScope_3982_);
lean_ctor_set(v_reuseFailAlloc_3999_, 2, v_ngen_3983_);
lean_ctor_set(v_reuseFailAlloc_3999_, 3, v_auxDeclNGen_3984_);
lean_ctor_set(v_reuseFailAlloc_3999_, 4, v_traceState_3985_);
lean_ctor_set(v_reuseFailAlloc_3999_, 5, v___x_3993_);
lean_ctor_set(v_reuseFailAlloc_3999_, 6, v_messages_3986_);
lean_ctor_set(v_reuseFailAlloc_3999_, 7, v_infoState_3987_);
lean_ctor_set(v_reuseFailAlloc_3999_, 8, v_snapshotTasks_3988_);
v___x_3995_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3996_ = lean_st_ref_put(v___y_3978_, v___x_3995_);
v___x_3997_ = lean_box(0);
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
return v___x_3998_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object* v_kind_4002_, lean_object* v_x_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_4002_, v_x_4003_, v___y_4004_, v___y_4005_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_4008_, lean_object* v_keys_4009_, lean_object* v_vals_4010_, lean_object* v_i_4011_, lean_object* v_acc_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v___x_4016_; uint8_t v___x_4017_; 
v___x_4016_ = lean_array_get_size(v_keys_4009_);
v___x_4017_ = lean_nat_dec_lt(v_i_4011_, v___x_4016_);
if (v___x_4017_ == 0)
{
lean_object* v___x_4018_; 
lean_dec(v_i_4011_);
lean_dec_ref(v_f_4008_);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v_acc_4012_);
return v___x_4018_;
}
else
{
lean_object* v_k_4019_; lean_object* v_v_4020_; lean_object* v___x_4021_; 
v_k_4019_ = lean_array_fget_borrowed(v_keys_4009_, v_i_4011_);
v_v_4020_ = lean_array_fget_borrowed(v_vals_4010_, v_i_4011_);
lean_inc_ref(v_f_4008_);
lean_inc(v___y_4014_);
lean_inc_ref(v___y_4013_);
lean_inc(v_v_4020_);
lean_inc(v_k_4019_);
v___x_4021_ = lean_apply_6(v_f_4008_, v_acc_4012_, v_k_4019_, v_v_4020_, v___y_4013_, v___y_4014_, lean_box(0));
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v___x_4021_, 1);
v___x_4023_ = lean_unsigned_to_nat(1u);
v___x_4024_ = lean_nat_add(v_i_4011_, v___x_4023_);
lean_dec(v_i_4011_);
v_i_4011_ = v___x_4024_;
v_acc_4012_ = v_a_4022_;
goto _start;
}
else
{
lean_dec(v_i_4011_);
lean_dec_ref(v_f_4008_);
return v___x_4021_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_4026_, lean_object* v_keys_4027_, lean_object* v_vals_4028_, lean_object* v_i_4029_, lean_object* v_acc_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4026_, v_keys_4027_, v_vals_4028_, v_i_4029_, v_acc_4030_, v___y_4031_, v___y_4032_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec_ref(v_vals_4028_);
lean_dec_ref(v_keys_4027_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_4035_, lean_object* v_as_4036_, size_t v_i_4037_, size_t v_stop_4038_, lean_object* v_b_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v_a_4044_; lean_object* v___y_4049_; uint8_t v___x_4051_; 
v___x_4051_ = lean_usize_dec_eq(v_i_4037_, v_stop_4038_);
if (v___x_4051_ == 0)
{
lean_object* v___x_4052_; 
v___x_4052_ = lean_array_uget_borrowed(v_as_4036_, v_i_4037_);
switch(lean_obj_tag(v___x_4052_))
{
case 0:
{
lean_object* v_key_4053_; lean_object* v_val_4054_; lean_object* v___x_4055_; 
v_key_4053_ = lean_ctor_get(v___x_4052_, 0);
v_val_4054_ = lean_ctor_get(v___x_4052_, 1);
lean_inc_ref(v_f_4035_);
lean_inc(v___y_4041_);
lean_inc_ref(v___y_4040_);
lean_inc(v_val_4054_);
lean_inc(v_key_4053_);
v___x_4055_ = lean_apply_6(v_f_4035_, v_b_4039_, v_key_4053_, v_val_4054_, v___y_4040_, v___y_4041_, lean_box(0));
v___y_4049_ = v___x_4055_;
goto v___jp_4048_;
}
case 1:
{
lean_object* v_node_4056_; lean_object* v___x_4057_; 
v_node_4056_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_node_4056_);
lean_inc_ref(v_f_4035_);
v___x_4057_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4035_, v_node_4056_, v_b_4039_, v___y_4040_, v___y_4041_);
v___y_4049_ = v___x_4057_;
goto v___jp_4048_;
}
default: 
{
v_a_4044_ = v_b_4039_;
goto v___jp_4043_;
}
}
}
else
{
lean_object* v___x_4058_; 
lean_dec_ref(v_f_4035_);
v___x_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4058_, 0, v_b_4039_);
return v___x_4058_;
}
v___jp_4043_:
{
size_t v___x_4045_; size_t v___x_4046_; 
v___x_4045_ = ((size_t)1ULL);
v___x_4046_ = lean_usize_add(v_i_4037_, v___x_4045_);
v_i_4037_ = v___x_4046_;
v_b_4039_ = v_a_4044_;
goto _start;
}
v___jp_4048_:
{
if (lean_obj_tag(v___y_4049_) == 0)
{
lean_object* v_a_4050_; 
v_a_4050_ = lean_ctor_get(v___y_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___y_4049_, 1);
v_a_4044_ = v_a_4050_;
goto v___jp_4043_;
}
else
{
lean_dec_ref(v_f_4035_);
return v___y_4049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object* v_f_4059_, lean_object* v_x_4060_, lean_object* v_x_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
if (lean_obj_tag(v_x_4060_) == 0)
{
lean_object* v_es_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4078_; 
v_es_4065_ = lean_ctor_get(v_x_4060_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v_x_4060_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4067_ = v_x_4060_;
v_isShared_4068_ = v_isSharedCheck_4078_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_es_4065_);
lean_dec(v_x_4060_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4078_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; uint8_t v___x_4071_; 
v___x_4069_ = lean_unsigned_to_nat(0u);
v___x_4070_ = lean_array_get_size(v_es_4065_);
v___x_4071_ = lean_nat_dec_lt(v___x_4069_, v___x_4070_);
if (v___x_4071_ == 0)
{
lean_object* v___x_4073_; 
lean_dec_ref(v_es_4065_);
lean_dec_ref(v_f_4059_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 0, v_x_4061_);
v___x_4073_ = v___x_4067_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_x_4061_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
else
{
size_t v___x_4075_; size_t v___x_4076_; lean_object* v___x_4077_; 
lean_del_object(v___x_4067_);
v___x_4075_ = ((size_t)0ULL);
v___x_4076_ = lean_usize_of_nat(v___x_4070_);
v___x_4077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4059_, v_es_4065_, v___x_4075_, v___x_4076_, v_x_4061_, v___y_4062_, v___y_4063_);
lean_dec_ref(v_es_4065_);
return v___x_4077_;
}
}
}
else
{
lean_object* v_ks_4079_; lean_object* v_vs_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v_ks_4079_ = lean_ctor_get(v_x_4060_, 0);
lean_inc_ref(v_ks_4079_);
v_vs_4080_ = lean_ctor_get(v_x_4060_, 1);
lean_inc_ref(v_vs_4080_);
lean_dec_ref_known(v_x_4060_, 2);
v___x_4081_ = lean_unsigned_to_nat(0u);
v___x_4082_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4059_, v_ks_4079_, v_vs_4080_, v___x_4081_, v_x_4061_, v___y_4062_, v___y_4063_);
lean_dec_ref(v_vs_4080_);
lean_dec_ref(v_ks_4079_);
return v___x_4082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_4083_, lean_object* v_x_4084_, lean_object* v_x_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4083_, v_x_4084_, v_x_4085_, v___y_4086_, v___y_4087_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_4090_, lean_object* v_as_4091_, lean_object* v_i_4092_, lean_object* v_stop_4093_, lean_object* v_b_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
size_t v_i_boxed_4098_; size_t v_stop_boxed_4099_; lean_object* v_res_4100_; 
v_i_boxed_4098_ = lean_unbox_usize(v_i_4092_);
lean_dec(v_i_4092_);
v_stop_boxed_4099_ = lean_unbox_usize(v_stop_4093_);
lean_dec(v_stop_4093_);
v_res_4100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4090_, v_as_4091_, v_i_boxed_4098_, v_stop_boxed_4099_, v_b_4094_, v___y_4095_, v___y_4096_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec_ref(v_as_4091_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object* v_f_4101_, lean_object* v_x_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v___x_4108_; 
lean_inc(v___y_4106_);
lean_inc_ref(v___y_4105_);
v___x_4108_ = lean_apply_5(v_f_4101_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, lean_box(0));
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object* v_f_4109_, lean_object* v_x_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4109_, v_x_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object* v_map_4117_, lean_object* v_f_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v___f_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___f_4122_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4122_, 0, v_f_4118_);
v___x_4123_ = lean_box(0);
v___x_4124_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v___f_4122_, v_map_4117_, v___x_4123_, v___y_4119_, v___y_4120_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object* v_map_4125_, lean_object* v_f_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4125_, v_f_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
return v_res_4130_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0));
v___x_4133_ = l_Lean_stringToMessageData(v___x_4132_);
return v___x_4133_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_4135_ = l_Lean_stringToMessageData(v___x_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t v_attrKind_4136_, lean_object* v_declName_4137_, lean_object* v_as_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
if (lean_obj_tag(v_as_4138_) == 0)
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
lean_dec(v_declName_4137_);
v___x_4142_ = lean_box(0);
v___x_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
return v___x_4143_;
}
else
{
lean_object* v_head_4144_; lean_object* v_tail_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4175_; 
v_head_4144_ = lean_ctor_get(v_as_4138_, 0);
v_tail_4145_ = lean_ctor_get(v_as_4138_, 1);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_as_4138_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4147_ = v_as_4138_;
v_isShared_4148_ = v_isSharedCheck_4175_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_tail_4145_);
lean_inc(v_head_4144_);
lean_dec(v_as_4138_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4175_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___y_4150_; lean_object* v___x_4152_; 
v___x_4152_ = l_Lean_Parser_addToken(v_head_4144_, v_attrKind_4136_, v___y_4139_, v___y_4140_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_del_object(v___x_4147_);
v___y_4150_ = v___x_4152_;
goto v___jp_4149_;
}
else
{
lean_object* v_a_4153_; uint8_t v___y_4155_; uint8_t v___x_4173_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
v___x_4173_ = l_Lean_Exception_isInterrupt(v_a_4153_);
if (v___x_4173_ == 0)
{
uint8_t v___x_4174_; 
lean_inc(v_a_4153_);
v___x_4174_ = l_Lean_Exception_isRuntime(v_a_4153_);
v___y_4155_ = v___x_4174_;
goto v___jp_4154_;
}
else
{
v___y_4155_ = v___x_4173_;
goto v___jp_4154_;
}
v___jp_4154_:
{
if (v___y_4155_ == 0)
{
if (lean_obj_tag(v_a_4153_) == 0)
{
lean_object* v_msg_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4171_; 
lean_dec_ref_known(v___x_4152_, 1);
v_msg_4156_ = lean_ctor_get(v_a_4153_, 1);
v_isSharedCheck_4171_ = !lean_is_exclusive(v_a_4153_);
if (v_isSharedCheck_4171_ == 0)
{
lean_object* v_unused_4172_; 
v_unused_4172_ = lean_ctor_get(v_a_4153_, 0);
lean_dec(v_unused_4172_);
v___x_4158_ = v_a_4153_;
v_isShared_4159_ = v_isSharedCheck_4171_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_msg_4156_);
lean_dec(v_a_4153_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4171_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4163_; 
v___x_4160_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1);
lean_inc(v_declName_4137_);
v___x_4161_ = l_Lean_MessageData_ofConstName(v_declName_4137_, v___y_4155_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set_tag(v___x_4158_, 7);
lean_ctor_set(v___x_4158_, 1, v___x_4161_);
lean_ctor_set(v___x_4158_, 0, v___x_4160_);
v___x_4163_ = v___x_4158_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4160_);
lean_ctor_set(v_reuseFailAlloc_4170_, 1, v___x_4161_);
v___x_4163_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
lean_object* v___x_4164_; lean_object* v___x_4166_; 
v___x_4164_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2);
if (v_isShared_4148_ == 0)
{
lean_ctor_set_tag(v___x_4147_, 7);
lean_ctor_set(v___x_4147_, 1, v___x_4164_);
lean_ctor_set(v___x_4147_, 0, v___x_4163_);
v___x_4166_ = v___x_4147_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4163_);
lean_ctor_set(v_reuseFailAlloc_4169_, 1, v___x_4164_);
v___x_4166_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
lean_ctor_set(v___x_4167_, 1, v_msg_4156_);
v___x_4168_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4167_, v___y_4139_, v___y_4140_);
v___y_4150_ = v___x_4168_;
goto v___jp_4149_;
}
}
}
}
else
{
lean_dec(v_a_4153_);
lean_del_object(v___x_4147_);
v___y_4150_ = v___x_4152_;
goto v___jp_4149_;
}
}
else
{
lean_dec(v_a_4153_);
lean_del_object(v___x_4147_);
v___y_4150_ = v___x_4152_;
goto v___jp_4149_;
}
}
}
v___jp_4149_:
{
if (lean_obj_tag(v___y_4150_) == 0)
{
lean_dec_ref_known(v___y_4150_, 1);
v_as_4138_ = v_tail_4145_;
goto _start;
}
else
{
lean_dec(v_tail_4145_);
lean_dec(v_declName_4137_);
return v___y_4150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object* v_attrKind_4176_, lean_object* v_declName_4177_, lean_object* v_as_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
uint8_t v_attrKind_boxed_4182_; lean_object* v_res_4183_; 
v_attrKind_boxed_4182_ = lean_unbox(v_attrKind_4176_);
v_res_4183_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_boxed_4182_, v_declName_4177_, v_as_4178_, v___y_4179_, v___y_4180_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object* v_catName_4185_, lean_object* v_declName_4186_, lean_object* v_stx_4187_, uint8_t v_attrKind_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_){
_start:
{
lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___x_4197_; 
v___x_4197_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4187_, v_a_4189_, v_a_4190_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v_env_4201_; lean_object* v___x_4202_; lean_object* v_ext_4203_; lean_object* v_toEnvExtension_4204_; lean_object* v_asyncMode_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v_categories_4208_; lean_object* v_env_4209_; lean_object* v_options_4210_; lean_object* v_ref_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref_known(v___x_4197_, 1);
v___x_4199_ = lean_st_ref_get(v_a_4190_);
v___x_4200_ = lean_st_ref_get(v_a_4190_);
v_env_4201_ = lean_ctor_get(v___x_4199_, 0);
lean_inc_ref(v_env_4201_);
lean_dec(v___x_4199_);
v___x_4202_ = l_Lean_Parser_parserExtension;
v_ext_4203_ = lean_ctor_get(v___x_4202_, 1);
v_toEnvExtension_4204_ = lean_ctor_get(v_ext_4203_, 0);
v_asyncMode_4205_ = lean_ctor_get(v_toEnvExtension_4204_, 2);
v___x_4206_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4207_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4206_, v___x_4202_, v_env_4201_, v_asyncMode_4205_);
v_categories_4208_ = lean_ctor_get(v___x_4207_, 2);
lean_inc_ref_n(v_categories_4208_, 2);
lean_dec(v___x_4207_);
v_env_4209_ = lean_ctor_get(v___x_4200_, 0);
lean_inc_ref(v_env_4209_);
lean_dec(v___x_4200_);
v_options_4210_ = lean_ctor_get(v_a_4189_, 2);
v_ref_4211_ = lean_ctor_get(v_a_4189_, 5);
lean_inc_ref(v_options_4210_);
v___x_4212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4212_, 0, v_env_4209_);
lean_ctor_set(v___x_4212_, 1, v_options_4210_);
lean_inc(v_declName_4186_);
v___x_4213_ = l_Lean_Parser_mkParserOfConstant(v_categories_4208_, v_declName_4186_, v___x_4212_);
lean_dec_ref_known(v___x_4212_, 2);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v_a_4214_; lean_object* v_snd_4215_; lean_object* v_info_4216_; lean_object* v_fst_4217_; lean_object* v_collectTokens_4218_; lean_object* v_collectKinds_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_a_4214_);
lean_dec_ref_known(v___x_4213_, 1);
v_snd_4215_ = lean_ctor_get(v_a_4214_, 1);
lean_inc(v_snd_4215_);
v_info_4216_ = lean_ctor_get(v_snd_4215_, 0);
v_fst_4217_ = lean_ctor_get(v_a_4214_, 0);
lean_inc(v_fst_4217_);
lean_dec(v_a_4214_);
v_collectTokens_4218_ = lean_ctor_get(v_info_4216_, 0);
v_collectKinds_4219_ = lean_ctor_get(v_info_4216_, 1);
v___x_4220_ = lean_box(0);
lean_inc_ref(v_collectTokens_4218_);
v___x_4221_ = lean_apply_1(v_collectTokens_4218_, v___x_4220_);
lean_inc(v_declName_4186_);
v___x_4222_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4188_, v_declName_4186_, v___x_4221_, v_a_4189_, v_a_4190_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v___f_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
lean_dec_ref_known(v___x_4222_, 1);
v___f_4223_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0));
v___x_4224_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
lean_inc_ref(v_collectKinds_4219_);
v___x_4225_ = lean_apply_1(v_collectKinds_4219_, v___x_4224_);
v___x_4226_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v___x_4225_, v___f_4223_, v_a_4189_, v_a_4190_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v___x_4227_; uint8_t v___x_4228_; uint8_t v___x_4229_; lean_object* v___x_4230_; 
lean_dec_ref_known(v___x_4226_, 1);
lean_inc(v_a_4198_);
lean_inc(v_snd_4215_);
lean_inc_n(v_declName_4186_, 2);
lean_inc_n(v_catName_4185_, 2);
v___x_4227_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_4227_, 0, v_catName_4185_);
lean_ctor_set(v___x_4227_, 1, v_declName_4186_);
lean_ctor_set(v___x_4227_, 2, v_snd_4215_);
lean_ctor_set(v___x_4227_, 3, v_a_4198_);
v___x_4228_ = lean_unbox(v_fst_4217_);
lean_ctor_set_uint8(v___x_4227_, sizeof(void*)*4, v___x_4228_);
v___x_4229_ = lean_unbox(v_fst_4217_);
lean_dec(v_fst_4217_);
v___x_4230_ = l_Lean_Parser_addParser(v_categories_4208_, v_catName_4185_, v_declName_4186_, v___x_4229_, v_snd_4215_, v_a_4198_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4240_; 
lean_dec_ref_known(v___x_4227_, 4);
lean_dec(v_declName_4186_);
lean_dec(v_catName_4185_);
v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4233_ = v___x_4230_;
v_isShared_4234_ = v_isSharedCheck_4240_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4230_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4240_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
lean_ctor_set_tag(v___x_4233_, 3);
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = l_Lean_MessageData_ofFormat(v___x_4236_);
v___x_4238_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4237_, v_a_4189_, v_a_4190_);
return v___x_4238_;
}
}
}
else
{
lean_object* v___x_4241_; 
lean_dec_ref_known(v___x_4230_, 1);
v___x_4241_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_4202_, v___x_4227_, v_attrKind_4188_, v_a_4189_, v_a_4190_);
lean_dec_ref(v___x_4241_);
v___y_4193_ = v_a_4189_;
v___y_4194_ = v_a_4190_;
goto v___jp_4192_;
}
}
else
{
lean_dec(v_fst_4217_);
lean_dec(v_snd_4215_);
lean_dec_ref(v_categories_4208_);
lean_dec(v_a_4198_);
lean_dec(v_declName_4186_);
lean_dec(v_catName_4185_);
return v___x_4226_;
}
}
else
{
lean_dec(v_fst_4217_);
lean_dec(v_snd_4215_);
lean_dec_ref(v_categories_4208_);
lean_dec(v_a_4198_);
lean_dec(v_declName_4186_);
lean_dec(v_catName_4185_);
return v___x_4222_;
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4253_; 
lean_dec_ref(v_categories_4208_);
lean_dec(v_a_4198_);
lean_dec(v_declName_4186_);
lean_dec(v_catName_4185_);
v_a_4242_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4244_ = v___x_4213_;
v_isShared_4245_ = v_isSharedCheck_4253_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4213_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4253_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4251_; 
v___x_4246_ = lean_io_error_to_string(v_a_4242_);
v___x_4247_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4246_);
v___x_4248_ = l_Lean_MessageData_ofFormat(v___x_4247_);
lean_inc(v_ref_4211_);
v___x_4249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4249_, 0, v_ref_4211_);
lean_ctor_set(v___x_4249_, 1, v___x_4248_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4249_);
v___x_4251_ = v___x_4244_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4249_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_dec(v_declName_4186_);
lean_dec(v_catName_4185_);
v_a_4254_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4197_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4197_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
v___jp_4192_:
{
uint8_t v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = 0;
v___x_4196_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4185_, v_declName_4186_, v___x_4195_, v___y_4193_, v___y_4194_);
return v___x_4196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object* v_catName_4262_, lean_object* v_declName_4263_, lean_object* v_stx_4264_, lean_object* v_attrKind_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_){
_start:
{
uint8_t v_attrKind_boxed_4269_; lean_object* v_res_4270_; 
v_attrKind_boxed_4269_ = lean_unbox(v_attrKind_4265_);
v_res_4270_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4262_, v_declName_4263_, v_stx_4264_, v_attrKind_boxed_4269_, v_a_4266_, v_a_4267_);
lean_dec(v_a_4267_);
lean_dec_ref(v_a_4266_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* v___attrName_4271_, lean_object* v_catName_4272_, lean_object* v_declName_4273_, lean_object* v_stx_4274_, uint8_t v_attrKind_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_){
_start:
{
lean_object* v___x_4279_; 
v___x_4279_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4272_, v_declName_4273_, v_stx_4274_, v_attrKind_4275_, v_a_4276_, v_a_4277_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* v___attrName_4280_, lean_object* v_catName_4281_, lean_object* v_declName_4282_, lean_object* v_stx_4283_, lean_object* v_attrKind_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_){
_start:
{
uint8_t v_attrKind_boxed_4288_; lean_object* v_res_4289_; 
v_attrKind_boxed_4288_ = lean_unbox(v_attrKind_4284_);
v_res_4289_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4280_, v_catName_4281_, v_declName_4282_, v_stx_4283_, v_attrKind_boxed_4288_, v_a_4285_, v_a_4286_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
lean_dec(v___attrName_4280_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object* v_00_u03b2_4290_, lean_object* v_map_4291_, lean_object* v_f_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
lean_object* v___x_4296_; 
v___x_4296_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4291_, v_f_4292_, v___y_4293_, v___y_4294_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b2_4297_, lean_object* v_map_4298_, lean_object* v_f_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(v_00_u03b2_4297_, v_map_4298_, v_f_4299_, v___y_4300_, v___y_4301_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object* v_map_4304_, lean_object* v_f_4305_, lean_object* v_init_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4305_, v_map_4304_, v_init_4306_, v___y_4307_, v___y_4308_);
return v___x_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object* v_map_4311_, lean_object* v_f_4312_, lean_object* v_init_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4311_, v_f_4312_, v_init_4313_, v___y_4314_, v___y_4315_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object* v_00_u03c3_4318_, lean_object* v_00_u03b2_4319_, lean_object* v_map_4320_, lean_object* v_f_4321_, lean_object* v_init_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4321_, v_map_4320_, v_init_4322_, v___y_4323_, v___y_4324_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object* v_00_u03c3_4327_, lean_object* v_00_u03b2_4328_, lean_object* v_map_4329_, lean_object* v_f_4330_, lean_object* v_init_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(v_00_u03c3_4327_, v_00_u03b2_4328_, v_map_4329_, v_f_4330_, v_init_4331_, v___y_4332_, v___y_4333_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_4336_, lean_object* v_00_u03b1_4337_, lean_object* v_00_u03b2_4338_, lean_object* v_f_4339_, lean_object* v_x_4340_, lean_object* v_x_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
lean_object* v___x_4345_; 
v___x_4345_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4339_, v_x_4340_, v_x_4341_, v___y_4342_, v___y_4343_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03c3_4346_, lean_object* v_00_u03b1_4347_, lean_object* v_00_u03b2_4348_, lean_object* v_f_4349_, lean_object* v_x_4350_, lean_object* v_x_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(v_00_u03c3_4346_, v_00_u03b1_4347_, v_00_u03b2_4348_, v_f_4349_, v_x_4350_, v_x_4351_, v___y_4352_, v___y_4353_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4356_, lean_object* v_00_u03b2_4357_, lean_object* v_00_u03c3_4358_, lean_object* v_f_4359_, lean_object* v_as_4360_, size_t v_i_4361_, size_t v_stop_4362_, lean_object* v_b_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4359_, v_as_4360_, v_i_4361_, v_stop_4362_, v_b_4363_, v___y_4364_, v___y_4365_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4368_, lean_object* v_00_u03b2_4369_, lean_object* v_00_u03c3_4370_, lean_object* v_f_4371_, lean_object* v_as_4372_, lean_object* v_i_4373_, lean_object* v_stop_4374_, lean_object* v_b_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
size_t v_i_boxed_4379_; size_t v_stop_boxed_4380_; lean_object* v_res_4381_; 
v_i_boxed_4379_ = lean_unbox_usize(v_i_4373_);
lean_dec(v_i_4373_);
v_stop_boxed_4380_ = lean_unbox_usize(v_stop_4374_);
lean_dec(v_stop_4374_);
v_res_4381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4368_, v_00_u03b2_4369_, v_00_u03c3_4370_, v_f_4371_, v_as_4372_, v_i_boxed_4379_, v_stop_boxed_4380_, v_b_4375_, v___y_4376_, v___y_4377_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec_ref(v_as_4372_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_4382_, lean_object* v_00_u03b1_4383_, lean_object* v_00_u03b2_4384_, lean_object* v_f_4385_, lean_object* v_keys_4386_, lean_object* v_vals_4387_, lean_object* v_heq_4388_, lean_object* v_i_4389_, lean_object* v_acc_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4385_, v_keys_4386_, v_vals_4387_, v_i_4389_, v_acc_4390_, v___y_4391_, v___y_4392_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_4395_, lean_object* v_00_u03b1_4396_, lean_object* v_00_u03b2_4397_, lean_object* v_f_4398_, lean_object* v_keys_4399_, lean_object* v_vals_4400_, lean_object* v_heq_4401_, lean_object* v_i_4402_, lean_object* v_acc_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4395_, v_00_u03b1_4396_, v_00_u03b2_4397_, v_f_4398_, v_keys_4399_, v_vals_4400_, v_heq_4401_, v_i_4402_, v_acc_4403_, v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec_ref(v_vals_4400_);
lean_dec_ref(v_keys_4399_);
return v_res_4407_;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___auto__1(void){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object* v_catName_4409_, lean_object* v_declName_4410_, lean_object* v_stx_4411_, uint8_t v_attrKind_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4409_, v_declName_4410_, v_stx_4411_, v_attrKind_4412_, v___y_4413_, v___y_4414_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object* v_catName_4417_, lean_object* v_declName_4418_, lean_object* v_stx_4419_, lean_object* v_attrKind_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
uint8_t v_attrKind_boxed_4424_; lean_object* v_res_4425_; 
v_attrKind_boxed_4424_ = lean_unbox(v_attrKind_4420_);
v_res_4425_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4417_, v_declName_4418_, v_stx_4419_, v_attrKind_boxed_4424_, v___y_4421_, v___y_4422_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* v_attrName_4427_, lean_object* v_catName_4428_, lean_object* v_ref_4429_){
_start:
{
lean_object* v___f_4430_; lean_object* v___f_4431_; lean_object* v___x_4432_; uint8_t v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___f_4430_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4430_, 0, v_catName_4428_);
lean_inc(v_attrName_4427_);
v___f_4431_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4431_, 0, v_attrName_4427_);
v___x_4432_ = ((lean_object*)(l_Lean_Parser_mkParserAttributeImpl___closed__0));
v___x_4433_ = 1;
v___x_4434_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4434_, 0, v_ref_4429_);
lean_ctor_set(v___x_4434_, 1, v_attrName_4427_);
lean_ctor_set(v___x_4434_, 2, v___x_4432_);
lean_ctor_set_uint8(v___x_4434_, sizeof(void*)*3, v___x_4433_);
v___x_4435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
lean_ctor_set(v___x_4435_, 1, v___f_4430_);
lean_ctor_set(v___x_4435_, 2, v___f_4431_);
return v___x_4435_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* v_attrName_4437_, lean_object* v_catName_4438_, lean_object* v_ref_4439_){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4441_ = l_Lean_Parser_mkParserAttributeImpl(v_attrName_4437_, v_catName_4438_, v_ref_4439_);
v___x_4442_ = l_Lean_registerBuiltinAttribute(v___x_4441_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object* v_attrName_4443_, lean_object* v_catName_4444_, lean_object* v_ref_4445_, lean_object* v_a_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4443_, v_catName_4444_, v_ref_4445_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object* v_ref_4451_, lean_object* v_args_4452_){
_start:
{
if (lean_obj_tag(v_args_4452_) == 1)
{
lean_object* v_head_4455_; 
v_head_4455_ = lean_ctor_get(v_args_4452_, 0);
lean_inc(v_head_4455_);
if (lean_obj_tag(v_head_4455_) == 2)
{
lean_object* v_tail_4456_; 
v_tail_4456_ = lean_ctor_get(v_args_4452_, 1);
lean_inc(v_tail_4456_);
lean_dec_ref_known(v_args_4452_, 2);
if (lean_obj_tag(v_tail_4456_) == 1)
{
lean_object* v_head_4457_; 
v_head_4457_ = lean_ctor_get(v_tail_4456_, 0);
lean_inc(v_head_4457_);
if (lean_obj_tag(v_head_4457_) == 2)
{
lean_object* v_tail_4458_; 
v_tail_4458_ = lean_ctor_get(v_tail_4456_, 1);
lean_inc(v_tail_4458_);
lean_dec_ref_known(v_tail_4456_, 2);
if (lean_obj_tag(v_tail_4458_) == 0)
{
lean_object* v_v_4459_; lean_object* v_v_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4468_; 
v_v_4459_ = lean_ctor_get(v_head_4455_, 0);
lean_inc(v_v_4459_);
lean_dec_ref_known(v_head_4455_, 1);
v_v_4460_ = lean_ctor_get(v_head_4457_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v_head_4457_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4462_ = v_head_4457_;
v_isShared_4463_ = v_isSharedCheck_4468_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_v_4460_);
lean_dec(v_head_4457_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4468_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4464_; lean_object* v___x_4466_; 
v___x_4464_ = l_Lean_Parser_mkParserAttributeImpl(v_v_4459_, v_v_4460_, v_ref_4451_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set_tag(v___x_4462_, 1);
lean_ctor_set(v___x_4462_, 0, v___x_4464_);
v___x_4466_ = v___x_4462_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4464_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
else
{
lean_dec_ref_known(v_head_4457_, 1);
lean_dec(v_tail_4458_);
lean_dec_ref_known(v_head_4455_, 1);
lean_dec(v_ref_4451_);
goto v___jp_4453_;
}
}
else
{
lean_dec(v_head_4457_);
lean_dec_ref_known(v_tail_4456_, 2);
lean_dec_ref_known(v_head_4455_, 1);
lean_dec(v_ref_4451_);
goto v___jp_4453_;
}
}
else
{
lean_dec_ref_known(v_head_4455_, 1);
lean_dec(v_tail_4456_);
lean_dec(v_ref_4451_);
goto v___jp_4453_;
}
}
else
{
lean_dec(v_head_4455_);
lean_dec_ref_known(v_args_4452_, 2);
lean_dec(v_ref_4451_);
goto v___jp_4453_;
}
}
else
{
lean_dec(v_args_4452_);
lean_dec(v_ref_4451_);
goto v___jp_4453_;
}
v___jp_4453_:
{
lean_object* v___x_4454_; 
v___x_4454_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
return v___x_4454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___f_4474_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4475_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4476_ = l_Lean_registerAttributeImplBuilder(v___x_4475_, v___f_4474_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object* v_a_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
return v_res_4478_;
}
}
static lean_object* _init_l_Lean_Parser_registerParserCategory___auto__1(void){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object* v_env_4480_, lean_object* v_attrName_4481_, lean_object* v_catName_4482_, uint8_t v_behavior_4483_, lean_object* v_ref_4484_){
_start:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
lean_inc(v_ref_4484_);
lean_inc(v_catName_4482_);
v___x_4486_ = l_Lean_Parser_addParserCategory(v_env_4480_, v_catName_4482_, v_ref_4484_, v_behavior_4483_);
v___x_4487_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_4486_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4501_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4490_ = v___x_4487_;
v_isShared_4491_ = v_isSharedCheck_4501_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4487_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4501_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4492_; lean_object* v___x_4494_; 
v___x_4492_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
if (v_isShared_4491_ == 0)
{
lean_ctor_set_tag(v___x_4490_, 2);
lean_ctor_set(v___x_4490_, 0, v_attrName_4481_);
v___x_4494_ = v___x_4490_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_attrName_4481_);
v___x_4494_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4495_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4495_, 0, v_catName_4482_);
v___x_4496_ = lean_box(0);
v___x_4497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4495_);
lean_ctor_set(v___x_4497_, 1, v___x_4496_);
v___x_4498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4494_);
lean_ctor_set(v___x_4498_, 1, v___x_4497_);
v___x_4499_ = l_Lean_registerAttributeOfBuilder(v_a_4488_, v___x_4492_, v_ref_4484_, v___x_4498_);
return v___x_4499_;
}
}
}
else
{
lean_dec(v_ref_4484_);
lean_dec(v_catName_4482_);
lean_dec(v_attrName_4481_);
return v___x_4487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* v_env_4502_, lean_object* v_attrName_4503_, lean_object* v_catName_4504_, lean_object* v_behavior_4505_, lean_object* v_ref_4506_, lean_object* v_a_4507_){
_start:
{
uint8_t v_behavior_boxed_4508_; lean_object* v_res_4509_; 
v_behavior_boxed_4508_ = lean_unbox(v_behavior_4505_);
v_res_4509_ = l_Lean_Parser_registerParserCategory(v_env_4502_, v_attrName_4503_, v_catName_4504_, v_behavior_boxed_4508_, v_ref_4506_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4532_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4533_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4534_ = 0;
v___x_4535_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4536_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4532_, v___x_4533_, v___x_4534_, v___x_4535_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object* v_a_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
return v_res_4538_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4544_ = lean_unsigned_to_nat(3431364690u);
v___x_4545_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4546_ = l_Lean_Name_num___override(v___x_4545_, v___x_4544_);
return v___x_4546_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4547_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4548_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4549_ = l_Lean_Name_str___override(v___x_4548_, v___x_4547_);
return v___x_4549_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4550_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4551_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4552_ = l_Lean_Name_str___override(v___x_4551_, v___x_4550_);
return v___x_4552_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4553_ = lean_unsigned_to_nat(2u);
v___x_4554_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4555_ = l_Lean_Name_num___override(v___x_4554_, v___x_4553_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4557_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4558_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4559_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4560_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4557_, v___x_4558_, v___x_4559_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object* v_a_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
return v_res_4562_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4572_ = lean_unsigned_to_nat(2342493449u);
v___x_4573_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4574_ = l_Lean_Name_num___override(v___x_4573_, v___x_4572_);
return v___x_4574_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4575_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4576_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4577_ = l_Lean_Name_str___override(v___x_4576_, v___x_4575_);
return v___x_4577_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4578_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4579_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4580_ = l_Lean_Name_str___override(v___x_4579_, v___x_4578_);
return v___x_4580_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4581_ = lean_unsigned_to_nat(2u);
v___x_4582_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4583_ = l_Lean_Name_num___override(v___x_4582_, v___x_4581_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; uint8_t v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4585_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4586_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4587_ = 0;
v___x_4588_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4589_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4585_, v___x_4586_, v___x_4587_, v___x_4588_);
return v___x_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object* v_a_4590_){
_start:
{
lean_object* v_res_4591_; 
v_res_4591_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
return v_res_4591_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4597_ = lean_unsigned_to_nat(3226070615u);
v___x_4598_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4599_ = l_Lean_Name_num___override(v___x_4598_, v___x_4597_);
return v___x_4599_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4600_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4601_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4602_ = l_Lean_Name_str___override(v___x_4601_, v___x_4600_);
return v___x_4602_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4603_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4604_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4605_ = l_Lean_Name_str___override(v___x_4604_, v___x_4603_);
return v___x_4605_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4606_ = lean_unsigned_to_nat(2u);
v___x_4607_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4608_ = l_Lean_Name_num___override(v___x_4607_, v___x_4606_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___x_4610_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4611_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4612_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4613_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4610_, v___x_4611_, v___x_4612_);
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object* v_a_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* v_rbp_4616_){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4618_ = l_Lean_Parser_categoryParser(v___x_4617_, v_rbp_4616_);
return v___x_4618_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t v_addOpenSimple_4619_, lean_object* v_x_4620_, lean_object* v_x_4621_){
_start:
{
if (lean_obj_tag(v_x_4621_) == 0)
{
return v_x_4620_;
}
else
{
lean_object* v_head_4622_; lean_object* v_tail_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4646_; 
v_head_4622_ = lean_ctor_get(v_x_4621_, 0);
v_tail_4623_ = lean_ctor_get(v_x_4621_, 1);
v_isSharedCheck_4646_ = !lean_is_exclusive(v_x_4621_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4625_ = v_x_4621_;
v_isShared_4626_ = v_isSharedCheck_4646_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_tail_4623_);
lean_inc(v_head_4622_);
lean_dec(v_x_4621_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4646_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v_fst_4627_; lean_object* v_snd_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4645_; 
v_fst_4627_ = lean_ctor_get(v_x_4620_, 0);
v_snd_4628_ = lean_ctor_get(v_x_4620_, 1);
v_isSharedCheck_4645_ = !lean_is_exclusive(v_x_4620_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4630_ = v_x_4620_;
v_isShared_4631_ = v_isSharedCheck_4645_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_snd_4628_);
lean_inc(v_fst_4627_);
lean_dec(v_x_4620_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4645_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___y_4633_; 
if (v_addOpenSimple_4619_ == 0)
{
lean_del_object(v___x_4625_);
v___y_4633_ = v_snd_4628_;
goto v___jp_4632_;
}
else
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4643_; 
v___x_4640_ = lean_box(0);
lean_inc(v_head_4622_);
v___x_4641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4641_, 0, v_head_4622_);
lean_ctor_set(v___x_4641_, 1, v___x_4640_);
if (v_isShared_4626_ == 0)
{
lean_ctor_set(v___x_4625_, 1, v_snd_4628_);
lean_ctor_set(v___x_4625_, 0, v___x_4641_);
v___x_4643_ = v___x_4625_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4641_);
lean_ctor_set(v_reuseFailAlloc_4644_, 1, v_snd_4628_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
v___y_4633_ = v___x_4643_;
goto v___jp_4632_;
}
}
v___jp_4632_:
{
lean_object* v___x_4634_; lean_object* v_env_4635_; lean_object* v___x_4637_; 
v___x_4634_ = l_Lean_Parser_parserExtension;
v_env_4635_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v___x_4634_, v_fst_4627_, v_head_4622_);
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 1, v___y_4633_);
lean_ctor_set(v___x_4630_, 0, v_env_4635_);
v___x_4637_ = v___x_4630_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_env_4635_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v___y_4633_);
v___x_4637_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
v_x_4620_ = v___x_4637_;
v_x_4621_ = v_tail_4623_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object* v_addOpenSimple_4647_, lean_object* v_x_4648_, lean_object* v_x_4649_){
_start:
{
uint8_t v_addOpenSimple_boxed_4650_; lean_object* v_res_4651_; 
v_addOpenSimple_boxed_4650_ = lean_unbox(v_addOpenSimple_4647_);
v_res_4651_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_boxed_4650_, v_x_4648_, v_x_4649_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t v_addOpenSimple_4652_, lean_object* v_as_4653_, size_t v_i_4654_, size_t v_stop_4655_, lean_object* v_b_4656_){
_start:
{
uint8_t v___x_4657_; 
v___x_4657_ = lean_usize_dec_eq(v_i_4654_, v_stop_4655_);
if (v___x_4657_ == 0)
{
lean_object* v_toParserModuleContext_4658_; lean_object* v_toInputContext_4659_; lean_object* v_toCacheableParserContext_4660_; lean_object* v_tokens_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4688_; 
v_toParserModuleContext_4658_ = lean_ctor_get(v_b_4656_, 1);
v_toInputContext_4659_ = lean_ctor_get(v_b_4656_, 0);
v_toCacheableParserContext_4660_ = lean_ctor_get(v_b_4656_, 2);
v_tokens_4661_ = lean_ctor_get(v_b_4656_, 3);
v_isSharedCheck_4688_ = !lean_is_exclusive(v_b_4656_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4663_ = v_b_4656_;
v_isShared_4664_ = v_isSharedCheck_4688_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_tokens_4661_);
lean_inc(v_toCacheableParserContext_4660_);
lean_inc(v_toParserModuleContext_4658_);
lean_inc(v_toInputContext_4659_);
lean_dec(v_b_4656_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4688_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v_env_4665_; lean_object* v_options_4666_; lean_object* v_currNamespace_4667_; lean_object* v_openDecls_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4687_; 
v_env_4665_ = lean_ctor_get(v_toParserModuleContext_4658_, 0);
v_options_4666_ = lean_ctor_get(v_toParserModuleContext_4658_, 1);
v_currNamespace_4667_ = lean_ctor_get(v_toParserModuleContext_4658_, 2);
v_openDecls_4668_ = lean_ctor_get(v_toParserModuleContext_4658_, 3);
v_isSharedCheck_4687_ = !lean_is_exclusive(v_toParserModuleContext_4658_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4670_ = v_toParserModuleContext_4658_;
v_isShared_4671_ = v_isSharedCheck_4687_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_openDecls_4668_);
lean_inc(v_currNamespace_4667_);
lean_inc(v_options_4666_);
lean_inc(v_env_4665_);
lean_dec(v_toParserModuleContext_4658_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4687_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4672_; lean_object* v_nss_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v_fst_4676_; lean_object* v_snd_4677_; lean_object* v___x_4679_; 
v___x_4672_ = lean_array_uget_borrowed(v_as_4653_, v_i_4654_);
lean_inc(v___x_4672_);
lean_inc(v_openDecls_4668_);
lean_inc(v_currNamespace_4667_);
lean_inc_ref(v_env_4665_);
v_nss_4673_ = l_Lean_ResolveName_resolveNamespace(v_env_4665_, v_currNamespace_4667_, v_openDecls_4668_, v___x_4672_);
v___x_4674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4674_, 0, v_env_4665_);
lean_ctor_set(v___x_4674_, 1, v_openDecls_4668_);
v___x_4675_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4652_, v___x_4674_, v_nss_4673_);
v_fst_4676_ = lean_ctor_get(v___x_4675_, 0);
lean_inc(v_fst_4676_);
v_snd_4677_ = lean_ctor_get(v___x_4675_, 1);
lean_inc(v_snd_4677_);
lean_dec_ref(v___x_4675_);
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 3, v_snd_4677_);
lean_ctor_set(v___x_4670_, 0, v_fst_4676_);
v___x_4679_ = v___x_4670_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_fst_4676_);
lean_ctor_set(v_reuseFailAlloc_4686_, 1, v_options_4666_);
lean_ctor_set(v_reuseFailAlloc_4686_, 2, v_currNamespace_4667_);
lean_ctor_set(v_reuseFailAlloc_4686_, 3, v_snd_4677_);
v___x_4679_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
lean_object* v___x_4681_; 
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 1, v___x_4679_);
v___x_4681_ = v___x_4663_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_toInputContext_4659_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v___x_4679_);
lean_ctor_set(v_reuseFailAlloc_4685_, 2, v_toCacheableParserContext_4660_);
lean_ctor_set(v_reuseFailAlloc_4685_, 3, v_tokens_4661_);
v___x_4681_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
size_t v___x_4682_; size_t v___x_4683_; 
v___x_4682_ = ((size_t)1ULL);
v___x_4683_ = lean_usize_add(v_i_4654_, v___x_4682_);
v_i_4654_ = v___x_4683_;
v_b_4656_ = v___x_4681_;
goto _start;
}
}
}
}
}
else
{
return v_b_4656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object* v_addOpenSimple_4689_, lean_object* v_as_4690_, lean_object* v_i_4691_, lean_object* v_stop_4692_, lean_object* v_b_4693_){
_start:
{
uint8_t v_addOpenSimple_boxed_4694_; size_t v_i_boxed_4695_; size_t v_stop_boxed_4696_; lean_object* v_res_4697_; 
v_addOpenSimple_boxed_4694_ = lean_unbox(v_addOpenSimple_4689_);
v_i_boxed_4695_ = lean_unbox_usize(v_i_4691_);
lean_dec(v_i_4691_);
v_stop_boxed_4696_ = lean_unbox_usize(v_stop_4692_);
lean_dec(v_stop_4692_);
v_res_4697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_boxed_4694_, v_as_4690_, v_i_boxed_4695_, v_stop_boxed_4696_, v_b_4693_);
lean_dec_ref(v_as_4690_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object* v___x_4698_, lean_object* v_ids_4699_, uint8_t v_addOpenSimple_4700_, lean_object* v_c_4701_){
_start:
{
lean_object* v___y_4703_; lean_object* v___x_4722_; lean_object* v___x_4723_; uint8_t v___x_4724_; 
v___x_4722_ = lean_unsigned_to_nat(0u);
v___x_4723_ = lean_array_get_size(v_ids_4699_);
v___x_4724_ = lean_nat_dec_lt(v___x_4722_, v___x_4723_);
if (v___x_4724_ == 0)
{
v___y_4703_ = v_c_4701_;
goto v___jp_4702_;
}
else
{
uint8_t v___x_4725_; 
v___x_4725_ = lean_nat_dec_le(v___x_4723_, v___x_4723_);
if (v___x_4725_ == 0)
{
if (v___x_4724_ == 0)
{
v___y_4703_ = v_c_4701_;
goto v___jp_4702_;
}
else
{
size_t v___x_4726_; size_t v___x_4727_; lean_object* v___x_4728_; 
v___x_4726_ = ((size_t)0ULL);
v___x_4727_ = lean_usize_of_nat(v___x_4723_);
v___x_4728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4700_, v_ids_4699_, v___x_4726_, v___x_4727_, v_c_4701_);
v___y_4703_ = v___x_4728_;
goto v___jp_4702_;
}
}
else
{
size_t v___x_4729_; size_t v___x_4730_; lean_object* v___x_4731_; 
v___x_4729_ = ((size_t)0ULL);
v___x_4730_ = lean_usize_of_nat(v___x_4723_);
v___x_4731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4700_, v_ids_4699_, v___x_4729_, v___x_4730_, v_c_4701_);
v___y_4703_ = v___x_4731_;
goto v___jp_4702_;
}
}
v___jp_4702_:
{
lean_object* v_toParserModuleContext_4704_; lean_object* v_toInputContext_4705_; lean_object* v_toCacheableParserContext_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4720_; 
v_toParserModuleContext_4704_ = lean_ctor_get(v___y_4703_, 1);
v_toInputContext_4705_ = lean_ctor_get(v___y_4703_, 0);
v_toCacheableParserContext_4706_ = lean_ctor_get(v___y_4703_, 2);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___y_4703_);
if (v_isSharedCheck_4720_ == 0)
{
lean_object* v_unused_4721_; 
v_unused_4721_ = lean_ctor_get(v___y_4703_, 3);
lean_dec(v_unused_4721_);
v___x_4708_ = v___y_4703_;
v_isShared_4709_ = v_isSharedCheck_4720_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_toCacheableParserContext_4706_);
lean_inc(v_toParserModuleContext_4704_);
lean_inc(v_toInputContext_4705_);
lean_dec(v___y_4703_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4720_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v_env_4710_; lean_object* v___x_4711_; lean_object* v_ext_4712_; lean_object* v_toEnvExtension_4713_; lean_object* v_asyncMode_4714_; lean_object* v___x_4715_; lean_object* v_tokens_4716_; lean_object* v___x_4718_; 
v_env_4710_ = lean_ctor_get(v_toParserModuleContext_4704_, 0);
v___x_4711_ = l_Lean_Parser_parserExtension;
v_ext_4712_ = lean_ctor_get(v___x_4711_, 1);
v_toEnvExtension_4713_ = lean_ctor_get(v_ext_4712_, 0);
v_asyncMode_4714_ = lean_ctor_get(v_toEnvExtension_4713_, 2);
lean_inc_ref(v_env_4710_);
v___x_4715_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4698_, v___x_4711_, v_env_4710_, v_asyncMode_4714_);
v_tokens_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc_ref(v_tokens_4716_);
lean_dec(v___x_4715_);
if (v_isShared_4709_ == 0)
{
lean_ctor_set(v___x_4708_, 3, v_tokens_4716_);
v___x_4718_ = v___x_4708_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_toInputContext_4705_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v_toParserModuleContext_4704_);
lean_ctor_set(v_reuseFailAlloc_4719_, 2, v_toCacheableParserContext_4706_);
lean_ctor_set(v_reuseFailAlloc_4719_, 3, v_tokens_4716_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object* v___x_4732_, lean_object* v_ids_4733_, lean_object* v_addOpenSimple_4734_, lean_object* v_c_4735_){
_start:
{
uint8_t v_addOpenSimple_boxed_4736_; lean_object* v_res_4737_; 
v_addOpenSimple_boxed_4736_ = lean_unbox(v_addOpenSimple_4734_);
v_res_4737_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_4732_, v_ids_4733_, v_addOpenSimple_boxed_4736_, v_c_4735_);
lean_dec_ref(v_ids_4733_);
lean_dec_ref(v___x_4732_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* v_ids_4738_, uint8_t v_addOpenSimple_4739_, lean_object* v_p_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_){
_start:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___f_4745_; lean_object* v___x_4746_; 
v___x_4743_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4744_ = lean_box(v_addOpenSimple_4739_);
v___f_4745_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4745_, 0, v___x_4743_);
lean_closure_set(v___f_4745_, 1, v_ids_4738_);
lean_closure_set(v___f_4745_, 2, v___x_4744_);
v___x_4746_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_4745_, v_p_4740_, v_a_4741_, v_a_4742_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* v_ids_4747_, lean_object* v_addOpenSimple_4748_, lean_object* v_p_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_){
_start:
{
uint8_t v_addOpenSimple_boxed_4752_; lean_object* v_res_4753_; 
v_addOpenSimple_boxed_4752_ = lean_unbox(v_addOpenSimple_4748_);
v_res_4753_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_4747_, v_addOpenSimple_boxed_4752_, v_p_4749_, v_a_4750_, v_a_4751_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t v_sz_4754_, size_t v_i_4755_, lean_object* v_bs_4756_){
_start:
{
uint8_t v___x_4757_; 
v___x_4757_ = lean_usize_dec_lt(v_i_4755_, v_sz_4754_);
if (v___x_4757_ == 0)
{
return v_bs_4756_;
}
else
{
lean_object* v_v_4758_; lean_object* v___x_4759_; lean_object* v_bs_x27_4760_; lean_object* v___x_4761_; size_t v___x_4762_; size_t v___x_4763_; lean_object* v___x_4764_; 
v_v_4758_ = lean_array_uget(v_bs_4756_, v_i_4755_);
v___x_4759_ = lean_unsigned_to_nat(0u);
v_bs_x27_4760_ = lean_array_uset(v_bs_4756_, v_i_4755_, v___x_4759_);
v___x_4761_ = l_Lean_Syntax_getId(v_v_4758_);
lean_dec(v_v_4758_);
v___x_4762_ = ((size_t)1ULL);
v___x_4763_ = lean_usize_add(v_i_4755_, v___x_4762_);
v___x_4764_ = lean_array_uset(v_bs_x27_4760_, v_i_4755_, v___x_4761_);
v_i_4755_ = v___x_4763_;
v_bs_4756_ = v___x_4764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object* v_sz_4766_, lean_object* v_i_4767_, lean_object* v_bs_4768_){
_start:
{
size_t v_sz_boxed_4769_; size_t v_i_boxed_4770_; lean_object* v_res_4771_; 
v_sz_boxed_4769_ = lean_unbox_usize(v_sz_4766_);
lean_dec(v_sz_4766_);
v_i_boxed_4770_ = lean_unbox_usize(v_i_4767_);
lean_dec(v_i_4767_);
v_res_4771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_boxed_4769_, v_i_boxed_4770_, v_bs_4768_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* v_openDeclStx_4785_, lean_object* v_p_4786_, lean_object* v_c_4787_, lean_object* v_s_4788_){
_start:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; uint8_t v___x_4791_; 
lean_inc(v_openDeclStx_4785_);
v___x_4789_ = l_Lean_Syntax_getKind(v_openDeclStx_4785_);
v___x_4790_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__2));
v___x_4791_ = lean_name_eq(v___x_4789_, v___x_4790_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4792_; uint8_t v___x_4793_; 
v___x_4792_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__4));
v___x_4793_ = lean_name_eq(v___x_4789_, v___x_4792_);
lean_dec(v___x_4789_);
if (v___x_4793_ == 0)
{
lean_object* v___x_4794_; 
lean_dec(v_openDeclStx_4785_);
v___x_4794_ = lean_apply_2(v_p_4786_, v_c_4787_, v_s_4788_);
return v___x_4794_;
}
else
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; size_t v_sz_4798_; size_t v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4795_ = lean_unsigned_to_nat(1u);
v___x_4796_ = l_Lean_Syntax_getArg(v_openDeclStx_4785_, v___x_4795_);
lean_dec(v_openDeclStx_4785_);
v___x_4797_ = l_Lean_Syntax_getArgs(v___x_4796_);
lean_dec(v___x_4796_);
v_sz_4798_ = lean_array_size(v___x_4797_);
v___x_4799_ = ((size_t)0ULL);
v___x_4800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4798_, v___x_4799_, v___x_4797_);
v___x_4801_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4800_, v___x_4791_, v_p_4786_, v_c_4787_, v_s_4788_);
return v___x_4801_;
}
}
else
{
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; size_t v_sz_4805_; size_t v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; 
lean_dec(v___x_4789_);
v___x_4802_ = lean_unsigned_to_nat(0u);
v___x_4803_ = l_Lean_Syntax_getArg(v_openDeclStx_4785_, v___x_4802_);
lean_dec(v_openDeclStx_4785_);
v___x_4804_ = l_Lean_Syntax_getArgs(v___x_4803_);
lean_dec(v___x_4803_);
v_sz_4805_ = lean_array_size(v___x_4804_);
v___x_4806_ = ((size_t)0ULL);
v___x_4807_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4805_, v___x_4806_, v___x_4804_);
v___x_4808_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4807_, v___x_4791_, v_p_4786_, v_c_4787_, v_s_4788_);
return v___x_4808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* v_p_4815_, lean_object* v_c_4816_, lean_object* v_s_4817_){
_start:
{
lean_object* v_stxStack_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; uint8_t v___x_4821_; 
v_stxStack_4818_ = lean_ctor_get(v_s_4817_, 0);
v___x_4819_ = lean_unsigned_to_nat(0u);
v___x_4820_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4818_);
v___x_4821_ = lean_nat_dec_lt(v___x_4819_, v___x_4820_);
lean_dec(v___x_4820_);
if (v___x_4821_ == 0)
{
lean_object* v___x_4822_; 
v___x_4822_ = lean_apply_2(v_p_4815_, v_c_4816_, v_s_4817_);
return v___x_4822_;
}
else
{
lean_object* v_stx_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; uint8_t v___x_4826_; 
v_stx_4823_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4818_);
lean_inc(v_stx_4823_);
v___x_4824_ = l_Lean_Syntax_getKind(v_stx_4823_);
v___x_4825_ = ((lean_object*)(l_Lean_Parser_withOpenFn___closed__1));
v___x_4826_ = lean_name_eq(v___x_4824_, v___x_4825_);
lean_dec(v___x_4824_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4827_; 
lean_dec(v_stx_4823_);
v___x_4827_ = lean_apply_2(v_p_4815_, v_c_4816_, v_s_4817_);
return v___x_4827_;
}
else
{
lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4828_ = lean_unsigned_to_nat(1u);
v___x_4829_ = l_Lean_Syntax_getArg(v_stx_4823_, v___x_4828_);
lean_dec(v_stx_4823_);
v___x_4830_ = l_Lean_Parser_withOpenDeclFnCore(v___x_4829_, v_p_4815_, v_c_4816_, v_s_4817_);
return v___x_4830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* v_p_4831_){
_start:
{
lean_object* v_info_4832_; lean_object* v_fn_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4841_; 
v_info_4832_ = lean_ctor_get(v_p_4831_, 0);
v_fn_4833_ = lean_ctor_get(v_p_4831_, 1);
v_isSharedCheck_4841_ = !lean_is_exclusive(v_p_4831_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4835_ = v_p_4831_;
v_isShared_4836_ = v_isSharedCheck_4841_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_fn_4833_);
lean_inc(v_info_4832_);
lean_dec(v_p_4831_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4841_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4837_; lean_object* v___x_4839_; 
v___x_4837_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(v___x_4837_, 0, v_fn_4833_);
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 1, v___x_4837_);
v___x_4839_ = v___x_4835_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_info_4832_);
lean_ctor_set(v_reuseFailAlloc_4840_, 1, v___x_4837_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* v_p_4842_, lean_object* v_c_4843_, lean_object* v_s_4844_){
_start:
{
lean_object* v_stxStack_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; uint8_t v___x_4848_; 
v_stxStack_4845_ = lean_ctor_get(v_s_4844_, 0);
v___x_4846_ = lean_unsigned_to_nat(0u);
v___x_4847_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4845_);
v___x_4848_ = lean_nat_dec_lt(v___x_4846_, v___x_4847_);
lean_dec(v___x_4847_);
if (v___x_4848_ == 0)
{
lean_object* v___x_4849_; 
v___x_4849_ = lean_apply_2(v_p_4842_, v_c_4843_, v_s_4844_);
return v___x_4849_;
}
else
{
lean_object* v_stx_4850_; lean_object* v___x_4851_; 
v_stx_4850_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4845_);
v___x_4851_ = l_Lean_Parser_withOpenDeclFnCore(v_stx_4850_, v_p_4842_, v_c_4843_, v_s_4844_);
return v___x_4851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* v_p_4852_){
_start:
{
lean_object* v_info_4853_; lean_object* v_fn_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4862_; 
v_info_4853_ = lean_ctor_get(v_p_4852_, 0);
v_fn_4854_ = lean_ctor_get(v_p_4852_, 1);
v_isSharedCheck_4862_ = !lean_is_exclusive(v_p_4852_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4856_ = v_p_4852_;
v_isShared_4857_ = v_isSharedCheck_4862_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_fn_4854_);
lean_inc(v_info_4853_);
lean_dec(v_p_4852_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4862_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4858_; lean_object* v___x_4860_; 
v___x_4858_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(v___x_4858_, 0, v_fn_4854_);
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 1, v___x_4858_);
v___x_4860_ = v___x_4856_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_info_4853_);
lean_ctor_set(v_reuseFailAlloc_4861_, 1, v___x_4858_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object* v_val_4869_){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = l_Lean_Syntax_isStrLit_x3f(v_val_4869_);
if (lean_obj_tag(v___x_4877_) == 1)
{
lean_object* v_val_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4886_; 
v_val_4878_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4880_ = v___x_4877_;
v_isShared_4881_ = v_isSharedCheck_4886_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_val_4878_);
lean_dec(v___x_4877_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4886_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4882_; lean_object* v___x_4884_; 
v___x_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4882_, 0, v_val_4878_);
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 0, v___x_4882_);
v___x_4884_ = v___x_4880_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v___x_4882_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
else
{
lean_object* v___x_4887_; 
lean_dec(v___x_4877_);
v___x_4887_ = l_Lean_Syntax_isNatLit_x3f(v_val_4869_);
if (lean_obj_tag(v___x_4887_) == 1)
{
lean_object* v_val_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4896_; 
v_val_4888_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4890_ = v___x_4887_;
v_isShared_4891_ = v_isSharedCheck_4896_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_val_4888_);
lean_dec(v___x_4887_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4896_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4892_; lean_object* v___x_4894_; 
v___x_4892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4892_, 0, v_val_4888_);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 0, v___x_4892_);
v___x_4894_ = v___x_4890_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4892_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
else
{
lean_dec(v___x_4887_);
if (lean_obj_tag(v_val_4869_) == 2)
{
lean_object* v_val_4897_; lean_object* v___x_4898_; uint8_t v___x_4899_; 
v_val_4897_ = lean_ctor_get(v_val_4869_, 1);
v___x_4898_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3));
v___x_4899_ = lean_string_dec_eq(v_val_4897_, v___x_4898_);
if (v___x_4899_ == 0)
{
goto v___jp_4870_;
}
else
{
lean_object* v___x_4900_; lean_object* v___x_4901_; 
v___x_4900_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4900_, 0, v___x_4899_);
v___x_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4901_, 0, v___x_4900_);
return v___x_4901_;
}
}
else
{
goto v___jp_4870_;
}
}
}
v___jp_4870_:
{
if (lean_obj_tag(v_val_4869_) == 2)
{
lean_object* v_val_4871_; lean_object* v___x_4872_; uint8_t v___x_4873_; 
v_val_4871_ = lean_ctor_get(v_val_4869_, 1);
v___x_4872_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0));
v___x_4873_ = lean_string_dec_eq(v_val_4871_, v___x_4872_);
if (v___x_4873_ == 0)
{
lean_object* v___x_4874_; 
v___x_4874_ = lean_box(0);
return v___x_4874_;
}
else
{
lean_object* v___x_4875_; 
v___x_4875_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2));
return v___x_4875_;
}
}
else
{
lean_object* v___x_4876_; 
v___x_4876_ = lean_box(0);
return v___x_4876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object* v_val_4902_){
_start:
{
lean_object* v_res_4903_; 
v_res_4903_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_val_4902_);
lean_dec(v_val_4902_);
return v_res_4903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object* v_nameStx_4904_, lean_object* v_v_4905_, lean_object* v_c_4906_){
_start:
{
lean_object* v_toParserModuleContext_4907_; lean_object* v_toInputContext_4908_; lean_object* v_toCacheableParserContext_4909_; lean_object* v_tokens_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4947_; 
v_toParserModuleContext_4907_ = lean_ctor_get(v_c_4906_, 1);
v_toInputContext_4908_ = lean_ctor_get(v_c_4906_, 0);
v_toCacheableParserContext_4909_ = lean_ctor_get(v_c_4906_, 2);
v_tokens_4910_ = lean_ctor_get(v_c_4906_, 3);
v_isSharedCheck_4947_ = !lean_is_exclusive(v_c_4906_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4912_ = v_c_4906_;
v_isShared_4913_ = v_isSharedCheck_4947_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_tokens_4910_);
lean_inc(v_toCacheableParserContext_4909_);
lean_inc(v_toParserModuleContext_4907_);
lean_inc(v_toInputContext_4908_);
lean_dec(v_c_4906_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4947_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v_env_4914_; lean_object* v_options_4915_; lean_object* v_currNamespace_4916_; lean_object* v_openDecls_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4946_; 
v_env_4914_ = lean_ctor_get(v_toParserModuleContext_4907_, 0);
v_options_4915_ = lean_ctor_get(v_toParserModuleContext_4907_, 1);
v_currNamespace_4916_ = lean_ctor_get(v_toParserModuleContext_4907_, 2);
v_openDecls_4917_ = lean_ctor_get(v_toParserModuleContext_4907_, 3);
v_isSharedCheck_4946_ = !lean_is_exclusive(v_toParserModuleContext_4907_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4919_ = v_toParserModuleContext_4907_;
v_isShared_4920_ = v_isSharedCheck_4946_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_openDecls_4917_);
lean_inc(v_currNamespace_4916_);
lean_inc(v_options_4915_);
lean_inc(v_env_4914_);
lean_dec(v_toParserModuleContext_4907_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4946_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___y_4922_; lean_object* v_map_4929_; uint8_t v_hasTrace_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4945_; 
v_map_4929_ = lean_ctor_get(v_options_4915_, 0);
v_hasTrace_4930_ = lean_ctor_get_uint8(v_options_4915_, sizeof(void*)*1);
v_isSharedCheck_4945_ = !lean_is_exclusive(v_options_4915_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4932_ = v_options_4915_;
v_isShared_4933_ = v_isSharedCheck_4945_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_map_4929_);
lean_dec(v_options_4915_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4945_;
goto v_resetjp_4931_;
}
v___jp_4921_:
{
lean_object* v___x_4924_; 
if (v_isShared_4920_ == 0)
{
lean_ctor_set(v___x_4919_, 1, v___y_4922_);
v___x_4924_ = v___x_4919_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_env_4914_);
lean_ctor_set(v_reuseFailAlloc_4928_, 1, v___y_4922_);
lean_ctor_set(v_reuseFailAlloc_4928_, 2, v_currNamespace_4916_);
lean_ctor_set(v_reuseFailAlloc_4928_, 3, v_openDecls_4917_);
v___x_4924_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
lean_object* v___x_4926_; 
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 1, v___x_4924_);
v___x_4926_ = v___x_4912_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_toInputContext_4908_);
lean_ctor_set(v_reuseFailAlloc_4927_, 1, v___x_4924_);
lean_ctor_set(v_reuseFailAlloc_4927_, 2, v_toCacheableParserContext_4909_);
lean_ctor_set(v_reuseFailAlloc_4927_, 3, v_tokens_4910_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
v_resetjp_4931_:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4934_ = l_Lean_Syntax_getId(v_nameStx_4904_);
v___x_4935_ = l_Lean_Name_eraseMacroScopes(v___x_4934_);
lean_dec(v___x_4934_);
lean_inc(v___x_4935_);
v___x_4936_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_4935_, v_v_4905_, v_map_4929_);
if (v_hasTrace_4930_ == 0)
{
lean_object* v___x_4937_; uint8_t v___x_4938_; lean_object* v___x_4940_; 
v___x_4937_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_4938_ = l_Lean_Name_isPrefixOf(v___x_4937_, v___x_4935_);
lean_dec(v___x_4935_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v___x_4936_);
v___x_4940_ = v___x_4932_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4936_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
lean_ctor_set_uint8(v___x_4940_, sizeof(void*)*1, v___x_4938_);
v___y_4922_ = v___x_4940_;
goto v___jp_4921_;
}
}
else
{
lean_object* v___x_4943_; 
lean_dec(v___x_4935_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v___x_4936_);
v___x_4943_ = v___x_4932_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v___x_4936_);
lean_ctor_set_uint8(v_reuseFailAlloc_4944_, sizeof(void*)*1, v_hasTrace_4930_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
v___y_4922_ = v___x_4943_;
goto v___jp_4921_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object* v_nameStx_4948_, lean_object* v_v_4949_, lean_object* v_c_4950_){
_start:
{
lean_object* v_res_4951_; 
v_res_4951_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(v_nameStx_4948_, v_v_4949_, v_c_4950_);
lean_dec(v_nameStx_4948_);
return v_res_4951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object* v_nameStx_4952_, lean_object* v_valStx_4953_, lean_object* v_p_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_valStx_4953_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v___x_4958_; 
lean_dec(v_nameStx_4952_);
v___x_4958_ = lean_apply_2(v_p_4954_, v_a_4955_, v_a_4956_);
return v___x_4958_;
}
else
{
lean_object* v_val_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v_val_4959_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_val_4959_);
lean_dec_ref_known(v___x_4957_, 1);
v___x_4960_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed), 3, 2);
lean_closure_set(v___x_4960_, 0, v_nameStx_4952_);
lean_closure_set(v___x_4960_, 1, v_val_4959_);
v___x_4961_ = l_Lean_Parser_adaptUncacheableContextFn(v___x_4960_, v_p_4954_, v_a_4955_, v_a_4956_);
return v___x_4961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object* v_nameStx_4962_, lean_object* v_valStx_4963_, lean_object* v_p_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v_nameStx_4962_, v_valStx_4963_, v_p_4964_, v_a_4965_, v_a_4966_);
lean_dec(v_valStx_4963_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object* v_p_4974_, lean_object* v_c_4975_, lean_object* v_s_4976_){
_start:
{
lean_object* v_stxStack_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; uint8_t v___x_4980_; 
v_stxStack_4977_ = lean_ctor_get(v_s_4976_, 0);
v___x_4978_ = lean_unsigned_to_nat(0u);
v___x_4979_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4977_);
v___x_4980_ = lean_nat_dec_lt(v___x_4978_, v___x_4979_);
lean_dec(v___x_4979_);
if (v___x_4980_ == 0)
{
lean_object* v___x_4981_; 
v___x_4981_ = lean_apply_2(v_p_4974_, v_c_4975_, v_s_4976_);
return v___x_4981_;
}
else
{
lean_object* v_stx_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; 
v_stx_4982_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4977_);
lean_inc(v_stx_4982_);
v___x_4983_ = l_Lean_Syntax_getKind(v_stx_4982_);
v___x_4984_ = ((lean_object*)(l_Lean_Parser_withSetOptionFn___closed__1));
v___x_4985_ = lean_name_eq(v___x_4983_, v___x_4984_);
lean_dec(v___x_4983_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; 
lean_dec(v_stx_4982_);
v___x_4986_ = lean_apply_2(v_p_4974_, v_c_4975_, v_s_4976_);
return v___x_4986_;
}
else
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4987_ = lean_unsigned_to_nat(1u);
v___x_4988_ = l_Lean_Syntax_getArg(v_stx_4982_, v___x_4987_);
v___x_4989_ = lean_unsigned_to_nat(3u);
v___x_4990_ = l_Lean_Syntax_getArg(v_stx_4982_, v___x_4989_);
lean_dec(v_stx_4982_);
v___x_4991_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_4988_, v___x_4990_, v_p_4974_, v_c_4975_, v_s_4976_);
lean_dec(v___x_4990_);
return v___x_4991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object* v_p_4992_){
_start:
{
lean_object* v_info_4993_; lean_object* v_fn_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5002_; 
v_info_4993_ = lean_ctor_get(v_p_4992_, 0);
v_fn_4994_ = lean_ctor_get(v_p_4992_, 1);
v_isSharedCheck_5002_ = !lean_is_exclusive(v_p_4992_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4996_ = v_p_4992_;
v_isShared_4997_ = v_isSharedCheck_5002_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_fn_4994_);
lean_inc(v_info_4993_);
lean_dec(v_p_4992_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5002_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v___x_4998_; lean_object* v___x_5000_; 
v___x_4998_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionFn), 3, 1);
lean_closure_set(v___x_4998_, 0, v_fn_4994_);
if (v_isShared_4997_ == 0)
{
lean_ctor_set(v___x_4996_, 1, v___x_4998_);
v___x_5000_ = v___x_4996_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_info_4993_);
lean_ctor_set(v_reuseFailAlloc_5001_, 1, v___x_4998_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object* v_p_5003_, lean_object* v_c_5004_, lean_object* v_s_5005_){
_start:
{
lean_object* v_stxStack_5006_; lean_object* v_sz_5007_; lean_object* v___x_5008_; uint8_t v___x_5009_; 
v_stxStack_5006_ = lean_ctor_get(v_s_5005_, 0);
v_sz_5007_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5006_);
v___x_5008_ = lean_unsigned_to_nat(3u);
v___x_5009_ = lean_nat_dec_le(v___x_5008_, v_sz_5007_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; 
lean_dec(v_sz_5007_);
v___x_5010_ = lean_apply_2(v_p_5003_, v_c_5004_, v_s_5005_);
return v___x_5010_;
}
else
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5011_ = lean_nat_sub(v_sz_5007_, v___x_5008_);
lean_dec(v_sz_5007_);
v___x_5012_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5006_, v___x_5011_);
lean_dec(v___x_5011_);
v___x_5013_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5006_);
v___x_5014_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5012_, v___x_5013_, v_p_5003_, v_c_5004_, v_s_5005_);
lean_dec(v___x_5013_);
return v___x_5014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object* v_p_5015_){
_start:
{
lean_object* v_info_5016_; lean_object* v_fn_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5025_; 
v_info_5016_ = lean_ctor_get(v_p_5015_, 0);
v_fn_5017_ = lean_ctor_get(v_p_5015_, 1);
v_isSharedCheck_5025_ = !lean_is_exclusive(v_p_5015_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5019_ = v_p_5015_;
v_isShared_5020_ = v_isSharedCheck_5025_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_fn_5017_);
lean_inc(v_info_5016_);
lean_dec(v_p_5015_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5025_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5021_; lean_object* v___x_5023_; 
v___x_5021_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionValueFn), 3, 1);
lean_closure_set(v___x_5021_, 0, v_fn_5017_);
if (v_isShared_5020_ == 0)
{
lean_ctor_set(v___x_5019_, 1, v___x_5021_);
v___x_5023_ = v___x_5019_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_info_5016_);
lean_ctor_set(v_reuseFailAlloc_5024_, 1, v___x_5021_);
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object* v___x_5026_){
_start:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5028_ = lean_st_ref_get(v___x_5026_);
v___x_5029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5029_, 0, v___x_5028_);
return v___x_5029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v___x_5030_, lean_object* v___y_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_5030_);
lean_dec(v___x_5030_);
return v_res_5032_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5033_; lean_object* v___f_5034_; 
v___x_5033_ = l_Lean_Parser_parserAliasesRef;
v___f_5034_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5034_, 0, v___x_5033_);
return v___f_5034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
v___f_5036_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_);
v___x_5037_ = lean_box(0);
v___x_5038_ = lean_box(2);
v___x_5039_ = l_Lean_registerEnvExtension___redArg(v___f_5036_, v___x_5037_, v___x_5038_);
return v___x_5039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v_a_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
return v_res_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx(lean_object* v_x_5042_){
_start:
{
switch(lean_obj_tag(v_x_5042_))
{
case 0:
{
lean_object* v___x_5043_; 
v___x_5043_ = lean_unsigned_to_nat(0u);
return v___x_5043_;
}
case 1:
{
lean_object* v___x_5044_; 
v___x_5044_ = lean_unsigned_to_nat(1u);
return v___x_5044_;
}
default: 
{
lean_object* v___x_5045_; 
v___x_5045_ = lean_unsigned_to_nat(2u);
return v___x_5045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___boxed(lean_object* v_x_5046_){
_start:
{
lean_object* v_res_5047_; 
v_res_5047_ = l_Lean_Parser_ParserResolution_ctorIdx(v_x_5046_);
lean_dec_ref(v_x_5046_);
return v_res_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object* v_t_5048_, lean_object* v_k_5049_){
_start:
{
switch(lean_obj_tag(v_t_5048_))
{
case 0:
{
lean_object* v_cat_5050_; lean_object* v___x_5051_; 
v_cat_5050_ = lean_ctor_get(v_t_5048_, 0);
lean_inc(v_cat_5050_);
lean_dec_ref_known(v_t_5048_, 1);
v___x_5051_ = lean_apply_1(v_k_5049_, v_cat_5050_);
return v___x_5051_;
}
case 1:
{
lean_object* v_decl_5052_; uint8_t v_isDescr_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
v_decl_5052_ = lean_ctor_get(v_t_5048_, 0);
lean_inc(v_decl_5052_);
v_isDescr_5053_ = lean_ctor_get_uint8(v_t_5048_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5048_, 1);
v___x_5054_ = lean_box(v_isDescr_5053_);
v___x_5055_ = lean_apply_2(v_k_5049_, v_decl_5052_, v___x_5054_);
return v___x_5055_;
}
default: 
{
lean_object* v_p_5056_; lean_object* v___x_5057_; 
v_p_5056_ = lean_ctor_get(v_t_5048_, 0);
lean_inc_ref(v_p_5056_);
lean_dec_ref_known(v_t_5048_, 1);
v___x_5057_ = lean_apply_1(v_k_5049_, v_p_5056_);
return v___x_5057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object* v_motive_5058_, lean_object* v_ctorIdx_5059_, lean_object* v_t_5060_, lean_object* v_h_5061_, lean_object* v_k_5062_){
_start:
{
lean_object* v___x_5063_; 
v___x_5063_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5060_, v_k_5062_);
return v___x_5063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object* v_motive_5064_, lean_object* v_ctorIdx_5065_, lean_object* v_t_5066_, lean_object* v_h_5067_, lean_object* v_k_5068_){
_start:
{
lean_object* v_res_5069_; 
v_res_5069_ = l_Lean_Parser_ParserResolution_ctorElim(v_motive_5064_, v_ctorIdx_5065_, v_t_5066_, v_h_5067_, v_k_5068_);
lean_dec(v_ctorIdx_5065_);
return v_res_5069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object* v_t_5070_, lean_object* v_category_5071_){
_start:
{
lean_object* v___x_5072_; 
v___x_5072_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5070_, v_category_5071_);
return v___x_5072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object* v_motive_5073_, lean_object* v_t_5074_, lean_object* v_h_5075_, lean_object* v_category_5076_){
_start:
{
lean_object* v___x_5077_; 
v___x_5077_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5074_, v_category_5076_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object* v_t_5078_, lean_object* v_parser_5079_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5078_, v_parser_5079_);
return v___x_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object* v_motive_5081_, lean_object* v_t_5082_, lean_object* v_h_5083_, lean_object* v_parser_5084_){
_start:
{
lean_object* v___x_5085_; 
v___x_5085_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5082_, v_parser_5084_);
return v___x_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object* v_t_5086_, lean_object* v_alias_5087_){
_start:
{
lean_object* v___x_5088_; 
v___x_5088_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5086_, v_alias_5087_);
return v___x_5088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object* v_motive_5089_, lean_object* v_t_5090_, lean_object* v_h_5091_, lean_object* v_alias_5092_){
_start:
{
lean_object* v___x_5093_; 
v___x_5093_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5090_, v_alias_5092_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object* v_env_5097_, lean_object* v_name_5098_){
_start:
{
uint8_t v___x_5099_; lean_object* v___x_5100_; 
v___x_5099_ = 0;
v___x_5100_ = l_Lean_Environment_find_x3f(v_env_5097_, v_name_5098_, v___x_5099_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v___x_5101_; 
v___x_5101_ = lean_box(0);
return v___x_5101_;
}
else
{
lean_object* v_val_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5149_; 
v_val_5102_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5149_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_5104_ = v___x_5100_;
v_isShared_5105_ = v_isSharedCheck_5149_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_val_5102_);
lean_dec(v___x_5100_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5149_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v___x_5106_; 
v___x_5106_ = l_Lean_ConstantInfo_type(v_val_5102_);
lean_dec(v_val_5102_);
if (lean_obj_tag(v___x_5106_) == 4)
{
lean_object* v_declName_5107_; 
v_declName_5107_ = lean_ctor_get(v___x_5106_, 0);
lean_inc(v_declName_5107_);
lean_dec_ref_known(v___x_5106_, 2);
if (lean_obj_tag(v_declName_5107_) == 1)
{
lean_object* v_pre_5108_; 
v_pre_5108_ = lean_ctor_get(v_declName_5107_, 0);
lean_inc(v_pre_5108_);
if (lean_obj_tag(v_pre_5108_) == 1)
{
lean_object* v_pre_5109_; 
v_pre_5109_ = lean_ctor_get(v_pre_5108_, 0);
switch(lean_obj_tag(v_pre_5109_))
{
case 1:
{
lean_object* v_pre_5110_; 
lean_inc_ref(v_pre_5109_);
lean_del_object(v___x_5104_);
v_pre_5110_ = lean_ctor_get(v_pre_5109_, 0);
if (lean_obj_tag(v_pre_5110_) == 0)
{
lean_object* v_str_5111_; lean_object* v_str_5112_; lean_object* v_str_5113_; lean_object* v___x_5114_; uint8_t v___x_5115_; 
v_str_5111_ = lean_ctor_get(v_declName_5107_, 1);
lean_inc_ref(v_str_5111_);
lean_dec_ref_known(v_declName_5107_, 2);
v_str_5112_ = lean_ctor_get(v_pre_5108_, 1);
lean_inc_ref(v_str_5112_);
lean_dec_ref_known(v_pre_5108_, 2);
v_str_5113_ = lean_ctor_get(v_pre_5109_, 1);
lean_inc_ref(v_str_5113_);
lean_dec_ref_known(v_pre_5109_, 2);
v___x_5114_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5115_ = lean_string_dec_eq(v_str_5113_, v___x_5114_);
lean_dec_ref(v_str_5113_);
if (v___x_5115_ == 0)
{
lean_object* v___x_5116_; 
lean_dec_ref(v_str_5112_);
lean_dec_ref(v_str_5111_);
v___x_5116_ = lean_box(0);
return v___x_5116_;
}
else
{
lean_object* v___x_5117_; uint8_t v___x_5118_; 
v___x_5117_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_5118_ = lean_string_dec_eq(v_str_5112_, v___x_5117_);
lean_dec_ref(v_str_5112_);
if (v___x_5118_ == 0)
{
lean_object* v___x_5119_; 
lean_dec_ref(v_str_5111_);
v___x_5119_ = lean_box(0);
return v___x_5119_;
}
else
{
uint8_t v___x_5120_; 
v___x_5120_ = lean_string_dec_eq(v_str_5111_, v___x_5117_);
if (v___x_5120_ == 0)
{
lean_object* v___x_5121_; uint8_t v___x_5122_; 
v___x_5121_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_5122_ = lean_string_dec_eq(v_str_5111_, v___x_5121_);
lean_dec_ref(v_str_5111_);
if (v___x_5122_ == 0)
{
lean_object* v___x_5123_; 
v___x_5123_ = lean_box(0);
return v___x_5123_;
}
else
{
lean_object* v___x_5124_; 
v___x_5124_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5124_;
}
}
else
{
lean_object* v___x_5125_; 
lean_dec_ref(v_str_5111_);
v___x_5125_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5125_;
}
}
}
}
else
{
lean_object* v___x_5126_; 
lean_dec_ref_known(v_pre_5109_, 2);
lean_dec_ref_known(v_pre_5108_, 2);
lean_dec_ref_known(v_declName_5107_, 2);
v___x_5126_ = lean_box(0);
return v___x_5126_;
}
}
case 0:
{
lean_object* v_str_5127_; lean_object* v_str_5128_; lean_object* v___x_5129_; uint8_t v___x_5130_; 
v_str_5127_ = lean_ctor_get(v_declName_5107_, 1);
lean_inc_ref(v_str_5127_);
lean_dec_ref_known(v_declName_5107_, 2);
v_str_5128_ = lean_ctor_get(v_pre_5108_, 1);
lean_inc_ref(v_str_5128_);
lean_dec_ref_known(v_pre_5108_, 2);
v___x_5129_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5130_ = lean_string_dec_eq(v_str_5128_, v___x_5129_);
lean_dec_ref(v_str_5128_);
if (v___x_5130_ == 0)
{
lean_object* v___x_5131_; 
lean_dec_ref(v_str_5127_);
lean_del_object(v___x_5104_);
v___x_5131_ = lean_box(0);
return v___x_5131_;
}
else
{
lean_object* v___x_5132_; uint8_t v___x_5133_; 
v___x_5132_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_5133_ = lean_string_dec_eq(v_str_5127_, v___x_5132_);
if (v___x_5133_ == 0)
{
lean_object* v___x_5134_; uint8_t v___x_5135_; 
v___x_5134_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_5135_ = lean_string_dec_eq(v_str_5127_, v___x_5134_);
lean_dec_ref(v_str_5127_);
if (v___x_5135_ == 0)
{
lean_object* v___x_5136_; 
lean_del_object(v___x_5104_);
v___x_5136_ = lean_box(0);
return v___x_5136_;
}
else
{
lean_object* v___x_5137_; lean_object* v___x_5139_; 
v___x_5137_ = lean_box(v___x_5130_);
if (v_isShared_5105_ == 0)
{
lean_ctor_set(v___x_5104_, 0, v___x_5137_);
v___x_5139_ = v___x_5104_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v___x_5137_);
v___x_5139_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
return v___x_5139_;
}
}
}
else
{
lean_object* v___x_5141_; lean_object* v___x_5143_; 
lean_dec_ref(v_str_5127_);
v___x_5141_ = lean_box(v___x_5130_);
if (v_isShared_5105_ == 0)
{
lean_ctor_set(v___x_5104_, 0, v___x_5141_);
v___x_5143_ = v___x_5104_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v___x_5141_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
}
default: 
{
lean_object* v___x_5145_; 
lean_dec_ref_known(v_pre_5108_, 2);
lean_dec_ref_known(v_declName_5107_, 2);
lean_del_object(v___x_5104_);
v___x_5145_ = lean_box(0);
return v___x_5145_;
}
}
}
else
{
lean_object* v___x_5146_; 
lean_dec(v_pre_5108_);
lean_dec_ref_known(v_declName_5107_, 2);
lean_del_object(v___x_5104_);
v___x_5146_ = lean_box(0);
return v___x_5146_;
}
}
else
{
lean_object* v___x_5147_; 
lean_dec(v_declName_5107_);
lean_del_object(v___x_5104_);
v___x_5147_ = lean_box(0);
return v___x_5147_;
}
}
else
{
lean_object* v___x_5148_; 
lean_dec_ref(v___x_5106_);
lean_del_object(v___x_5104_);
v___x_5148_ = lean_box(0);
return v___x_5148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object* v_env_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_){
_start:
{
if (lean_obj_tag(v_a_5151_) == 0)
{
lean_object* v___x_5153_; 
lean_dec_ref(v_env_5150_);
v___x_5153_ = lean_array_to_list(v_a_5152_);
return v___x_5153_;
}
else
{
lean_object* v_head_5154_; lean_object* v_snd_5155_; 
v_head_5154_ = lean_ctor_get(v_a_5151_, 0);
v_snd_5155_ = lean_ctor_get(v_head_5154_, 1);
if (lean_obj_tag(v_snd_5155_) == 0)
{
lean_object* v_tail_5156_; lean_object* v_fst_5157_; lean_object* v___x_5158_; 
lean_inc(v_head_5154_);
v_tail_5156_ = lean_ctor_get(v_a_5151_, 1);
lean_inc(v_tail_5156_);
lean_dec_ref_known(v_a_5151_, 2);
v_fst_5157_ = lean_ctor_get(v_head_5154_, 0);
lean_inc_n(v_fst_5157_, 2);
lean_dec(v_head_5154_);
lean_inc_ref(v_env_5150_);
v___x_5158_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5150_, v_fst_5157_);
if (lean_obj_tag(v___x_5158_) == 0)
{
lean_dec(v_fst_5157_);
v_a_5151_ = v_tail_5156_;
goto _start;
}
else
{
lean_object* v_val_5160_; lean_object* v___x_5161_; uint8_t v___x_5162_; lean_object* v___x_5163_; 
v_val_5160_ = lean_ctor_get(v___x_5158_, 0);
lean_inc(v_val_5160_);
lean_dec_ref_known(v___x_5158_, 1);
v___x_5161_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5161_, 0, v_fst_5157_);
v___x_5162_ = lean_unbox(v_val_5160_);
lean_dec(v_val_5160_);
lean_ctor_set_uint8(v___x_5161_, sizeof(void*)*1, v___x_5162_);
v___x_5163_ = lean_array_push(v_a_5152_, v___x_5161_);
v_a_5151_ = v_tail_5156_;
v_a_5152_ = v___x_5163_;
goto _start;
}
}
else
{
lean_object* v_tail_5165_; 
v_tail_5165_ = lean_ctor_get(v_a_5151_, 1);
lean_inc(v_tail_5165_);
lean_dec_ref_known(v_a_5151_, 2);
v_a_5151_ = v_tail_5165_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object* v_env_5170_, lean_object* v_as_x27_5171_, lean_object* v_b_5172_){
_start:
{
if (lean_obj_tag(v_as_x27_5171_) == 0)
{
lean_dec_ref(v_env_5170_);
lean_inc_ref(v_b_5172_);
return v_b_5172_;
}
else
{
lean_object* v_head_5173_; lean_object* v_tail_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; 
v_head_5173_ = lean_ctor_get(v_as_x27_5171_, 0);
v_tail_5174_ = lean_ctor_get(v_as_x27_5171_, 1);
v___x_5175_ = lean_box(0);
v___x_5176_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_5173_) == 1)
{
lean_object* v_fields_5177_; 
v_fields_5177_ = lean_ctor_get(v_head_5173_, 1);
if (lean_obj_tag(v_fields_5177_) == 0)
{
lean_object* v_n_5178_; lean_object* v___x_5179_; 
v_n_5178_ = lean_ctor_get(v_head_5173_, 0);
lean_inc(v_n_5178_);
lean_inc_ref(v_env_5170_);
v___x_5179_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5170_, v_n_5178_);
if (lean_obj_tag(v___x_5179_) == 1)
{
lean_object* v_val_5180_; lean_object* v___x_5182_; uint8_t v_isShared_5183_; uint8_t v_isSharedCheck_5192_; 
lean_dec_ref(v_env_5170_);
v_val_5180_ = lean_ctor_get(v___x_5179_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5182_ = v___x_5179_;
v_isShared_5183_ = v_isSharedCheck_5192_;
goto v_resetjp_5181_;
}
else
{
lean_inc(v_val_5180_);
lean_dec(v___x_5179_);
v___x_5182_ = lean_box(0);
v_isShared_5183_ = v_isSharedCheck_5192_;
goto v_resetjp_5181_;
}
v_resetjp_5181_:
{
lean_object* v___x_5184_; uint8_t v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5189_; 
lean_inc(v_n_5178_);
v___x_5184_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5184_, 0, v_n_5178_);
v___x_5185_ = lean_unbox(v_val_5180_);
lean_dec(v_val_5180_);
lean_ctor_set_uint8(v___x_5184_, sizeof(void*)*1, v___x_5185_);
v___x_5186_ = lean_box(0);
v___x_5187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5184_);
lean_ctor_set(v___x_5187_, 1, v___x_5186_);
if (v_isShared_5183_ == 0)
{
lean_ctor_set(v___x_5182_, 0, v___x_5187_);
v___x_5189_ = v___x_5182_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5187_);
v___x_5189_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
lean_object* v___x_5190_; 
v___x_5190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5190_, 0, v___x_5189_);
lean_ctor_set(v___x_5190_, 1, v___x_5175_);
return v___x_5190_;
}
}
}
else
{
lean_dec(v___x_5179_);
v_as_x27_5171_ = v_tail_5174_;
v_b_5172_ = v___x_5176_;
goto _start;
}
}
else
{
v_as_x27_5171_ = v_tail_5174_;
v_b_5172_ = v___x_5176_;
goto _start;
}
}
else
{
v_as_x27_5171_ = v_tail_5174_;
v_b_5172_ = v___x_5176_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object* v_env_5196_, lean_object* v_as_x27_5197_, lean_object* v_b_5198_){
_start:
{
lean_object* v_res_5199_; 
v_res_5199_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5196_, v_as_x27_5197_, v_b_5198_);
lean_dec_ref(v_b_5198_);
lean_dec(v_as_x27_5197_);
return v_res_5199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object* v_env_5202_, lean_object* v_opts_5203_, lean_object* v_currNamespace_5204_, lean_object* v_openDecls_5205_, lean_object* v_ident_5206_){
_start:
{
if (lean_obj_tag(v_ident_5206_) == 3)
{
lean_object* v_val_5207_; lean_object* v_preresolved_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v_fst_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5246_; 
v_val_5207_ = lean_ctor_get(v_ident_5206_, 2);
lean_inc(v_val_5207_);
v_preresolved_5208_ = lean_ctor_get(v_ident_5206_, 3);
lean_inc(v_preresolved_5208_);
lean_dec_ref_known(v_ident_5206_, 4);
v___x_5209_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
lean_inc_ref(v_env_5202_);
v___x_5210_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5202_, v_preresolved_5208_, v___x_5209_);
lean_dec(v_preresolved_5208_);
v_fst_5211_ = lean_ctor_get(v___x_5210_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___x_5210_);
if (v_isSharedCheck_5246_ == 0)
{
lean_object* v_unused_5247_; 
v_unused_5247_ = lean_ctor_get(v___x_5210_, 1);
lean_dec(v_unused_5247_);
v___x_5213_ = v___x_5210_;
v_isShared_5214_ = v_isSharedCheck_5246_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_fst_5211_);
lean_dec(v___x_5210_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5246_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
if (lean_obj_tag(v_fst_5211_) == 0)
{
lean_object* v___x_5215_; uint8_t v___x_5216_; 
v___x_5215_ = l_Lean_Name_eraseMacroScopes(v_val_5207_);
lean_inc_ref(v_env_5202_);
v___x_5216_ = l_Lean_Parser_isParserCategory(v_env_5202_, v___x_5215_);
if (v___x_5216_ == 0)
{
lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; uint8_t v___x_5220_; 
lean_inc_ref_n(v_env_5202_, 2);
v___x_5217_ = l_Lean_ResolveName_resolveGlobalName(v_env_5202_, v_opts_5203_, v_currNamespace_5204_, v_openDecls_5205_, v_val_5207_);
v___x_5218_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0));
v___x_5219_ = l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(v_env_5202_, v___x_5217_, v___x_5218_);
v___x_5220_ = l_List_isEmpty___redArg(v___x_5219_);
if (v___x_5220_ == 0)
{
lean_dec(v___x_5215_);
lean_del_object(v___x_5213_);
lean_dec_ref(v_env_5202_);
return v___x_5219_;
}
else
{
lean_object* v___x_5221_; lean_object* v_asyncMode_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
lean_dec(v___x_5219_);
v___x_5221_ = l_Lean_Parser_aliasExtension;
v_asyncMode_5222_ = lean_ctor_get(v___x_5221_, 2);
v___x_5223_ = lean_box(1);
v___x_5224_ = lean_box(0);
v___x_5225_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5223_, v___x_5221_, v_env_5202_, v_asyncMode_5222_, v___x_5224_);
v___x_5226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5225_, v___x_5215_);
lean_dec(v___x_5215_);
lean_dec(v___x_5225_);
if (lean_obj_tag(v___x_5226_) == 1)
{
lean_object* v_val_5227_; lean_object* v___x_5229_; uint8_t v_isShared_5230_; uint8_t v_isSharedCheck_5238_; 
v_val_5227_ = lean_ctor_get(v___x_5226_, 0);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5226_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5229_ = v___x_5226_;
v_isShared_5230_ = v_isSharedCheck_5238_;
goto v_resetjp_5228_;
}
else
{
lean_inc(v_val_5227_);
lean_dec(v___x_5226_);
v___x_5229_ = lean_box(0);
v_isShared_5230_ = v_isSharedCheck_5238_;
goto v_resetjp_5228_;
}
v_resetjp_5228_:
{
lean_object* v___x_5232_; 
if (v_isShared_5230_ == 0)
{
lean_ctor_set_tag(v___x_5229_, 2);
v___x_5232_ = v___x_5229_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_val_5227_);
v___x_5232_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
lean_object* v___x_5233_; lean_object* v___x_5235_; 
v___x_5233_ = lean_box(0);
if (v_isShared_5214_ == 0)
{
lean_ctor_set_tag(v___x_5213_, 1);
lean_ctor_set(v___x_5213_, 1, v___x_5233_);
lean_ctor_set(v___x_5213_, 0, v___x_5232_);
v___x_5235_ = v___x_5213_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v___x_5232_);
lean_ctor_set(v_reuseFailAlloc_5236_, 1, v___x_5233_);
v___x_5235_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
return v___x_5235_;
}
}
}
}
else
{
lean_object* v___x_5239_; 
lean_dec(v___x_5226_);
lean_del_object(v___x_5213_);
v___x_5239_ = lean_box(0);
return v___x_5239_;
}
}
}
else
{
lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5243_; 
lean_dec(v_val_5207_);
lean_dec(v_openDecls_5205_);
lean_dec(v_currNamespace_5204_);
lean_dec_ref(v_env_5202_);
v___x_5240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5240_, 0, v___x_5215_);
v___x_5241_ = lean_box(0);
if (v_isShared_5214_ == 0)
{
lean_ctor_set_tag(v___x_5213_, 1);
lean_ctor_set(v___x_5213_, 1, v___x_5241_);
lean_ctor_set(v___x_5213_, 0, v___x_5240_);
v___x_5243_ = v___x_5213_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v___x_5240_);
lean_ctor_set(v_reuseFailAlloc_5244_, 1, v___x_5241_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
else
{
lean_object* v_val_5245_; 
lean_del_object(v___x_5213_);
lean_dec(v_val_5207_);
lean_dec(v_openDecls_5205_);
lean_dec(v_currNamespace_5204_);
lean_dec_ref(v_env_5202_);
v_val_5245_ = lean_ctor_get(v_fst_5211_, 0);
lean_inc(v_val_5245_);
lean_dec_ref_known(v_fst_5211_, 1);
return v_val_5245_;
}
}
}
else
{
lean_object* v___x_5248_; 
lean_dec(v_ident_5206_);
lean_dec(v_openDecls_5205_);
lean_dec(v_currNamespace_5204_);
lean_dec_ref(v_env_5202_);
v___x_5248_ = lean_box(0);
return v___x_5248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object* v_env_5249_, lean_object* v_opts_5250_, lean_object* v_currNamespace_5251_, lean_object* v_openDecls_5252_, lean_object* v_ident_5253_){
_start:
{
lean_object* v_res_5254_; 
v_res_5254_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5249_, v_opts_5250_, v_currNamespace_5251_, v_openDecls_5252_, v_ident_5253_);
lean_dec_ref(v_opts_5250_);
return v_res_5254_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object* v_env_5255_, lean_object* v_as_5256_, lean_object* v_as_x27_5257_, lean_object* v_b_5258_, lean_object* v_a_5259_){
_start:
{
lean_object* v___x_5260_; 
v___x_5260_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5255_, v_as_x27_5257_, v_b_5258_);
return v___x_5260_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object* v_env_5261_, lean_object* v_as_5262_, lean_object* v_as_x27_5263_, lean_object* v_b_5264_, lean_object* v_a_5265_){
_start:
{
lean_object* v_res_5266_; 
v_res_5266_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(v_env_5261_, v_as_5262_, v_as_x27_5263_, v_b_5264_, v_a_5265_);
lean_dec_ref(v_b_5264_);
lean_dec(v_as_x27_5263_);
lean_dec(v_as_5262_);
return v_res_5266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object* v_ctx_5267_, lean_object* v_id_5268_, uint8_t v_unsetExporting_5269_){
_start:
{
lean_object* v___y_5271_; 
if (v_unsetExporting_5269_ == 0)
{
lean_object* v_toParserModuleContext_5277_; lean_object* v_env_5278_; 
v_toParserModuleContext_5277_ = lean_ctor_get(v_ctx_5267_, 1);
v_env_5278_ = lean_ctor_get(v_toParserModuleContext_5277_, 0);
lean_inc_ref(v_env_5278_);
v___y_5271_ = v_env_5278_;
goto v___jp_5270_;
}
else
{
lean_object* v_toParserModuleContext_5279_; lean_object* v_env_5280_; uint8_t v___x_5281_; lean_object* v___x_5282_; 
v_toParserModuleContext_5279_ = lean_ctor_get(v_ctx_5267_, 1);
v_env_5280_ = lean_ctor_get(v_toParserModuleContext_5279_, 0);
v___x_5281_ = 0;
lean_inc_ref(v_env_5280_);
v___x_5282_ = l_Lean_Environment_setExporting(v_env_5280_, v___x_5281_);
v___y_5271_ = v___x_5282_;
goto v___jp_5270_;
}
v___jp_5270_:
{
lean_object* v_toParserModuleContext_5272_; lean_object* v_options_5273_; lean_object* v_currNamespace_5274_; lean_object* v_openDecls_5275_; lean_object* v___x_5276_; 
v_toParserModuleContext_5272_ = lean_ctor_get(v_ctx_5267_, 1);
lean_inc_ref(v_toParserModuleContext_5272_);
lean_dec_ref(v_ctx_5267_);
v_options_5273_ = lean_ctor_get(v_toParserModuleContext_5272_, 1);
lean_inc_ref(v_options_5273_);
v_currNamespace_5274_ = lean_ctor_get(v_toParserModuleContext_5272_, 2);
lean_inc(v_currNamespace_5274_);
v_openDecls_5275_ = lean_ctor_get(v_toParserModuleContext_5272_, 3);
lean_inc(v_openDecls_5275_);
lean_dec_ref(v_toParserModuleContext_5272_);
v___x_5276_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v___y_5271_, v_options_5273_, v_currNamespace_5274_, v_openDecls_5275_, v_id_5268_);
lean_dec_ref(v_options_5273_);
return v___x_5276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object* v_ctx_5283_, lean_object* v_id_5284_, lean_object* v_unsetExporting_5285_){
_start:
{
uint8_t v_unsetExporting_boxed_5286_; lean_object* v_res_5287_; 
v_unsetExporting_boxed_5286_ = lean_unbox(v_unsetExporting_5285_);
v_res_5287_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5283_, v_id_5284_, v_unsetExporting_boxed_5286_);
return v_res_5287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object* v_id_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_){
_start:
{
lean_object* v___x_5292_; lean_object* v_env_5293_; lean_object* v_options_5294_; lean_object* v_currNamespace_5295_; lean_object* v_openDecls_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5292_ = lean_st_ref_get(v_a_5290_);
v_env_5293_ = lean_ctor_get(v___x_5292_, 0);
lean_inc_ref(v_env_5293_);
lean_dec(v___x_5292_);
v_options_5294_ = lean_ctor_get(v_a_5289_, 2);
v_currNamespace_5295_ = lean_ctor_get(v_a_5289_, 6);
v_openDecls_5296_ = lean_ctor_get(v_a_5289_, 7);
lean_inc(v_openDecls_5296_);
lean_inc(v_currNamespace_5295_);
v___x_5297_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5293_, v_options_5294_, v_currNamespace_5295_, v_openDecls_5296_, v_id_5288_);
v___x_5298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5298_, 0, v___x_5297_);
return v___x_5298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object* v_id_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Lean_Parser_resolveParserName(v_id_5299_, v_a_5300_, v_a_5301_);
lean_dec(v_a_5301_);
lean_dec_ref(v_a_5300_);
return v_res_5303_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object* v_x_5304_, lean_object* v_x_5305_){
_start:
{
if (lean_obj_tag(v_x_5304_) == 0)
{
if (lean_obj_tag(v_x_5305_) == 0)
{
uint8_t v___x_5306_; 
v___x_5306_ = 1;
return v___x_5306_;
}
else
{
uint8_t v___x_5307_; 
v___x_5307_ = 0;
return v___x_5307_;
}
}
else
{
if (lean_obj_tag(v_x_5305_) == 0)
{
uint8_t v___x_5308_; 
v___x_5308_ = 0;
return v___x_5308_;
}
else
{
lean_object* v_val_5309_; lean_object* v_val_5310_; uint8_t v___x_5311_; 
v_val_5309_ = lean_ctor_get(v_x_5304_, 0);
v_val_5310_ = lean_ctor_get(v_x_5305_, 0);
v___x_5311_ = l_Lean_Parser_instBEqError_beq(v_val_5309_, v_val_5310_);
return v___x_5311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object* v_x_5312_, lean_object* v_x_5313_){
_start:
{
uint8_t v_res_5314_; lean_object* v_r_5315_; 
v_res_5314_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5312_, v_x_5313_);
lean_dec(v_x_5313_);
lean_dec(v_x_5312_);
v_r_5315_ = lean_box(v_res_5314_);
return v_r_5315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t v___x_5316_, lean_object* v_ctx_5317_){
_start:
{
lean_object* v_toParserModuleContext_5318_; lean_object* v_toInputContext_5319_; lean_object* v_toCacheableParserContext_5320_; lean_object* v_tokens_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5346_; 
v_toParserModuleContext_5318_ = lean_ctor_get(v_ctx_5317_, 1);
v_toInputContext_5319_ = lean_ctor_get(v_ctx_5317_, 0);
v_toCacheableParserContext_5320_ = lean_ctor_get(v_ctx_5317_, 2);
v_tokens_5321_ = lean_ctor_get(v_ctx_5317_, 3);
v_isSharedCheck_5346_ = !lean_is_exclusive(v_ctx_5317_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5323_ = v_ctx_5317_;
v_isShared_5324_ = v_isSharedCheck_5346_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_tokens_5321_);
lean_inc(v_toCacheableParserContext_5320_);
lean_inc(v_toParserModuleContext_5318_);
lean_inc(v_toInputContext_5319_);
lean_dec(v_ctx_5317_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5346_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v_env_5325_; lean_object* v_options_5326_; lean_object* v_currNamespace_5327_; lean_object* v_openDecls_5328_; lean_object* v___x_5330_; uint8_t v_isShared_5331_; uint8_t v_isSharedCheck_5345_; 
v_env_5325_ = lean_ctor_get(v_toParserModuleContext_5318_, 0);
v_options_5326_ = lean_ctor_get(v_toParserModuleContext_5318_, 1);
v_currNamespace_5327_ = lean_ctor_get(v_toParserModuleContext_5318_, 2);
v_openDecls_5328_ = lean_ctor_get(v_toParserModuleContext_5318_, 3);
v_isSharedCheck_5345_ = !lean_is_exclusive(v_toParserModuleContext_5318_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5330_ = v_toParserModuleContext_5318_;
v_isShared_5331_ = v_isSharedCheck_5345_;
goto v_resetjp_5329_;
}
else
{
lean_inc(v_openDecls_5328_);
lean_inc(v_currNamespace_5327_);
lean_inc(v_options_5326_);
lean_inc(v_env_5325_);
lean_dec(v_toParserModuleContext_5318_);
v___x_5330_ = lean_box(0);
v_isShared_5331_ = v_isSharedCheck_5345_;
goto v_resetjp_5329_;
}
v_resetjp_5329_:
{
lean_object* v___x_5332_; uint8_t v___y_5334_; lean_object* v___x_5342_; uint8_t v___x_5343_; 
v___x_5332_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_5342_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_5343_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_5326_, v___x_5342_);
if (v___x_5343_ == 0)
{
uint8_t v___x_5344_; 
v___x_5344_ = 1;
v___y_5334_ = v___x_5344_;
goto v___jp_5333_;
}
else
{
v___y_5334_ = v___x_5316_;
goto v___jp_5333_;
}
v___jp_5333_:
{
lean_object* v___x_5335_; lean_object* v___x_5337_; 
v___x_5335_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_5326_, v___x_5332_, v___y_5334_);
if (v_isShared_5331_ == 0)
{
lean_ctor_set(v___x_5330_, 1, v___x_5335_);
v___x_5337_ = v___x_5330_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v_env_5325_);
lean_ctor_set(v_reuseFailAlloc_5341_, 1, v___x_5335_);
lean_ctor_set(v_reuseFailAlloc_5341_, 2, v_currNamespace_5327_);
lean_ctor_set(v_reuseFailAlloc_5341_, 3, v_openDecls_5328_);
v___x_5337_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
lean_object* v___x_5339_; 
if (v_isShared_5324_ == 0)
{
lean_ctor_set(v___x_5323_, 1, v___x_5337_);
v___x_5339_ = v___x_5323_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_toInputContext_5319_);
lean_ctor_set(v_reuseFailAlloc_5340_, 1, v___x_5337_);
lean_ctor_set(v_reuseFailAlloc_5340_, 2, v_toCacheableParserContext_5320_);
lean_ctor_set(v_reuseFailAlloc_5340_, 3, v_tokens_5321_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
return v___x_5339_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object* v___x_5347_, lean_object* v_ctx_5348_){
_start:
{
uint8_t v___x_1069__boxed_5349_; lean_object* v_res_5350_; 
v___x_1069__boxed_5349_ = lean_unbox(v___x_5347_);
v_res_5350_ = l_Lean_Parser_parserOfStackFn___lam__0(v___x_1069__boxed_5349_, v_ctx_5348_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* v_offset_5358_, lean_object* v_ctx_5359_, lean_object* v_s_5360_){
_start:
{
lean_object* v_stxStack_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; uint8_t v___x_5365_; 
v_stxStack_5361_ = lean_ctor_get(v_s_5360_, 0);
v___x_5362_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5361_);
v___x_5363_ = lean_unsigned_to_nat(1u);
v___x_5364_ = lean_nat_add(v_offset_5358_, v___x_5363_);
v___x_5365_ = lean_nat_dec_lt(v___x_5362_, v___x_5364_);
lean_dec(v___x_5364_);
if (v___x_5365_ == 0)
{
lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; 
v___x_5366_ = lean_nat_sub(v___x_5362_, v_offset_5358_);
lean_dec(v___x_5362_);
v___x_5367_ = lean_nat_sub(v___x_5366_, v___x_5363_);
lean_dec(v___x_5366_);
v___x_5368_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5361_, v___x_5367_);
lean_dec(v___x_5367_);
if (lean_obj_tag(v___x_5368_) == 3)
{
uint8_t v___x_5380_; lean_object* v___x_5381_; 
v___x_5380_ = 1;
lean_inc_ref(v___x_5368_);
lean_inc_ref(v_ctx_5359_);
v___x_5381_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5359_, v___x_5368_, v___x_5380_);
if (lean_obj_tag(v___x_5381_) == 0)
{
lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; 
lean_dec_ref(v_ctx_5359_);
v___x_5382_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__1));
v___x_5383_ = lean_box(0);
v___x_5384_ = l_Lean_Syntax_formatStx(v___x_5368_, v___x_5383_, v___x_5365_);
v___x_5385_ = l_Std_Format_defWidth;
v___x_5386_ = lean_unsigned_to_nat(0u);
v___x_5387_ = l_Std_Format_pretty(v___x_5384_, v___x_5385_, v___x_5386_, v___x_5386_);
v___x_5388_ = lean_string_append(v___x_5382_, v___x_5387_);
lean_dec_ref(v___x_5387_);
v___x_5389_ = lean_box(0);
v___x_5390_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5360_, v___x_5388_, v___x_5389_, v___x_5380_);
return v___x_5390_;
}
else
{
lean_object* v_head_5391_; lean_object* v_tail_5392_; lean_object* v_iniSz_5393_; lean_object* v_s_5395_; 
v_head_5391_ = lean_ctor_get(v___x_5381_, 0);
lean_inc(v_head_5391_);
v_tail_5392_ = lean_ctor_get(v___x_5381_, 1);
lean_inc(v_tail_5392_);
lean_dec_ref_known(v___x_5381_, 2);
v_iniSz_5393_ = l_Lean_Parser_ParserState_stackSize(v_s_5360_);
switch(lean_obj_tag(v_head_5391_))
{
case 0:
{
if (lean_obj_tag(v_tail_5392_) == 0)
{
lean_object* v_cat_5405_; lean_object* v___x_5406_; 
lean_dec_ref_known(v___x_5368_, 4);
v_cat_5405_ = lean_ctor_get(v_head_5391_, 0);
lean_inc(v_cat_5405_);
lean_dec_ref_known(v_head_5391_, 1);
v___x_5406_ = l_Lean_Parser_categoryParserFn(v_cat_5405_, v_ctx_5359_, v_s_5360_);
v_s_5395_ = v___x_5406_;
goto v___jp_5394_;
}
else
{
lean_dec_ref_known(v_tail_5392_, 2);
lean_dec_ref_known(v_head_5391_, 1);
lean_dec(v_iniSz_5393_);
lean_dec_ref(v_ctx_5359_);
goto v___jp_5369_;
}
}
case 1:
{
if (lean_obj_tag(v_tail_5392_) == 0)
{
lean_object* v_decl_5407_; lean_object* v___x_5408_; lean_object* v___f_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; 
lean_dec_ref_known(v___x_5368_, 4);
v_decl_5407_ = lean_ctor_get(v_head_5391_, 0);
lean_inc(v_decl_5407_);
lean_dec_ref_known(v_head_5391_, 1);
v___x_5408_ = lean_box(v___x_5365_);
v___f_5409_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5409_, 0, v___x_5408_);
v___x_5410_ = lean_box(0);
v___x_5411_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_5411_, 0, v_decl_5407_);
lean_closure_set(v___x_5411_, 1, v___x_5410_);
v___x_5412_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5409_, v___x_5411_, v_ctx_5359_, v_s_5360_);
v_s_5395_ = v___x_5412_;
goto v___jp_5394_;
}
else
{
lean_dec_ref_known(v_tail_5392_, 2);
lean_dec_ref_known(v_head_5391_, 1);
lean_dec(v_iniSz_5393_);
lean_dec_ref(v_ctx_5359_);
goto v___jp_5369_;
}
}
default: 
{
if (lean_obj_tag(v_tail_5392_) == 0)
{
lean_object* v_p_5413_; 
v_p_5413_ = lean_ctor_get(v_head_5391_, 0);
lean_inc_ref(v_p_5413_);
lean_dec_ref_known(v_head_5391_, 1);
if (lean_obj_tag(v_p_5413_) == 0)
{
lean_object* v_p_5414_; lean_object* v_fn_5415_; lean_object* v___x_5416_; 
lean_dec_ref_known(v___x_5368_, 4);
v_p_5414_ = lean_ctor_get(v_p_5413_, 0);
lean_inc(v_p_5414_);
lean_dec_ref_known(v_p_5413_, 1);
v_fn_5415_ = lean_ctor_get(v_p_5414_, 1);
lean_inc_ref(v_fn_5415_);
lean_dec(v_p_5414_);
v___x_5416_ = lean_apply_2(v_fn_5415_, v_ctx_5359_, v_s_5360_);
v_s_5395_ = v___x_5416_;
goto v___jp_5394_;
}
else
{
lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; 
lean_dec_ref(v_p_5413_);
lean_dec(v_iniSz_5393_);
lean_dec_ref(v_ctx_5359_);
v___x_5417_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__3));
v___x_5418_ = lean_box(0);
v___x_5419_ = l_Lean_Syntax_formatStx(v___x_5368_, v___x_5418_, v___x_5365_);
v___x_5420_ = l_Std_Format_defWidth;
v___x_5421_ = lean_unsigned_to_nat(0u);
v___x_5422_ = l_Std_Format_pretty(v___x_5419_, v___x_5420_, v___x_5421_, v___x_5421_);
v___x_5423_ = lean_string_append(v___x_5417_, v___x_5422_);
lean_dec_ref(v___x_5422_);
v___x_5424_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__4));
v___x_5425_ = lean_string_append(v___x_5423_, v___x_5424_);
v___x_5426_ = lean_box(0);
v___x_5427_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5360_, v___x_5425_, v___x_5426_, v___x_5380_);
return v___x_5427_;
}
}
else
{
lean_dec_ref_known(v_tail_5392_, 2);
lean_dec_ref_known(v_head_5391_, 1);
lean_dec(v_iniSz_5393_);
lean_dec_ref(v_ctx_5359_);
goto v___jp_5369_;
}
}
}
v___jp_5394_:
{
lean_object* v_errorMsg_5396_; lean_object* v___x_5397_; uint8_t v___x_5398_; 
v_errorMsg_5396_ = lean_ctor_get(v_s_5395_, 4);
v___x_5397_ = lean_box(0);
v___x_5398_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_errorMsg_5396_, v___x_5397_);
if (v___x_5398_ == 0)
{
lean_dec(v_iniSz_5393_);
return v_s_5395_;
}
else
{
lean_object* v___x_5399_; lean_object* v___x_5400_; uint8_t v___x_5401_; 
v___x_5399_ = l_Lean_Parser_ParserState_stackSize(v_s_5395_);
v___x_5400_ = lean_nat_add(v_iniSz_5393_, v___x_5363_);
lean_dec(v_iniSz_5393_);
v___x_5401_ = lean_nat_dec_eq(v___x_5399_, v___x_5400_);
lean_dec(v___x_5400_);
lean_dec(v___x_5399_);
if (v___x_5401_ == 0)
{
lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5402_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__2));
v___x_5403_ = lean_box(0);
v___x_5404_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5395_, v___x_5402_, v___x_5403_, v___x_5398_);
return v___x_5404_;
}
else
{
return v_s_5395_;
}
}
}
}
}
else
{
lean_object* v___x_5428_; lean_object* v___x_5429_; uint8_t v___x_5430_; lean_object* v___x_5431_; 
lean_dec(v___x_5368_);
lean_dec_ref(v_ctx_5359_);
v___x_5428_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__5));
v___x_5429_ = lean_box(0);
v___x_5430_ = 1;
v___x_5431_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5360_, v___x_5428_, v___x_5429_, v___x_5430_);
return v___x_5431_;
}
v___jp_5369_:
{
lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; uint8_t v___x_5378_; lean_object* v___x_5379_; 
v___x_5370_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__0));
v___x_5371_ = lean_box(0);
v___x_5372_ = l_Lean_Syntax_formatStx(v___x_5368_, v___x_5371_, v___x_5365_);
v___x_5373_ = l_Std_Format_defWidth;
v___x_5374_ = lean_unsigned_to_nat(0u);
v___x_5375_ = l_Std_Format_pretty(v___x_5372_, v___x_5373_, v___x_5374_, v___x_5374_);
v___x_5376_ = lean_string_append(v___x_5370_, v___x_5375_);
lean_dec_ref(v___x_5375_);
v___x_5377_ = lean_box(0);
v___x_5378_ = 1;
v___x_5379_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5360_, v___x_5376_, v___x_5377_, v___x_5378_);
return v___x_5379_;
}
}
else
{
lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; 
lean_dec(v___x_5362_);
lean_dec_ref(v_ctx_5359_);
v___x_5432_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__6));
v___x_5433_ = lean_box(0);
v___x_5434_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5360_, v___x_5432_, v___x_5433_, v___x_5365_);
return v___x_5434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* v_offset_5435_, lean_object* v_ctx_5436_, lean_object* v_s_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = l_Lean_Parser_parserOfStackFn(v_offset_5435_, v_ctx_5436_, v_s_5437_);
lean_dec(v_offset_5435_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object* v_prec_5439_, lean_object* v_x_5440_){
_start:
{
lean_object* v_quotDepth_5441_; uint8_t v_suppressInsideQuot_5442_; lean_object* v_savedPos_x3f_5443_; lean_object* v_forbiddenTks_5444_; lean_object* v___x_5446_; uint8_t v_isShared_5447_; uint8_t v_isSharedCheck_5451_; 
v_quotDepth_5441_ = lean_ctor_get(v_x_5440_, 1);
v_suppressInsideQuot_5442_ = lean_ctor_get_uint8(v_x_5440_, sizeof(void*)*4);
v_savedPos_x3f_5443_ = lean_ctor_get(v_x_5440_, 2);
v_forbiddenTks_5444_ = lean_ctor_get(v_x_5440_, 3);
v_isSharedCheck_5451_ = !lean_is_exclusive(v_x_5440_);
if (v_isSharedCheck_5451_ == 0)
{
lean_object* v_unused_5452_; 
v_unused_5452_ = lean_ctor_get(v_x_5440_, 0);
lean_dec(v_unused_5452_);
v___x_5446_ = v_x_5440_;
v_isShared_5447_ = v_isSharedCheck_5451_;
goto v_resetjp_5445_;
}
else
{
lean_inc(v_forbiddenTks_5444_);
lean_inc(v_savedPos_x3f_5443_);
lean_inc(v_quotDepth_5441_);
lean_dec(v_x_5440_);
v___x_5446_ = lean_box(0);
v_isShared_5447_ = v_isSharedCheck_5451_;
goto v_resetjp_5445_;
}
v_resetjp_5445_:
{
lean_object* v___x_5449_; 
if (v_isShared_5447_ == 0)
{
lean_ctor_set(v___x_5446_, 0, v_prec_5439_);
v___x_5449_ = v___x_5446_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v_prec_5439_);
lean_ctor_set(v_reuseFailAlloc_5450_, 1, v_quotDepth_5441_);
lean_ctor_set(v_reuseFailAlloc_5450_, 2, v_savedPos_x3f_5443_);
lean_ctor_set(v_reuseFailAlloc_5450_, 3, v_forbiddenTks_5444_);
lean_ctor_set_uint8(v_reuseFailAlloc_5450_, sizeof(void*)*4, v_suppressInsideQuot_5442_);
v___x_5449_ = v_reuseFailAlloc_5450_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
return v___x_5449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object* v___y_5453_){
_start:
{
lean_inc(v___y_5453_);
return v___y_5453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object* v___y_5454_){
_start:
{
lean_object* v_res_5455_; 
v_res_5455_ = l_Lean_Parser_parserOfStack___lam__1(v___y_5454_);
lean_dec(v___y_5454_);
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object* v___y_5456_){
_start:
{
lean_inc_ref(v___y_5456_);
return v___y_5456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object* v___y_5457_){
_start:
{
lean_object* v_res_5458_; 
v_res_5458_ = l_Lean_Parser_parserOfStack___lam__2(v___y_5457_);
lean_dec_ref(v___y_5457_);
return v_res_5458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* v_offset_5465_, lean_object* v_prec_5466_){
_start:
{
lean_object* v___f_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; 
v___f_5467_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___lam__0), 2, 1);
lean_closure_set(v___f_5467_, 0, v_prec_5466_);
v___x_5468_ = ((lean_object*)(l_Lean_Parser_parserOfStack___closed__2));
v___x_5469_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___boxed), 3, 1);
lean_closure_set(v___x_5469_, 0, v_offset_5465_);
v___x_5470_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5470_, 0, v___f_5467_);
lean_closure_set(v___x_5470_, 1, v___x_5469_);
v___x_5471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5471_, 0, v___x_5468_);
lean_ctor_set(v___x_5471_, 1, v___x_5470_);
return v___x_5471_;
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
