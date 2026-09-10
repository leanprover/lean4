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
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fieldIdx"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 141, 165, 29, 238, 211, 61, 163)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_58_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_59_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_58_);
lean_dec_ref(v___x_59_);
v___x_60_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_61_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_60_);
lean_dec_ref(v___x_61_);
v___x_62_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_63_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_62_);
lean_dec_ref(v___x_63_);
v___x_64_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_65_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_64_);
lean_dec_ref(v___x_65_);
v___x_66_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_67_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_66_);
lean_dec_ref(v___x_67_);
v___x_68_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_69_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_68_);
lean_dec_ref(v___x_69_);
v___x_70_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_71_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_70_);
lean_dec_ref(v___x_71_);
v___x_72_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_73_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_72_);
lean_dec_ref(v___x_73_);
v___x_74_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_75_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_74_);
lean_dec_ref(v___x_75_);
v___x_76_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_77_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2____boxed(lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_();
return v_res_79_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_80_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_);
v___x_85_ = lean_st_mk_ref(v___x_84_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2____boxed(lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(lean_object* v_catName_91_){
_start:
{
lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0));
v___x_93_ = 1;
v___x_94_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_91_, v___x_93_);
v___x_95_ = lean_string_append(v___x_92_, v___x_94_);
lean_dec_ref(v___x_94_);
v___x_96_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1));
v___x_97_ = lean_string_append(v___x_95_, v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined(lean_object* v_00_u03b1_99_, lean_object* v_catName_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_102_, lean_object* v_x_103_, lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
lean_object* v_ks_106_; lean_object* v_vs_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_131_; 
v_ks_106_ = lean_ctor_get(v_x_102_, 0);
v_vs_107_ = lean_ctor_get(v_x_102_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v_x_102_);
if (v_isSharedCheck_131_ == 0)
{
v___x_109_ = v_x_102_;
v_isShared_110_ = v_isSharedCheck_131_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_vs_107_);
lean_inc(v_ks_106_);
lean_dec(v_x_102_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_131_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_array_get_size(v_ks_106_);
v___x_112_ = lean_nat_dec_lt(v_x_103_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
lean_dec(v_x_103_);
v___x_113_ = lean_array_push(v_ks_106_, v_x_104_);
v___x_114_ = lean_array_push(v_vs_107_, v_x_105_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_114_);
lean_ctor_set(v___x_109_, 0, v___x_113_);
v___x_116_ = v___x_109_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
else
{
lean_object* v_k_x27_118_; uint8_t v___x_119_; 
v_k_x27_118_ = lean_array_fget_borrowed(v_ks_106_, v_x_103_);
v___x_119_ = lean_name_eq(v_x_104_, v_k_x27_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_121_; 
if (v_isShared_110_ == 0)
{
v___x_121_ = v___x_109_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_ks_106_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_vs_107_);
v___x_121_ = v_reuseFailAlloc_125_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_add(v_x_103_, v___x_122_);
lean_dec(v_x_103_);
v_x_102_ = v___x_121_;
v_x_103_ = v___x_123_;
goto _start;
}
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_126_ = lean_array_fset(v_ks_106_, v_x_103_, v_x_104_);
v___x_127_ = lean_array_fset(v_vs_107_, v_x_103_, v_x_105_);
lean_dec(v_x_103_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_127_);
lean_ctor_set(v___x_109_, 0, v___x_126_);
v___x_129_ = v___x_109_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(lean_object* v_n_132_, lean_object* v_k_133_, lean_object* v_v_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_n_132_, v___x_135_, v_k_133_, v_v_134_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(lean_object* v_x_138_, size_t v_x_139_, size_t v_x_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_es_143_; size_t v___x_144_; size_t v___x_145_; lean_object* v_j_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_es_143_ = lean_ctor_get(v_x_138_, 0);
v___x_144_ = ((size_t)31ULL);
v___x_145_ = lean_usize_land(v_x_139_, v___x_144_);
v_j_146_ = lean_usize_to_nat(v___x_145_);
v___x_147_ = lean_array_get_size(v_es_143_);
v___x_148_ = lean_nat_dec_lt(v_j_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_dec(v_j_146_);
lean_dec(v_x_142_);
lean_dec(v_x_141_);
return v_x_138_;
}
else
{
lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_187_; 
lean_inc_ref(v_es_143_);
v_isSharedCheck_187_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v_x_138_, 0);
lean_dec(v_unused_188_);
v___x_150_ = v_x_138_;
v_isShared_151_ = v_isSharedCheck_187_;
goto v_resetjp_149_;
}
else
{
lean_dec(v_x_138_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_187_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v_v_152_; lean_object* v___x_153_; lean_object* v_xs_x27_154_; lean_object* v___y_156_; 
v_v_152_ = lean_array_fget(v_es_143_, v_j_146_);
v___x_153_ = lean_box(0);
v_xs_x27_154_ = lean_array_fset(v_es_143_, v_j_146_, v___x_153_);
switch(lean_obj_tag(v_v_152_))
{
case 0:
{
lean_object* v_key_161_; lean_object* v_val_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_172_; 
v_key_161_ = lean_ctor_get(v_v_152_, 0);
v_val_162_ = lean_ctor_get(v_v_152_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_v_152_);
if (v_isSharedCheck_172_ == 0)
{
v___x_164_ = v_v_152_;
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_val_162_);
lean_inc(v_key_161_);
lean_dec(v_v_152_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
uint8_t v___x_166_; 
v___x_166_ = lean_name_eq(v_x_141_, v_key_161_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_del_object(v___x_164_);
v___x_167_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_161_, v_val_162_, v_x_141_, v_x_142_);
v___x_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
v___y_156_ = v___x_168_;
goto v___jp_155_;
}
else
{
lean_object* v___x_170_; 
lean_dec(v_val_162_);
lean_dec(v_key_161_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v_x_142_);
lean_ctor_set(v___x_164_, 0, v_x_141_);
v___x_170_ = v___x_164_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_x_141_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_x_142_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
v___y_156_ = v___x_170_;
goto v___jp_155_;
}
}
}
}
case 1:
{
lean_object* v_node_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_185_; 
v_node_173_ = lean_ctor_get(v_v_152_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_v_152_);
if (v_isSharedCheck_185_ == 0)
{
v___x_175_ = v_v_152_;
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_node_173_);
lean_dec(v_v_152_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; size_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_177_ = ((size_t)5ULL);
v___x_178_ = lean_usize_shift_right(v_x_139_, v___x_177_);
v___x_179_ = ((size_t)1ULL);
v___x_180_ = lean_usize_add(v_x_140_, v___x_179_);
v___x_181_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_node_173_, v___x_178_, v___x_180_, v_x_141_, v_x_142_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_181_);
v___x_183_ = v___x_175_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
v___y_156_ = v___x_183_;
goto v___jp_155_;
}
}
}
default: 
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_x_141_);
lean_ctor_set(v___x_186_, 1, v_x_142_);
v___y_156_ = v___x_186_;
goto v___jp_155_;
}
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_157_ = lean_array_fset(v_xs_x27_154_, v_j_146_, v___y_156_);
lean_dec(v_j_146_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_157_);
v___x_159_ = v___x_150_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
else
{
lean_object* v_ks_189_; lean_object* v_vs_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_208_; 
v_ks_189_ = lean_ctor_get(v_x_138_, 0);
v_vs_190_ = lean_ctor_get(v_x_138_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_208_ == 0)
{
v___x_192_ = v_x_138_;
v_isShared_193_ = v_isSharedCheck_208_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_vs_190_);
lean_inc(v_ks_189_);
lean_dec(v_x_138_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_208_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_ks_189_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_vs_190_);
v___x_195_ = v_reuseFailAlloc_207_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v_newNode_196_; size_t v___x_197_; uint8_t v___x_198_; 
v_newNode_196_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v___x_195_, v_x_141_, v_x_142_);
v___x_197_ = ((size_t)7ULL);
v___x_198_ = lean_usize_dec_le(v___x_197_, v_x_140_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_199_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_196_);
v___x_200_ = lean_unsigned_to_nat(4u);
v___x_201_ = lean_nat_dec_lt(v___x_199_, v___x_200_);
lean_dec(v___x_199_);
if (v___x_201_ == 0)
{
lean_object* v_ks_202_; lean_object* v_vs_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_ks_202_ = lean_ctor_get(v_newNode_196_, 0);
lean_inc_ref(v_ks_202_);
v_vs_203_ = lean_ctor_get(v_newNode_196_, 1);
lean_inc_ref(v_vs_203_);
lean_dec_ref(v_newNode_196_);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0);
v___x_206_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_x_140_, v_ks_202_, v_vs_203_, v___x_204_, v___x_205_);
lean_dec_ref(v_vs_203_);
lean_dec_ref(v_ks_202_);
return v___x_206_;
}
else
{
return v_newNode_196_;
}
}
else
{
return v_newNode_196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(size_t v_depth_209_, lean_object* v_keys_210_, lean_object* v_vals_211_, lean_object* v_i_212_, lean_object* v_entries_213_){
_start:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_array_get_size(v_keys_210_);
v___x_215_ = lean_nat_dec_lt(v_i_212_, v___x_214_);
if (v___x_215_ == 0)
{
lean_dec(v_i_212_);
return v_entries_213_;
}
else
{
lean_object* v_k_216_; lean_object* v_v_217_; uint64_t v___y_219_; 
v_k_216_ = lean_array_fget_borrowed(v_keys_210_, v_i_212_);
v_v_217_ = lean_array_fget_borrowed(v_vals_211_, v_i_212_);
if (lean_obj_tag(v_k_216_) == 0)
{
uint64_t v___x_230_; 
v___x_230_ = 1723ULL;
v___y_219_ = v___x_230_;
goto v___jp_218_;
}
else
{
uint64_t v_hash_231_; 
v_hash_231_ = lean_ctor_get_uint64(v_k_216_, sizeof(void*)*2);
v___y_219_ = v_hash_231_;
goto v___jp_218_;
}
v___jp_218_:
{
size_t v_h_220_; size_t v___x_221_; lean_object* v___x_222_; size_t v___x_223_; size_t v___x_224_; size_t v___x_225_; size_t v_h_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_h_220_ = lean_uint64_to_usize(v___y_219_);
v___x_221_ = ((size_t)5ULL);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = ((size_t)1ULL);
v___x_224_ = lean_usize_sub(v_depth_209_, v___x_223_);
v___x_225_ = lean_usize_mul(v___x_221_, v___x_224_);
v_h_226_ = lean_usize_shift_right(v_h_220_, v___x_225_);
v___x_227_ = lean_nat_add(v_i_212_, v___x_222_);
lean_dec(v_i_212_);
lean_inc(v_v_217_);
lean_inc(v_k_216_);
v___x_228_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_entries_213_, v_h_226_, v_depth_209_, v_k_216_, v_v_217_);
v_i_212_ = v___x_227_;
v_entries_213_ = v___x_228_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_232_, lean_object* v_keys_233_, lean_object* v_vals_234_, lean_object* v_i_235_, lean_object* v_entries_236_){
_start:
{
size_t v_depth_boxed_237_; lean_object* v_res_238_; 
v_depth_boxed_237_ = lean_unbox_usize(v_depth_232_);
lean_dec(v_depth_232_);
v_res_238_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_boxed_237_, v_keys_233_, v_vals_234_, v_i_235_, v_entries_236_);
lean_dec_ref(v_vals_234_);
lean_dec_ref(v_keys_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
size_t v_x_523__boxed_244_; size_t v_x_524__boxed_245_; lean_object* v_res_246_; 
v_x_523__boxed_244_ = lean_unbox_usize(v_x_240_);
lean_dec(v_x_240_);
v_x_524__boxed_245_ = lean_unbox_usize(v_x_241_);
lean_dec(v_x_241_);
v_res_246_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_239_, v_x_523__boxed_244_, v_x_524__boxed_245_, v_x_242_, v_x_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
uint64_t v___y_251_; 
if (lean_obj_tag(v_x_248_) == 0)
{
uint64_t v___x_255_; 
v___x_255_ = 1723ULL;
v___y_251_ = v___x_255_;
goto v___jp_250_;
}
else
{
uint64_t v_hash_256_; 
v_hash_256_ = lean_ctor_get_uint64(v_x_248_, sizeof(void*)*2);
v___y_251_ = v_hash_256_;
goto v___jp_250_;
}
v___jp_250_:
{
size_t v___x_252_; size_t v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_uint64_to_usize(v___y_251_);
v___x_253_ = ((size_t)1ULL);
v___x_254_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_247_, v___x_252_, v___x_253_, v_x_248_, v_x_249_);
return v___x_254_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_257_, lean_object* v_i_258_, lean_object* v_k_259_){
_start:
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_array_get_size(v_keys_257_);
v___x_261_ = lean_nat_dec_lt(v_i_258_, v___x_260_);
if (v___x_261_ == 0)
{
lean_dec(v_i_258_);
return v___x_261_;
}
else
{
lean_object* v_k_x27_262_; uint8_t v___x_263_; 
v_k_x27_262_ = lean_array_fget_borrowed(v_keys_257_, v_i_258_);
v___x_263_ = lean_name_eq(v_k_259_, v_k_x27_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_nat_add(v_i_258_, v___x_264_);
lean_dec(v_i_258_);
v_i_258_ = v___x_265_;
goto _start;
}
else
{
lean_dec(v_i_258_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_267_, lean_object* v_i_268_, lean_object* v_k_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_267_, v_i_268_, v_k_269_);
lean_dec(v_k_269_);
lean_dec_ref(v_keys_267_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(lean_object* v_x_272_, size_t v_x_273_, lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_272_) == 0)
{
lean_object* v_es_275_; lean_object* v___x_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v_j_279_; lean_object* v___x_280_; 
v_es_275_ = lean_ctor_get(v_x_272_, 0);
v___x_276_ = lean_box(2);
v___x_277_ = ((size_t)31ULL);
v___x_278_ = lean_usize_land(v_x_273_, v___x_277_);
v_j_279_ = lean_usize_to_nat(v___x_278_);
v___x_280_ = lean_array_get_borrowed(v___x_276_, v_es_275_, v_j_279_);
lean_dec(v_j_279_);
switch(lean_obj_tag(v___x_280_))
{
case 0:
{
lean_object* v_key_281_; uint8_t v___x_282_; 
v_key_281_ = lean_ctor_get(v___x_280_, 0);
v___x_282_ = lean_name_eq(v_x_274_, v_key_281_);
return v___x_282_;
}
case 1:
{
lean_object* v_node_283_; size_t v___x_284_; size_t v___x_285_; 
v_node_283_ = lean_ctor_get(v___x_280_, 0);
v___x_284_ = ((size_t)5ULL);
v___x_285_ = lean_usize_shift_right(v_x_273_, v___x_284_);
v_x_272_ = v_node_283_;
v_x_273_ = v___x_285_;
goto _start;
}
default: 
{
uint8_t v___x_287_; 
v___x_287_ = 0;
return v___x_287_;
}
}
}
else
{
lean_object* v_ks_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_ks_288_ = lean_ctor_get(v_x_272_, 0);
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_ks_288_, v___x_289_, v_x_274_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_291_, lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
size_t v_x_707__boxed_294_; uint8_t v_res_295_; lean_object* v_r_296_; 
v_x_707__boxed_294_ = lean_unbox_usize(v_x_292_);
lean_dec(v_x_292_);
v_res_295_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_291_, v_x_707__boxed_294_, v_x_293_);
lean_dec(v_x_293_);
lean_dec_ref(v_x_291_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
uint64_t v___y_300_; 
if (lean_obj_tag(v_x_298_) == 0)
{
uint64_t v___x_303_; 
v___x_303_ = 1723ULL;
v___y_300_ = v___x_303_;
goto v___jp_299_;
}
else
{
uint64_t v_hash_304_; 
v_hash_304_ = lean_ctor_get_uint64(v_x_298_, sizeof(void*)*2);
v___y_300_ = v_hash_304_;
goto v___jp_299_;
}
v___jp_299_:
{
size_t v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_uint64_to_usize(v___y_300_);
v___x_302_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_297_, v___x_301_, v_x_298_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg___boxed(lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
uint8_t v_res_307_; lean_object* v_r_308_; 
v_res_307_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_305_, v_x_306_);
lean_dec(v_x_306_);
lean_dec_ref(v_x_305_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object* v_categories_309_, lean_object* v_catName_310_, lean_object* v_initial_311_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_309_, v_catName_310_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_309_, v_catName_310_, v_initial_311_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; 
lean_dec_ref(v_initial_311_);
lean_dec_ref(v_categories_309_);
v___x_315_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_310_);
return v___x_315_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(lean_object* v_00_u03b2_316_, lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_317_, v_x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___boxed(lean_object* v_00_u03b2_320_, lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(v_00_u03b2_320_, v_x_321_, v_x_322_);
lean_dec(v_x_322_);
lean_dec_ref(v_x_321_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1(lean_object* v_00_u03b2_325_, lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_x_326_, v_x_327_, v_x_328_);
return v___x_329_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(lean_object* v_00_u03b2_330_, lean_object* v_x_331_, size_t v_x_332_, lean_object* v_x_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_331_, v_x_332_, v_x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_335_, lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
size_t v_x_788__boxed_339_; uint8_t v_res_340_; lean_object* v_r_341_; 
v_x_788__boxed_339_ = lean_unbox_usize(v_x_337_);
lean_dec(v_x_337_);
v_res_340_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(v_00_u03b2_335_, v_x_336_, v_x_788__boxed_339_, v_x_338_);
lean_dec(v_x_338_);
lean_dec_ref(v_x_336_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(lean_object* v_00_u03b2_342_, lean_object* v_x_343_, size_t v_x_344_, size_t v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_343_, v_x_344_, v_x_345_, v_x_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_349_, lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
size_t v_x_799__boxed_355_; size_t v_x_800__boxed_356_; lean_object* v_res_357_; 
v_x_799__boxed_355_ = lean_unbox_usize(v_x_351_);
lean_dec(v_x_351_);
v_x_800__boxed_356_ = lean_unbox_usize(v_x_352_);
lean_dec(v_x_352_);
v_res_357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(v_00_u03b2_349_, v_x_350_, v_x_799__boxed_355_, v_x_800__boxed_356_, v_x_353_, v_x_354_);
return v_res_357_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_358_, lean_object* v_keys_359_, lean_object* v_vals_360_, lean_object* v_heq_361_, lean_object* v_i_362_, lean_object* v_k_363_){
_start:
{
uint8_t v___x_364_; 
v___x_364_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_359_, v_i_362_, v_k_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_365_, lean_object* v_keys_366_, lean_object* v_vals_367_, lean_object* v_heq_368_, lean_object* v_i_369_, lean_object* v_k_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(v_00_u03b2_365_, v_keys_366_, v_vals_367_, v_heq_368_, v_i_369_, v_k_370_);
lean_dec(v_k_370_);
lean_dec_ref(v_vals_367_);
lean_dec_ref(v_keys_366_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_373_, lean_object* v_n_374_, lean_object* v_k_375_, lean_object* v_v_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v_n_374_, v_k_375_, v_v_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_378_, size_t v_depth_379_, lean_object* v_keys_380_, lean_object* v_vals_381_, lean_object* v_heq_382_, lean_object* v_i_383_, lean_object* v_entries_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_379_, v_keys_380_, v_vals_381_, v_i_383_, v_entries_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_386_, lean_object* v_depth_387_, lean_object* v_keys_388_, lean_object* v_vals_389_, lean_object* v_heq_390_, lean_object* v_i_391_, lean_object* v_entries_392_){
_start:
{
size_t v_depth_boxed_393_; lean_object* v_res_394_; 
v_depth_boxed_393_ = lean_unbox_usize(v_depth_387_);
lean_dec(v_depth_387_);
v_res_394_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(v_00_u03b2_386_, v_depth_boxed_393_, v_keys_388_, v_vals_389_, v_heq_390_, v_i_391_, v_entries_392_);
lean_dec_ref(v_vals_389_);
lean_dec_ref(v_keys_388_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_x_396_, v_x_397_, v_x_398_, v_x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(lean_object* v_e_401_){
_start:
{
if (lean_obj_tag(v_e_401_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_411_; 
v_a_403_ = lean_ctor_get(v_e_401_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_e_401_);
if (v_isSharedCheck_411_ == 0)
{
v___x_405_ = v_e_401_;
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v_e_401_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = lean_mk_io_user_error(v_a_403_);
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 1);
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_a_412_ = lean_ctor_get(v_e_401_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_e_401_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v_e_401_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v_e_401_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 0);
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg___boxed(lean_object* v_e_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(lean_object* v_00_u03b1_423_, lean_object* v_e_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___boxed(lean_object* v_00_u03b1_427_, lean_object* v_e_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(v_00_u03b1_427_, v_e_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object* v_catName_434_, lean_object* v_declName_435_, uint8_t v_behavior_436_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_438_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_439_ = lean_st_ref_get(v___x_438_);
v___x_440_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_441_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_442_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_442_, 0, v_declName_435_);
lean_ctor_set(v___x_442_, 1, v___x_440_);
lean_ctor_set(v___x_442_, 2, v___x_441_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*3, v_behavior_436_);
v___x_443_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(v___x_439_, v_catName_434_, v___x_442_);
v___x_444_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_443_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_454_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_454_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_454_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_454_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_449_ = lean_st_ref_swap(v___x_438_, v_a_445_);
lean_dec(v___x_449_);
v___x_450_ = lean_box(0);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_450_);
v___x_452_ = v___x_447_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_a_455_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_444_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_444_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object* v_catName_463_, lean_object* v_declName_464_, lean_object* v_behavior_465_, lean_object* v_a_466_){
_start:
{
uint8_t v_behavior_boxed_467_; lean_object* v_res_468_; 
v_behavior_boxed_467_ = lean_unbox(v_behavior_465_);
v_res_468_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_463_, v_declName_464_, v_behavior_boxed_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(lean_object* v_x_469_){
_start:
{
switch(lean_obj_tag(v_x_469_))
{
case 0:
{
lean_object* v___x_470_; 
v___x_470_ = lean_unsigned_to_nat(0u);
return v___x_470_;
}
case 1:
{
lean_object* v___x_471_; 
v___x_471_ = lean_unsigned_to_nat(1u);
return v___x_471_;
}
case 2:
{
lean_object* v___x_472_; 
v___x_472_ = lean_unsigned_to_nat(2u);
return v___x_472_;
}
default: 
{
lean_object* v___x_473_; 
v___x_473_ = lean_unsigned_to_nat(3u);
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___boxed(lean_object* v_x_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(v_x_474_);
lean_dec_ref(v_x_474_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(lean_object* v_t_476_, lean_object* v_k_477_){
_start:
{
switch(lean_obj_tag(v_t_476_))
{
case 0:
{
lean_object* v_val_478_; lean_object* v___x_479_; 
v_val_478_ = lean_ctor_get(v_t_476_, 0);
lean_inc_ref(v_val_478_);
lean_dec_ref_known(v_t_476_, 1);
v___x_479_ = lean_apply_1(v_k_477_, v_val_478_);
return v___x_479_;
}
case 1:
{
lean_object* v_val_480_; lean_object* v___x_481_; 
v_val_480_ = lean_ctor_get(v_t_476_, 0);
lean_inc(v_val_480_);
lean_dec_ref_known(v_t_476_, 1);
v___x_481_ = lean_apply_1(v_k_477_, v_val_480_);
return v___x_481_;
}
case 2:
{
lean_object* v_catName_482_; lean_object* v_declName_483_; uint8_t v_behavior_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_catName_482_ = lean_ctor_get(v_t_476_, 0);
lean_inc(v_catName_482_);
v_declName_483_ = lean_ctor_get(v_t_476_, 1);
lean_inc(v_declName_483_);
v_behavior_484_ = lean_ctor_get_uint8(v_t_476_, sizeof(void*)*2);
lean_dec_ref_known(v_t_476_, 2);
v___x_485_ = lean_box(v_behavior_484_);
v___x_486_ = lean_apply_3(v_k_477_, v_catName_482_, v_declName_483_, v___x_485_);
return v___x_486_;
}
default: 
{
lean_object* v_catName_487_; lean_object* v_declName_488_; lean_object* v_prio_489_; lean_object* v___x_490_; 
v_catName_487_ = lean_ctor_get(v_t_476_, 0);
lean_inc(v_catName_487_);
v_declName_488_ = lean_ctor_get(v_t_476_, 1);
lean_inc(v_declName_488_);
v_prio_489_ = lean_ctor_get(v_t_476_, 2);
lean_inc(v_prio_489_);
lean_dec_ref_known(v_t_476_, 3);
v___x_490_ = lean_apply_3(v_k_477_, v_catName_487_, v_declName_488_, v_prio_489_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(lean_object* v_motive_491_, lean_object* v_ctorIdx_492_, lean_object* v_t_493_, lean_object* v_h_494_, lean_object* v_k_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_493_, v_k_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___boxed(lean_object* v_motive_497_, lean_object* v_ctorIdx_498_, lean_object* v_t_499_, lean_object* v_h_500_, lean_object* v_k_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(v_motive_497_, v_ctorIdx_498_, v_t_499_, v_h_500_, v_k_501_);
lean_dec(v_ctorIdx_498_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim___redArg(lean_object* v_t_503_, lean_object* v_token_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_503_, v_token_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim(lean_object* v_motive_506_, lean_object* v_t_507_, lean_object* v_h_508_, lean_object* v_token_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_507_, v_token_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim___redArg(lean_object* v_t_511_, lean_object* v_kind_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_511_, v_kind_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim(lean_object* v_motive_514_, lean_object* v_t_515_, lean_object* v_h_516_, lean_object* v_kind_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_515_, v_kind_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim___redArg(lean_object* v_t_519_, lean_object* v_category_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_519_, v_category_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim(lean_object* v_motive_522_, lean_object* v_t_523_, lean_object* v_h_524_, lean_object* v_category_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_523_, v_category_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim___redArg(lean_object* v_t_527_, lean_object* v_parser_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_527_, v_parser_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim(lean_object* v_motive_530_, lean_object* v_t_531_, lean_object* v_h_532_, lean_object* v_parser_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_531_, v_parser_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx(lean_object* v_x_540_){
_start:
{
switch(lean_obj_tag(v_x_540_))
{
case 0:
{
lean_object* v___x_541_; 
v___x_541_ = lean_unsigned_to_nat(0u);
return v___x_541_;
}
case 1:
{
lean_object* v___x_542_; 
v___x_542_ = lean_unsigned_to_nat(1u);
return v___x_542_;
}
case 2:
{
lean_object* v___x_543_; 
v___x_543_ = lean_unsigned_to_nat(2u);
return v___x_543_;
}
default: 
{
lean_object* v___x_544_; 
v___x_544_ = lean_unsigned_to_nat(3u);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___boxed(lean_object* v_x_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Parser_ParserExtension_Entry_ctorIdx(v_x_545_);
lean_dec_ref(v_x_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(lean_object* v_t_547_, lean_object* v_k_548_){
_start:
{
switch(lean_obj_tag(v_t_547_))
{
case 0:
{
lean_object* v_val_549_; lean_object* v___x_550_; 
v_val_549_ = lean_ctor_get(v_t_547_, 0);
lean_inc_ref(v_val_549_);
lean_dec_ref_known(v_t_547_, 1);
v___x_550_ = lean_apply_1(v_k_548_, v_val_549_);
return v___x_550_;
}
case 1:
{
lean_object* v_val_551_; lean_object* v___x_552_; 
v_val_551_ = lean_ctor_get(v_t_547_, 0);
lean_inc(v_val_551_);
lean_dec_ref_known(v_t_547_, 1);
v___x_552_ = lean_apply_1(v_k_548_, v_val_551_);
return v___x_552_;
}
case 2:
{
lean_object* v_catName_553_; lean_object* v_declName_554_; uint8_t v_behavior_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_catName_553_ = lean_ctor_get(v_t_547_, 0);
lean_inc(v_catName_553_);
v_declName_554_ = lean_ctor_get(v_t_547_, 1);
lean_inc(v_declName_554_);
v_behavior_555_ = lean_ctor_get_uint8(v_t_547_, sizeof(void*)*2);
lean_dec_ref_known(v_t_547_, 2);
v___x_556_ = lean_box(v_behavior_555_);
v___x_557_ = lean_apply_3(v_k_548_, v_catName_553_, v_declName_554_, v___x_556_);
return v___x_557_;
}
default: 
{
lean_object* v_catName_558_; lean_object* v_declName_559_; uint8_t v_leading_560_; lean_object* v_p_561_; lean_object* v_prio_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_catName_558_ = lean_ctor_get(v_t_547_, 0);
lean_inc(v_catName_558_);
v_declName_559_ = lean_ctor_get(v_t_547_, 1);
lean_inc(v_declName_559_);
v_leading_560_ = lean_ctor_get_uint8(v_t_547_, sizeof(void*)*4);
v_p_561_ = lean_ctor_get(v_t_547_, 2);
lean_inc_ref(v_p_561_);
v_prio_562_ = lean_ctor_get(v_t_547_, 3);
lean_inc(v_prio_562_);
lean_dec_ref_known(v_t_547_, 4);
v___x_563_ = lean_box(v_leading_560_);
v___x_564_ = lean_apply_5(v_k_548_, v_catName_558_, v_declName_559_, v___x_563_, v_p_561_, v_prio_562_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim(lean_object* v_motive_565_, lean_object* v_ctorIdx_566_, lean_object* v_t_567_, lean_object* v_h_568_, lean_object* v_k_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_567_, v_k_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___boxed(lean_object* v_motive_571_, lean_object* v_ctorIdx_572_, lean_object* v_t_573_, lean_object* v_h_574_, lean_object* v_k_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Parser_ParserExtension_Entry_ctorElim(v_motive_571_, v_ctorIdx_572_, v_t_573_, v_h_574_, v_k_575_);
lean_dec(v_ctorIdx_572_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim___redArg(lean_object* v_t_577_, lean_object* v_token_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_577_, v_token_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim(lean_object* v_motive_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_token_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_581_, v_token_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim___redArg(lean_object* v_t_585_, lean_object* v_kind_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_585_, v_kind_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim(lean_object* v_motive_588_, lean_object* v_t_589_, lean_object* v_h_590_, lean_object* v_kind_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_589_, v_kind_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim___redArg(lean_object* v_t_593_, lean_object* v_category_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_593_, v_category_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim(lean_object* v_motive_596_, lean_object* v_t_597_, lean_object* v_h_598_, lean_object* v_category_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_597_, v_category_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim___redArg(lean_object* v_t_601_, lean_object* v_parser_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_601_, v_parser_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim(lean_object* v_motive_604_, lean_object* v_t_605_, lean_object* v_h_606_, lean_object* v_parser_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_605_, v_parser_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object* v_x_613_){
_start:
{
switch(lean_obj_tag(v_x_613_))
{
case 0:
{
lean_object* v_val_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
v_val_614_ = lean_ctor_get(v_x_613_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_x_613_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v_x_613_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_val_614_);
lean_dec(v_x_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_val_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
case 1:
{
lean_object* v_val_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
v_val_622_ = lean_ctor_get(v_x_613_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_x_613_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v_x_613_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_val_622_);
lean_dec(v_x_613_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_val_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
case 2:
{
lean_object* v_catName_630_; lean_object* v_declName_631_; uint8_t v_behavior_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_catName_630_ = lean_ctor_get(v_x_613_, 0);
v_declName_631_ = lean_ctor_get(v_x_613_, 1);
v_behavior_632_ = lean_ctor_get_uint8(v_x_613_, sizeof(void*)*2);
v_isSharedCheck_639_ = !lean_is_exclusive(v_x_613_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v_x_613_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_declName_631_);
lean_inc(v_catName_630_);
lean_dec(v_x_613_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_catName_630_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_declName_631_);
lean_ctor_set_uint8(v_reuseFailAlloc_638_, sizeof(void*)*2, v_behavior_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
default: 
{
lean_object* v_catName_640_; lean_object* v_declName_641_; lean_object* v_prio_642_; lean_object* v___x_643_; 
v_catName_640_ = lean_ctor_get(v_x_613_, 0);
lean_inc(v_catName_640_);
v_declName_641_ = lean_ctor_get(v_x_613_, 1);
lean_inc(v_declName_641_);
v_prio_642_ = lean_ctor_get(v_x_613_, 3);
lean_inc(v_prio_642_);
lean_dec_ref_known(v_x_613_, 4);
v___x_643_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_643_, 0, v_catName_640_);
lean_ctor_set(v___x_643_, 1, v_declName_641_);
lean_ctor_set(v___x_643_, 2, v_prio_642_);
return v___x_643_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_645_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
lean_ctor_set(v___x_646_, 2, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default(void){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0, &l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0_once, _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState(void){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_650_ = l_Lean_Parser_builtinTokenTable;
v___x_651_ = lean_st_ref_get(v___x_650_);
v___x_652_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_653_ = lean_st_ref_get(v___x_652_);
v___x_654_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_655_ = lean_st_ref_get(v___x_654_);
v___x_656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_656_, 0, v___x_651_);
lean_ctor_set(v___x_656_, 1, v___x_653_);
lean_ctor_set(v___x_656_, 2, v___x_655_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object* v_tokens_663_, lean_object* v_tk_664_){
_start:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = ((lean_object*)(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0));
v___x_666_ = lean_string_dec_eq(v_tk_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Data_Trie_find_x3f___redArg(v_tokens_663_, v_tk_664_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
lean_inc_ref(v_tk_664_);
v___x_668_ = l_Lean_Data_Trie_insert___redArg(v_tokens_663_, v_tk_664_, v_tk_664_);
lean_dec_ref(v_tk_664_);
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
else
{
lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec_ref(v_tk_664_);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v___x_667_, 0);
lean_dec(v_unused_677_);
v___x_671_ = v___x_667_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_dec(v___x_667_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v_tokens_663_);
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_tokens_663_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
else
{
lean_object* v___x_678_; 
lean_dec_ref(v_tk_664_);
lean_dec_ref(v_tokens_663_);
v___x_678_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1));
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg(lean_object* v_catName_681_){
_start:
{
lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_682_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0));
v___x_683_ = 1;
v___x_684_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_681_, v___x_683_);
v___x_685_ = lean_string_append(v___x_682_, v___x_684_);
lean_dec_ref(v___x_684_);
v___x_686_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_687_ = lean_string_append(v___x_685_, v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object* v_00_u03b1_689_, lean_object* v_catName_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object* v_categories_694_, lean_object* v_catName_695_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__0));
v___x_697_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__1));
v___x_698_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_696_, v___x_697_, v_categories_694_, v_catName_695_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory___boxed(lean_object* v_categories_699_, lean_object* v_catName_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Parser_getCategory(v_categories_699_, v_catName_700_);
lean_dec_ref(v_categories_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(lean_object* v_as_703_){
_start:
{
lean_object* v___f_704_; lean_object* v___x_705_; 
v___f_704_ = ((lean_object*)(l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0));
v___x_705_ = l_List_eraseDupsBy___redArg(v___f_704_, v_as_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(lean_object* v_p_706_, lean_object* v_prio_707_, lean_object* v_x_708_, lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_709_) == 0)
{
lean_dec(v_prio_707_);
lean_dec_ref(v_p_706_);
return v_x_708_;
}
else
{
lean_object* v_head_710_; lean_object* v_tail_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_731_; 
v_head_710_ = lean_ctor_get(v_x_709_, 0);
v_tail_711_ = lean_ctor_get(v_x_709_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_709_);
if (v_isSharedCheck_731_ == 0)
{
v___x_713_ = v_x_709_;
v_isShared_714_ = v_isSharedCheck_731_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_tail_711_);
lean_inc(v_head_710_);
lean_dec(v_x_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_731_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_leadingTable_715_; lean_object* v_leadingParsers_716_; lean_object* v_trailingTable_717_; lean_object* v_trailingParsers_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_730_; 
v_leadingTable_715_ = lean_ctor_get(v_x_708_, 0);
v_leadingParsers_716_ = lean_ctor_get(v_x_708_, 1);
v_trailingTable_717_ = lean_ctor_get(v_x_708_, 2);
v_trailingParsers_718_ = lean_ctor_get(v_x_708_, 3);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_708_);
if (v_isSharedCheck_730_ == 0)
{
v___x_720_ = v_x_708_;
v_isShared_721_ = v_isSharedCheck_730_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_trailingParsers_718_);
lean_inc(v_trailingTable_717_);
lean_inc(v_leadingParsers_716_);
lean_inc(v_leadingTable_715_);
lean_dec(v_x_708_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_730_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
lean_inc(v_prio_707_);
lean_inc_ref(v_p_706_);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 0);
lean_ctor_set(v___x_713_, 1, v_prio_707_);
lean_ctor_set(v___x_713_, 0, v_p_706_);
v___x_723_ = v___x_713_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_p_706_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_prio_707_);
v___x_723_ = v_reuseFailAlloc_729_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = l_Lean_Parser_TokenMap_insert___redArg(v_leadingTable_715_, v_head_710_, v___x_723_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_724_);
v___x_726_ = v___x_720_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_leadingParsers_716_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_trailingTable_717_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_trailingParsers_718_);
v___x_726_ = v_reuseFailAlloc_728_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
v_x_708_ = v___x_726_;
v_x_709_ = v_tail_711_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_732_, lean_object* v_vals_733_, lean_object* v_i_734_, lean_object* v_k_735_){
_start:
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_array_get_size(v_keys_732_);
v___x_737_ = lean_nat_dec_lt(v_i_734_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
lean_dec(v_i_734_);
v___x_738_ = lean_box(0);
return v___x_738_;
}
else
{
lean_object* v_k_x27_739_; uint8_t v___x_740_; 
v_k_x27_739_ = lean_array_fget_borrowed(v_keys_732_, v_i_734_);
v___x_740_ = lean_name_eq(v_k_735_, v_k_x27_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_nat_add(v_i_734_, v___x_741_);
lean_dec(v_i_734_);
v_i_734_ = v___x_742_;
goto _start;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_array_fget_borrowed(v_vals_733_, v_i_734_);
lean_dec(v_i_734_);
lean_inc(v___x_744_);
v___x_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_746_, lean_object* v_vals_747_, lean_object* v_i_748_, lean_object* v_k_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_746_, v_vals_747_, v_i_748_, v_k_749_);
lean_dec(v_k_749_);
lean_dec_ref(v_vals_747_);
lean_dec_ref(v_keys_746_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(lean_object* v_x_751_, size_t v_x_752_, lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
lean_object* v_es_754_; lean_object* v___x_755_; size_t v___x_756_; size_t v___x_757_; lean_object* v_j_758_; lean_object* v___x_759_; 
v_es_754_ = lean_ctor_get(v_x_751_, 0);
v___x_755_ = lean_box(2);
v___x_756_ = ((size_t)31ULL);
v___x_757_ = lean_usize_land(v_x_752_, v___x_756_);
v_j_758_ = lean_usize_to_nat(v___x_757_);
v___x_759_ = lean_array_get_borrowed(v___x_755_, v_es_754_, v_j_758_);
lean_dec(v_j_758_);
switch(lean_obj_tag(v___x_759_))
{
case 0:
{
lean_object* v_key_760_; lean_object* v_val_761_; uint8_t v___x_762_; 
v_key_760_ = lean_ctor_get(v___x_759_, 0);
v_val_761_ = lean_ctor_get(v___x_759_, 1);
v___x_762_ = lean_name_eq(v_x_753_, v_key_760_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
v___x_763_ = lean_box(0);
return v___x_763_;
}
else
{
lean_object* v___x_764_; 
lean_inc(v_val_761_);
v___x_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_764_, 0, v_val_761_);
return v___x_764_;
}
}
case 1:
{
lean_object* v_node_765_; size_t v___x_766_; size_t v___x_767_; 
v_node_765_ = lean_ctor_get(v___x_759_, 0);
v___x_766_ = ((size_t)5ULL);
v___x_767_ = lean_usize_shift_right(v_x_752_, v___x_766_);
v_x_751_ = v_node_765_;
v_x_752_ = v___x_767_;
goto _start;
}
default: 
{
lean_object* v___x_769_; 
v___x_769_ = lean_box(0);
return v___x_769_;
}
}
}
else
{
lean_object* v_ks_770_; lean_object* v_vs_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_ks_770_ = lean_ctor_get(v_x_751_, 0);
v_vs_771_ = lean_ctor_get(v_x_751_, 1);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_ks_770_, v_vs_771_, v___x_772_, v_x_753_);
return v___x_773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg___boxed(lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
size_t v_x_490__boxed_777_; lean_object* v_res_778_; 
v_x_490__boxed_777_ = lean_unbox_usize(v_x_775_);
lean_dec(v_x_775_);
v_res_778_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_774_, v_x_490__boxed_777_, v_x_776_);
lean_dec(v_x_776_);
lean_dec_ref(v_x_774_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
uint64_t v___y_782_; 
if (lean_obj_tag(v_x_780_) == 0)
{
uint64_t v___x_785_; 
v___x_785_ = 1723ULL;
v___y_782_ = v___x_785_;
goto v___jp_781_;
}
else
{
uint64_t v_hash_786_; 
v_hash_786_ = lean_ctor_get_uint64(v_x_780_, sizeof(void*)*2);
v___y_782_ = v_hash_786_;
goto v___jp_781_;
}
v___jp_781_:
{
size_t v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_uint64_to_usize(v___y_782_);
v___x_784_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_779_, v___x_783_, v_x_780_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg___boxed(lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_787_, v_x_788_);
lean_dec(v_x_788_);
lean_dec_ref(v_x_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
if (lean_obj_tag(v_a_790_) == 0)
{
lean_object* v___x_792_; 
v___x_792_ = l_List_reverse___redArg(v_a_791_);
return v___x_792_;
}
else
{
lean_object* v_head_793_; lean_object* v_tail_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_804_; 
v_head_793_ = lean_ctor_get(v_a_790_, 0);
v_tail_794_ = lean_ctor_get(v_a_790_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_a_790_);
if (v_isSharedCheck_804_ == 0)
{
v___x_796_ = v_a_790_;
v_isShared_797_ = v_isSharedCheck_804_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_tail_794_);
lean_inc(v_head_793_);
lean_dec(v_a_790_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_804_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_798_ = lean_box(0);
v___x_799_ = l_Lean_Name_str___override(v___x_798_, v_head_793_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v_a_791_);
lean_ctor_set(v___x_796_, 0, v___x_799_);
v___x_801_ = v___x_796_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_a_791_);
v___x_801_ = v_reuseFailAlloc_803_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
v_a_790_ = v_tail_794_;
v_a_791_ = v___x_801_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object* v_categories_805_, lean_object* v_catName_806_, lean_object* v_declName_807_, lean_object* v_p_808_, lean_object* v_prio_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_805_, v_catName_806_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; 
lean_dec(v_prio_809_);
lean_dec_ref(v_p_808_);
lean_dec(v_declName_807_);
lean_dec_ref(v_categories_805_);
v___x_811_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_806_);
return v___x_811_;
}
else
{
lean_object* v_val_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_858_; 
v_val_812_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_858_ == 0)
{
v___x_814_ = v___x_810_;
v_isShared_815_ = v_isSharedCheck_858_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_val_812_);
lean_dec(v___x_810_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_858_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_info_816_; lean_object* v_declName_817_; lean_object* v_kinds_818_; lean_object* v_tables_819_; uint8_t v_behavior_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_857_; 
v_info_816_ = lean_ctor_get(v_p_808_, 0);
v_declName_817_ = lean_ctor_get(v_val_812_, 0);
v_kinds_818_ = lean_ctor_get(v_val_812_, 1);
v_tables_819_ = lean_ctor_get(v_val_812_, 2);
v_behavior_820_ = lean_ctor_get_uint8(v_val_812_, sizeof(void*)*3);
v_isSharedCheck_857_ = !lean_is_exclusive(v_val_812_);
if (v_isSharedCheck_857_ == 0)
{
v___x_822_ = v_val_812_;
v_isShared_823_ = v_isSharedCheck_857_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_tables_819_);
lean_inc(v_kinds_818_);
lean_inc(v_declName_817_);
lean_dec(v_val_812_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_857_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_firstTokens_824_; lean_object* v_kinds_825_; lean_object* v_tks_827_; 
v_firstTokens_824_ = lean_ctor_get(v_info_816_, 2);
v_kinds_825_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_818_, v_declName_807_);
switch(lean_obj_tag(v_firstTokens_824_))
{
case 2:
{
lean_object* v_a_839_; 
v_a_839_ = lean_ctor_get(v_firstTokens_824_, 0);
lean_inc(v_a_839_);
v_tks_827_ = v_a_839_;
goto v___jp_826_;
}
case 3:
{
lean_object* v_a_840_; 
v_a_840_ = lean_ctor_get(v_firstTokens_824_, 0);
lean_inc(v_a_840_);
v_tks_827_ = v_a_840_;
goto v___jp_826_;
}
default: 
{
lean_object* v_leadingTable_841_; lean_object* v_leadingParsers_842_; lean_object* v_trailingTable_843_; lean_object* v_trailingParsers_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_856_; 
lean_del_object(v___x_822_);
lean_del_object(v___x_814_);
v_leadingTable_841_ = lean_ctor_get(v_tables_819_, 0);
v_leadingParsers_842_ = lean_ctor_get(v_tables_819_, 1);
v_trailingTable_843_ = lean_ctor_get(v_tables_819_, 2);
v_trailingParsers_844_ = lean_ctor_get(v_tables_819_, 3);
v_isSharedCheck_856_ = !lean_is_exclusive(v_tables_819_);
if (v_isSharedCheck_856_ == 0)
{
v___x_846_ = v_tables_819_;
v_isShared_847_ = v_isSharedCheck_856_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_trailingParsers_844_);
lean_inc(v_trailingTable_843_);
lean_inc(v_leadingParsers_842_);
lean_inc(v_leadingTable_841_);
lean_dec(v_tables_819_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_856_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v_tables_851_; 
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_p_808_);
lean_ctor_set(v___x_848_, 1, v_prio_809_);
v___x_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v_leadingParsers_842_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v___x_849_);
v_tables_851_ = v___x_846_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_leadingTable_841_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_trailingTable_843_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v_trailingParsers_844_);
v_tables_851_ = v_reuseFailAlloc_855_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_852_, 0, v_declName_817_);
lean_ctor_set(v___x_852_, 1, v_kinds_825_);
lean_ctor_set(v___x_852_, 2, v_tables_851_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*3, v_behavior_820_);
v___x_853_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_805_, v_catName_806_, v___x_852_);
v___x_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
}
}
}
v___jp_826_:
{
lean_object* v___x_828_; lean_object* v_tks_829_; lean_object* v___x_830_; lean_object* v_tables_831_; lean_object* v___x_833_; 
v___x_828_ = lean_box(0);
v_tks_829_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_827_, v___x_828_);
v___x_830_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_829_);
v_tables_831_ = l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(v_p_808_, v_prio_809_, v_tables_819_, v___x_830_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 2, v_tables_831_);
lean_ctor_set(v___x_822_, 1, v_kinds_825_);
v___x_833_ = v___x_822_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_declName_817_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_kinds_825_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_tables_831_);
lean_ctor_set_uint8(v_reuseFailAlloc_838_, sizeof(void*)*3, v_behavior_820_);
v___x_833_ = v_reuseFailAlloc_838_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_805_, v_catName_806_, v___x_833_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_834_);
v___x_836_ = v___x_814_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___boxed(lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(v_00_u03b2_863_, v_x_864_, v_x_865_);
lean_dec(v_x_865_);
lean_dec_ref(v_x_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, size_t v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_868_, v_x_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___boxed(lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
size_t v_x_659__boxed_876_; lean_object* v_res_877_; 
v_x_659__boxed_876_ = lean_unbox_usize(v_x_874_);
lean_dec(v_x_874_);
v_res_877_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(v_00_u03b2_872_, v_x_873_, v_x_659__boxed_876_, v_x_875_);
lean_dec(v_x_875_);
lean_dec_ref(v_x_873_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_878_, lean_object* v_keys_879_, lean_object* v_vals_880_, lean_object* v_heq_881_, lean_object* v_i_882_, lean_object* v_k_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_879_, v_vals_880_, v_i_882_, v_k_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_885_, lean_object* v_keys_886_, lean_object* v_vals_887_, lean_object* v_heq_888_, lean_object* v_i_889_, lean_object* v_k_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(v_00_u03b2_885_, v_keys_886_, v_vals_887_, v_heq_888_, v_i_889_, v_k_890_);
lean_dec(v_k_890_);
lean_dec_ref(v_vals_887_);
lean_dec_ref(v_keys_886_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(lean_object* v_p_892_, lean_object* v_prio_893_, lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_x_895_) == 0)
{
lean_dec(v_prio_893_);
lean_dec_ref(v_p_892_);
return v_x_894_;
}
else
{
lean_object* v_head_896_; lean_object* v_tail_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_917_; 
v_head_896_ = lean_ctor_get(v_x_895_, 0);
v_tail_897_ = lean_ctor_get(v_x_895_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_x_895_);
if (v_isSharedCheck_917_ == 0)
{
v___x_899_ = v_x_895_;
v_isShared_900_ = v_isSharedCheck_917_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_tail_897_);
lean_inc(v_head_896_);
lean_dec(v_x_895_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_917_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_leadingTable_901_; lean_object* v_leadingParsers_902_; lean_object* v_trailingTable_903_; lean_object* v_trailingParsers_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_916_; 
v_leadingTable_901_ = lean_ctor_get(v_x_894_, 0);
v_leadingParsers_902_ = lean_ctor_get(v_x_894_, 1);
v_trailingTable_903_ = lean_ctor_get(v_x_894_, 2);
v_trailingParsers_904_ = lean_ctor_get(v_x_894_, 3);
v_isSharedCheck_916_ = !lean_is_exclusive(v_x_894_);
if (v_isSharedCheck_916_ == 0)
{
v___x_906_ = v_x_894_;
v_isShared_907_ = v_isSharedCheck_916_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_trailingParsers_904_);
lean_inc(v_trailingTable_903_);
lean_inc(v_leadingParsers_902_);
lean_inc(v_leadingTable_901_);
lean_dec(v_x_894_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_916_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
lean_inc(v_prio_893_);
lean_inc_ref(v_p_892_);
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 0);
lean_ctor_set(v___x_899_, 1, v_prio_893_);
lean_ctor_set(v___x_899_, 0, v_p_892_);
v___x_909_ = v___x_899_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_p_892_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_prio_893_);
v___x_909_ = v_reuseFailAlloc_915_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = l_Lean_Parser_TokenMap_insert___redArg(v_trailingTable_903_, v_head_896_, v___x_909_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 2, v___x_910_);
v___x_912_ = v___x_906_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_leadingTable_901_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_leadingParsers_902_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_trailingParsers_904_);
v___x_912_ = v_reuseFailAlloc_914_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
v_x_894_ = v___x_912_;
v_x_895_ = v_tail_897_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object* v_tables_918_, lean_object* v_p_919_, lean_object* v_prio_920_){
_start:
{
lean_object* v_tks_922_; lean_object* v_info_927_; lean_object* v_firstTokens_928_; 
v_info_927_ = lean_ctor_get(v_p_919_, 0);
v_firstTokens_928_ = lean_ctor_get(v_info_927_, 2);
switch(lean_obj_tag(v_firstTokens_928_))
{
case 2:
{
lean_object* v_a_929_; 
v_a_929_ = lean_ctor_get(v_firstTokens_928_, 0);
lean_inc(v_a_929_);
v_tks_922_ = v_a_929_;
goto v___jp_921_;
}
case 3:
{
lean_object* v_a_930_; 
v_a_930_ = lean_ctor_get(v_firstTokens_928_, 0);
lean_inc(v_a_930_);
v_tks_922_ = v_a_930_;
goto v___jp_921_;
}
default: 
{
lean_object* v_leadingTable_931_; lean_object* v_leadingParsers_932_; lean_object* v_trailingTable_933_; lean_object* v_trailingParsers_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_943_; 
v_leadingTable_931_ = lean_ctor_get(v_tables_918_, 0);
v_leadingParsers_932_ = lean_ctor_get(v_tables_918_, 1);
v_trailingTable_933_ = lean_ctor_get(v_tables_918_, 2);
v_trailingParsers_934_ = lean_ctor_get(v_tables_918_, 3);
v_isSharedCheck_943_ = !lean_is_exclusive(v_tables_918_);
if (v_isSharedCheck_943_ == 0)
{
v___x_936_ = v_tables_918_;
v_isShared_937_ = v_isSharedCheck_943_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_trailingParsers_934_);
lean_inc(v_trailingTable_933_);
lean_inc(v_leadingParsers_932_);
lean_inc(v_leadingTable_931_);
lean_dec(v_tables_918_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_943_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_p_919_);
lean_ctor_set(v___x_938_, 1, v_prio_920_);
v___x_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v_trailingParsers_934_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 3, v___x_939_);
v___x_941_ = v___x_936_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_leadingTable_931_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_leadingParsers_932_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_trailingTable_933_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
v___jp_921_:
{
lean_object* v___x_923_; lean_object* v_tks_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_923_ = lean_box(0);
v_tks_924_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_922_, v___x_923_);
v___x_925_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_924_);
v___x_926_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(v_p_919_, v_prio_920_, v_tables_918_, v___x_925_);
return v___x_926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object* v_categories_944_, lean_object* v_catName_945_, lean_object* v_declName_946_, lean_object* v_p_947_, lean_object* v_prio_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_944_, v_catName_945_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v___x_950_; 
lean_dec(v_prio_948_);
lean_dec_ref(v_p_947_);
lean_dec(v_declName_946_);
lean_dec_ref(v_categories_944_);
v___x_950_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_945_);
return v___x_950_;
}
else
{
lean_object* v_val_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_972_; 
v_val_951_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_972_ == 0)
{
v___x_953_ = v___x_949_;
v_isShared_954_ = v_isSharedCheck_972_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_val_951_);
lean_dec(v___x_949_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_972_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_declName_955_; lean_object* v_kinds_956_; lean_object* v_tables_957_; uint8_t v_behavior_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_971_; 
v_declName_955_ = lean_ctor_get(v_val_951_, 0);
v_kinds_956_ = lean_ctor_get(v_val_951_, 1);
v_tables_957_ = lean_ctor_get(v_val_951_, 2);
v_behavior_958_ = lean_ctor_get_uint8(v_val_951_, sizeof(void*)*3);
v_isSharedCheck_971_ = !lean_is_exclusive(v_val_951_);
if (v_isSharedCheck_971_ == 0)
{
v___x_960_ = v_val_951_;
v_isShared_961_ = v_isSharedCheck_971_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_tables_957_);
lean_inc(v_kinds_956_);
lean_inc(v_declName_955_);
lean_dec(v_val_951_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_971_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v_kinds_962_; lean_object* v_tables_963_; lean_object* v___x_965_; 
v_kinds_962_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_956_, v_declName_946_);
v_tables_963_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(v_tables_957_, v_p_947_, v_prio_948_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 2, v_tables_963_);
lean_ctor_set(v___x_960_, 1, v_kinds_962_);
v___x_965_ = v___x_960_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_declName_955_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_kinds_962_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_tables_963_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*3, v_behavior_958_);
v___x_965_ = v_reuseFailAlloc_970_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_944_, v_catName_945_, v___x_965_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_966_);
v___x_968_ = v___x_953_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object* v_categories_973_, lean_object* v_catName_974_, lean_object* v_declName_975_, uint8_t v_leading_976_, lean_object* v_p_977_, lean_object* v_prio_978_){
_start:
{
if (v_leading_976_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_Parser_addTrailingParser(v_categories_973_, v_catName_974_, v_declName_975_, v_p_977_, v_prio_978_);
return v___x_979_;
}
else
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_Parser_addLeadingParser(v_categories_973_, v_catName_974_, v_declName_975_, v_p_977_, v_prio_978_);
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object* v_categories_981_, lean_object* v_catName_982_, lean_object* v_declName_983_, lean_object* v_leading_984_, lean_object* v_p_985_, lean_object* v_prio_986_){
_start:
{
uint8_t v_leading_boxed_987_; lean_object* v_res_988_; 
v_leading_boxed_987_ = lean_unbox(v_leading_984_);
v_res_988_ = l_Lean_Parser_addParser(v_categories_981_, v_catName_982_, v_declName_983_, v_leading_boxed_987_, v_p_985_, v_prio_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(lean_object* v_x_989_, lean_object* v_x_990_){
_start:
{
if (lean_obj_tag(v_x_990_) == 0)
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_991_, 0, v_x_989_);
return v___x_991_;
}
else
{
lean_object* v_head_992_; lean_object* v_tail_993_; lean_object* v___x_994_; 
v_head_992_ = lean_ctor_get(v_x_990_, 0);
lean_inc(v_head_992_);
v_tail_993_ = lean_ctor_get(v_x_990_, 1);
lean_inc(v_tail_993_);
lean_dec_ref_known(v_x_990_, 2);
v___x_994_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_x_989_, v_head_992_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_dec(v_tail_993_);
return v___x_994_;
}
else
{
lean_object* v_a_995_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
v_x_989_ = v_a_995_;
v_x_990_ = v_tail_993_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object* v_tokenTable_997_, lean_object* v_info_998_){
_start:
{
lean_object* v_collectTokens_999_; lean_object* v___x_1000_; lean_object* v_newTokens_1001_; lean_object* v___x_1002_; 
v_collectTokens_999_ = lean_ctor_get(v_info_998_, 0);
lean_inc_ref(v_collectTokens_999_);
lean_dec_ref(v_info_998_);
v___x_1000_ = lean_box(0);
v_newTokens_1001_ = lean_apply_1(v_collectTokens_999_, v___x_1000_);
v___x_1002_ = l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(v_tokenTable_997_, v_newTokens_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object* v_info_1005_, lean_object* v_declName_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1008_ = l_Lean_Parser_builtinTokenTable;
v___x_1009_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_1010_ = lean_st_ref_swap(v___x_1008_, v___x_1009_);
v___x_1011_ = l_Lean_Parser_addParserTokens(v___x_1010_, v_info_1005_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1028_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1028_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1028_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1016_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0));
v___x_1017_ = l_Lean_privateToUserName(v_declName_1006_);
v___x_1018_ = 1;
v___x_1019_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1017_, v___x_1018_);
v___x_1020_ = lean_string_append(v___x_1016_, v___x_1019_);
lean_dec_ref(v___x_1019_);
v___x_1021_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_1022_ = lean_string_append(v___x_1020_, v___x_1021_);
v___x_1023_ = lean_string_append(v___x_1022_, v_a_1012_);
lean_dec(v_a_1012_);
v___x_1024_ = lean_mk_io_user_error(v___x_1023_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set_tag(v___x_1014_, 1);
lean_ctor_set(v___x_1014_, 0, v___x_1024_);
v___x_1026_ = v___x_1014_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v_declName_1006_);
v_a_1029_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1031_ = v___x_1011_;
v_isShared_1032_ = v_isSharedCheck_1038_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1011_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1038_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1033_ = lean_st_ref_swap(v___x_1008_, v_a_1029_);
lean_dec(v___x_1033_);
v___x_1034_ = lean_box(0);
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1034_);
v___x_1036_ = v___x_1031_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___boxed(lean_object* v_info_1039_, lean_object* v_declName_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_1039_, v_declName_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(lean_object* v_msg_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1045_ = lean_panic_fn_borrowed(v___x_1044_, v_msg_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object* v_s_1049_, lean_object* v_e_1050_){
_start:
{
switch(lean_obj_tag(v_e_1050_))
{
case 0:
{
lean_object* v_val_1051_; lean_object* v_tokens_1052_; lean_object* v_kinds_1053_; lean_object* v_categories_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1072_; 
v_val_1051_ = lean_ctor_get(v_e_1050_, 0);
lean_inc_ref(v_val_1051_);
lean_dec_ref_known(v_e_1050_, 1);
v_tokens_1052_ = lean_ctor_get(v_s_1049_, 0);
v_kinds_1053_ = lean_ctor_get(v_s_1049_, 1);
v_categories_1054_ = lean_ctor_get(v_s_1049_, 2);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_s_1049_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1056_ = v_s_1049_;
v_isShared_1057_ = v_isSharedCheck_1072_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_categories_1054_);
lean_inc(v_kinds_1053_);
lean_inc(v_tokens_1052_);
lean_dec(v_s_1049_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1072_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; 
v___x_1058_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_1052_, v_val_1051_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_del_object(v___x_1056_);
lean_dec_ref(v_categories_1054_);
lean_dec_ref(v_kinds_1053_);
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1061_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1062_ = lean_unsigned_to_nat(166u);
v___x_1063_ = lean_unsigned_to_nat(26u);
v___x_1064_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1065_ = lean_string_append(v___x_1064_, v_a_1059_);
lean_dec(v_a_1059_);
v___x_1066_ = l_mkPanicMessageWithDecl(v___x_1060_, v___x_1061_, v___x_1062_, v___x_1063_, v___x_1065_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1066_);
return v___x_1067_;
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; 
v_a_1068_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1058_, 1);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v_a_1068_);
v___x_1070_ = v___x_1056_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1068_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_kinds_1053_);
lean_ctor_set(v_reuseFailAlloc_1071_, 2, v_categories_1054_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
case 1:
{
lean_object* v_val_1073_; lean_object* v_tokens_1074_; lean_object* v_kinds_1075_; lean_object* v_categories_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1084_; 
v_val_1073_ = lean_ctor_get(v_e_1050_, 0);
lean_inc(v_val_1073_);
lean_dec_ref_known(v_e_1050_, 1);
v_tokens_1074_ = lean_ctor_get(v_s_1049_, 0);
v_kinds_1075_ = lean_ctor_get(v_s_1049_, 1);
v_categories_1076_ = lean_ctor_get(v_s_1049_, 2);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_s_1049_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1078_ = v_s_1049_;
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_categories_1076_);
lean_inc(v_kinds_1075_);
lean_inc(v_tokens_1074_);
lean_dec(v_s_1049_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_1075_, v_val_1073_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 1, v___x_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_tokens_1074_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_categories_1076_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
case 2:
{
lean_object* v_catName_1085_; lean_object* v_declName_1086_; uint8_t v_behavior_1087_; lean_object* v_tokens_1088_; lean_object* v_kinds_1089_; lean_object* v_categories_1090_; uint8_t v___x_1091_; 
v_catName_1085_ = lean_ctor_get(v_e_1050_, 0);
lean_inc(v_catName_1085_);
v_declName_1086_ = lean_ctor_get(v_e_1050_, 1);
lean_inc(v_declName_1086_);
v_behavior_1087_ = lean_ctor_get_uint8(v_e_1050_, sizeof(void*)*2);
lean_dec_ref_known(v_e_1050_, 2);
v_tokens_1088_ = lean_ctor_get(v_s_1049_, 0);
v_kinds_1089_ = lean_ctor_get(v_s_1049_, 1);
v_categories_1090_ = lean_ctor_get(v_s_1049_, 2);
v___x_1091_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_1090_, v_catName_1085_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1102_; 
lean_inc_ref(v_categories_1090_);
lean_inc_ref(v_kinds_1089_);
lean_inc_ref(v_tokens_1088_);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_s_1049_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; lean_object* v_unused_1104_; lean_object* v_unused_1105_; 
v_unused_1103_ = lean_ctor_get(v_s_1049_, 2);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_s_1049_, 1);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_s_1049_, 0);
lean_dec(v_unused_1105_);
v___x_1093_ = v_s_1049_;
v_isShared_1094_ = v_isSharedCheck_1102_;
goto v_resetjp_1092_;
}
else
{
lean_dec(v_s_1049_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1102_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1095_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_1096_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_1097_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1097_, 0, v_declName_1086_);
lean_ctor_set(v___x_1097_, 1, v___x_1095_);
lean_ctor_set(v___x_1097_, 2, v___x_1096_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*3, v_behavior_1087_);
v___x_1098_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_1090_, v_catName_1085_, v___x_1097_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 2, v___x_1098_);
v___x_1100_ = v___x_1093_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_tokens_1088_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_kinds_1089_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
else
{
lean_dec(v_declName_1086_);
lean_dec(v_catName_1085_);
return v_s_1049_;
}
}
default: 
{
lean_object* v_catName_1106_; lean_object* v_declName_1107_; uint8_t v_leading_1108_; lean_object* v_p_1109_; lean_object* v_prio_1110_; lean_object* v_tokens_1111_; lean_object* v_kinds_1112_; lean_object* v_categories_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1131_; 
v_catName_1106_ = lean_ctor_get(v_e_1050_, 0);
lean_inc(v_catName_1106_);
v_declName_1107_ = lean_ctor_get(v_e_1050_, 1);
lean_inc(v_declName_1107_);
v_leading_1108_ = lean_ctor_get_uint8(v_e_1050_, sizeof(void*)*4);
v_p_1109_ = lean_ctor_get(v_e_1050_, 2);
lean_inc_ref(v_p_1109_);
v_prio_1110_ = lean_ctor_get(v_e_1050_, 3);
lean_inc(v_prio_1110_);
lean_dec_ref_known(v_e_1050_, 4);
v_tokens_1111_ = lean_ctor_get(v_s_1049_, 0);
v_kinds_1112_ = lean_ctor_get(v_s_1049_, 1);
v_categories_1113_ = lean_ctor_get(v_s_1049_, 2);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_s_1049_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1115_ = v_s_1049_;
v_isShared_1116_ = v_isSharedCheck_1131_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_categories_1113_);
lean_inc(v_kinds_1112_);
lean_inc(v_tokens_1111_);
lean_dec(v_s_1049_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1131_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Parser_addParser(v_categories_1113_, v_catName_1106_, v_declName_1107_, v_leading_1108_, v_p_1109_, v_prio_1110_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_del_object(v___x_1115_);
lean_dec_ref(v_kinds_1112_);
lean_dec_ref(v_tokens_1111_);
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1120_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1121_ = lean_unsigned_to_nat(176u);
v___x_1122_ = lean_unsigned_to_nat(30u);
v___x_1123_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1124_ = lean_string_append(v___x_1123_, v_a_1118_);
lean_dec(v_a_1118_);
v___x_1125_ = l_mkPanicMessageWithDecl(v___x_1119_, v___x_1120_, v___x_1121_, v___x_1122_, v___x_1124_);
lean_dec_ref(v___x_1124_);
v___x_1126_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1125_);
return v___x_1126_;
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; 
v_a_1127_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1117_, 1);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 2, v_a_1127_);
v___x_1129_ = v___x_1115_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_tokens_1111_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_kinds_1112_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_a_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg(lean_object* v_x_1132_){
_start:
{
switch(lean_obj_tag(v_x_1132_))
{
case 0:
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_unsigned_to_nat(0u);
return v___x_1133_;
}
case 1:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_unsigned_to_nat(1u);
return v___x_1134_;
}
default: 
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_unsigned_to_nat(2u);
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg___boxed(lean_object* v_x_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Parser_AliasValue_ctorIdx___redArg(v_x_1136_);
lean_dec_ref(v_x_1136_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx(lean_object* v_00_u03b1_1138_, lean_object* v_x_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_Parser_AliasValue_ctorIdx___redArg(v_x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_x_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Parser_AliasValue_ctorIdx(v_00_u03b1_1141_, v_x_1142_);
lean_dec_ref(v_x_1142_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___redArg(lean_object* v_t_1144_, lean_object* v_k_1145_){
_start:
{
lean_object* v_p_1146_; lean_object* v___x_1147_; 
v_p_1146_ = lean_ctor_get(v_t_1144_, 0);
lean_inc(v_p_1146_);
lean_dec_ref(v_t_1144_);
v___x_1147_ = lean_apply_1(v_k_1145_, v_p_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim(lean_object* v_00_u03b1_1148_, lean_object* v_motive_1149_, lean_object* v_ctorIdx_1150_, lean_object* v_t_1151_, lean_object* v_h_1152_, lean_object* v_k_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1151_, v_k_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_motive_1156_, lean_object* v_ctorIdx_1157_, lean_object* v_t_1158_, lean_object* v_h_1159_, lean_object* v_k_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Parser_AliasValue_ctorElim(v_00_u03b1_1155_, v_motive_1156_, v_ctorIdx_1157_, v_t_1158_, v_h_1159_, v_k_1160_);
lean_dec(v_ctorIdx_1157_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim___redArg(lean_object* v_t_1162_, lean_object* v_const_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1162_, v_const_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim(lean_object* v_00_u03b1_1165_, lean_object* v_motive_1166_, lean_object* v_t_1167_, lean_object* v_h_1168_, lean_object* v_const_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1167_, v_const_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim___redArg(lean_object* v_t_1171_, lean_object* v_unary_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1171_, v_unary_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim(lean_object* v_00_u03b1_1174_, lean_object* v_motive_1175_, lean_object* v_t_1176_, lean_object* v_h_1177_, lean_object* v_unary_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1176_, v_unary_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim___redArg(lean_object* v_t_1180_, lean_object* v_binary_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1180_, v_binary_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim(lean_object* v_00_u03b1_1183_, lean_object* v_motive_1184_, lean_object* v_t_1185_, lean_object* v_h_1186_, lean_object* v_binary_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1185_, v_binary_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_Parser_registerAliasCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__0));
v___x_1191_ = lean_mk_io_user_error(v___x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg(lean_object* v_mapRef_1194_, lean_object* v_aliasName_1195_, lean_object* v_value_1196_){
_start:
{
uint8_t v___x_1198_; 
v___x_1198_ = l_Lean_initializing();
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec_ref(v_value_1196_);
lean_dec(v_aliasName_1195_);
v___x_1199_ = lean_obj_once(&l_Lean_Parser_registerAliasCore___redArg___closed__1, &l_Lean_Parser_registerAliasCore___redArg___closed__1_once, _init_l_Lean_Parser_registerAliasCore___redArg___closed__1);
v___x_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
else
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = lean_st_ref_get(v_mapRef_1194_);
v___x_1202_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_aliasName_1195_, v___x_1201_);
lean_dec(v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1203_ = lean_st_ref_take(v_mapRef_1194_);
v___x_1204_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1195_, v_value_1196_, v___x_1203_);
v___x_1205_ = lean_st_ref_put(v_mapRef_1194_, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec_ref(v_value_1196_);
v___x_1207_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__2));
v___x_1208_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1195_, v___x_1202_);
v___x_1209_ = lean_string_append(v___x_1207_, v___x_1208_);
lean_dec_ref(v___x_1208_);
v___x_1210_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__3));
v___x_1211_ = lean_string_append(v___x_1209_, v___x_1210_);
v___x_1212_ = lean_mk_io_user_error(v___x_1211_);
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg___boxed(lean_object* v_mapRef_1214_, lean_object* v_aliasName_1215_, lean_object* v_value_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1214_, v_aliasName_1215_, v_value_1216_);
lean_dec(v_mapRef_1214_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore(lean_object* v_00_u03b1_1219_, lean_object* v_mapRef_1220_, lean_object* v_aliasName_1221_, lean_object* v_value_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1220_, v_aliasName_1221_, v_value_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___boxed(lean_object* v_00_u03b1_1225_, lean_object* v_mapRef_1226_, lean_object* v_aliasName_1227_, lean_object* v_value_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Parser_registerAliasCore(v_00_u03b1_1225_, v_mapRef_1226_, v_aliasName_1227_, v_value_1228_);
lean_dec(v_mapRef_1226_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg(lean_object* v_mapRef_1231_, lean_object* v_aliasName_1232_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = lean_st_ref_get(v_mapRef_1231_);
v___x_1235_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1234_, v_aliasName_1232_);
lean_dec(v___x_1234_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg___boxed(lean_object* v_mapRef_1237_, lean_object* v_aliasName_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1237_, v_aliasName_1238_);
lean_dec(v_aliasName_1238_);
lean_dec(v_mapRef_1237_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias(lean_object* v_00_u03b1_1241_, lean_object* v_mapRef_1242_, lean_object* v_aliasName_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1242_, v_aliasName_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_mapRef_1247_, lean_object* v_aliasName_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Parser_getAlias(v_00_u03b1_1246_, v_mapRef_1247_, v_aliasName_1248_);
lean_dec(v_aliasName_1248_);
lean_dec(v_mapRef_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object* v_mapRef_1255_, lean_object* v_aliasName_1256_){
_start:
{
lean_object* v___x_1258_; lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1298_; 
v___x_1258_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1255_, v_aliasName_1256_);
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1261_ = v___x_1258_;
v_isShared_1262_ = v_isSharedCheck_1298_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1258_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1298_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
if (lean_obj_tag(v_a_1259_) == 0)
{
lean_object* v___x_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1263_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1264_ = 1;
v___x_1265_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1256_, v___x_1264_);
v___x_1266_ = lean_string_append(v___x_1263_, v___x_1265_);
lean_dec_ref(v___x_1265_);
v___x_1267_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1268_ = lean_string_append(v___x_1266_, v___x_1267_);
v___x_1269_ = lean_mk_io_user_error(v___x_1268_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set_tag(v___x_1261_, 1);
lean_ctor_set(v___x_1261_, 0, v___x_1269_);
v___x_1271_ = v___x_1261_;
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
else
{
lean_object* v_val_1273_; 
v_val_1273_ = lean_ctor_get(v_a_1259_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v_a_1259_, 1);
switch(lean_obj_tag(v_val_1273_))
{
case 0:
{
lean_object* v_p_1274_; lean_object* v___x_1276_; 
lean_dec(v_aliasName_1256_);
v_p_1274_ = lean_ctor_get(v_val_1273_, 0);
lean_inc(v_p_1274_);
lean_dec_ref_known(v_val_1273_, 1);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v_p_1274_);
v___x_1276_ = v___x_1261_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_p_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
case 1:
{
lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
lean_dec_ref_known(v_val_1273_, 1);
v___x_1278_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1279_ = 1;
v___x_1280_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1256_, v___x_1279_);
v___x_1281_ = lean_string_append(v___x_1278_, v___x_1280_);
lean_dec_ref(v___x_1280_);
v___x_1282_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__2));
v___x_1283_ = lean_string_append(v___x_1281_, v___x_1282_);
v___x_1284_ = lean_mk_io_user_error(v___x_1283_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set_tag(v___x_1261_, 1);
lean_ctor_set(v___x_1261_, 0, v___x_1284_);
v___x_1286_ = v___x_1261_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
default: 
{
lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
lean_dec_ref_known(v_val_1273_, 1);
v___x_1288_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1289_ = 1;
v___x_1290_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1256_, v___x_1289_);
v___x_1291_ = lean_string_append(v___x_1288_, v___x_1290_);
lean_dec_ref(v___x_1290_);
v___x_1292_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__3));
v___x_1293_ = lean_string_append(v___x_1291_, v___x_1292_);
v___x_1294_ = lean_mk_io_user_error(v___x_1293_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set_tag(v___x_1261_, 1);
lean_ctor_set(v___x_1261_, 0, v___x_1294_);
v___x_1296_ = v___x_1261_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object* v_mapRef_1299_, lean_object* v_aliasName_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1299_, v_aliasName_1300_);
lean_dec(v_mapRef_1299_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object* v_00_u03b1_1303_, lean_object* v_mapRef_1304_, lean_object* v_aliasName_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1304_, v_aliasName_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object* v_00_u03b1_1308_, lean_object* v_mapRef_1309_, lean_object* v_aliasName_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Parser_getConstAlias(v_00_u03b1_1308_, v_mapRef_1309_, v_aliasName_1310_);
lean_dec(v_mapRef_1309_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object* v_mapRef_1314_, lean_object* v_aliasName_1315_){
_start:
{
lean_object* v___x_1317_; lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1347_; 
v___x_1317_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1314_, v_aliasName_1315_);
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1347_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1347_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
if (lean_obj_tag(v_a_1318_) == 0)
{
lean_object* v___x_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1322_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1323_ = 1;
v___x_1324_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1315_, v___x_1323_);
v___x_1325_ = lean_string_append(v___x_1322_, v___x_1324_);
lean_dec_ref(v___x_1324_);
v___x_1326_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1327_ = lean_string_append(v___x_1325_, v___x_1326_);
v___x_1328_ = lean_mk_io_user_error(v___x_1327_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set_tag(v___x_1320_, 1);
lean_ctor_set(v___x_1320_, 0, v___x_1328_);
v___x_1330_ = v___x_1320_;
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
else
{
lean_object* v_val_1332_; 
v_val_1332_ = lean_ctor_get(v_a_1318_, 0);
lean_inc(v_val_1332_);
lean_dec_ref_known(v_a_1318_, 1);
if (lean_obj_tag(v_val_1332_) == 1)
{
lean_object* v_p_1333_; lean_object* v___x_1335_; 
lean_dec(v_aliasName_1315_);
v_p_1333_ = lean_ctor_get(v_val_1332_, 0);
lean_inc(v_p_1333_);
lean_dec_ref_known(v_val_1332_, 1);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v_p_1333_);
v___x_1335_ = v___x_1320_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_p_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
else
{
lean_object* v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
lean_dec(v_val_1332_);
v___x_1337_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1338_ = 1;
v___x_1339_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1315_, v___x_1338_);
v___x_1340_ = lean_string_append(v___x_1337_, v___x_1339_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = ((lean_object*)(l_Lean_Parser_getUnaryAlias___redArg___closed__0));
v___x_1342_ = lean_string_append(v___x_1340_, v___x_1341_);
v___x_1343_ = lean_mk_io_user_error(v___x_1342_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set_tag(v___x_1320_, 1);
lean_ctor_set(v___x_1320_, 0, v___x_1343_);
v___x_1345_ = v___x_1320_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object* v_mapRef_1348_, lean_object* v_aliasName_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1348_, v_aliasName_1349_);
lean_dec(v_mapRef_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object* v_00_u03b1_1352_, lean_object* v_mapRef_1353_, lean_object* v_aliasName_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1353_, v_aliasName_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object* v_00_u03b1_1357_, lean_object* v_mapRef_1358_, lean_object* v_aliasName_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Parser_getUnaryAlias(v_00_u03b1_1357_, v_mapRef_1358_, v_aliasName_1359_);
lean_dec(v_mapRef_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object* v_mapRef_1363_, lean_object* v_aliasName_1364_){
_start:
{
lean_object* v___x_1366_; lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1396_; 
v___x_1366_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1363_, v_aliasName_1364_);
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1396_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1396_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
if (lean_obj_tag(v_a_1367_) == 0)
{
lean_object* v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1371_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1372_ = 1;
v___x_1373_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1364_, v___x_1372_);
v___x_1374_ = lean_string_append(v___x_1371_, v___x_1373_);
lean_dec_ref(v___x_1373_);
v___x_1375_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1376_ = lean_string_append(v___x_1374_, v___x_1375_);
v___x_1377_ = lean_mk_io_user_error(v___x_1376_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 1);
lean_ctor_set(v___x_1369_, 0, v___x_1377_);
v___x_1379_ = v___x_1369_;
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
else
{
lean_object* v_val_1381_; 
v_val_1381_ = lean_ctor_get(v_a_1367_, 0);
lean_inc(v_val_1381_);
lean_dec_ref_known(v_a_1367_, 1);
if (lean_obj_tag(v_val_1381_) == 2)
{
lean_object* v_p_1382_; lean_object* v___x_1384_; 
lean_dec(v_aliasName_1364_);
v_p_1382_ = lean_ctor_get(v_val_1381_, 0);
lean_inc(v_p_1382_);
lean_dec_ref_known(v_val_1381_, 1);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v_p_1382_);
v___x_1384_ = v___x_1369_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_p_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
else
{
lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
lean_dec(v_val_1381_);
v___x_1386_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1387_ = 1;
v___x_1388_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1364_, v___x_1387_);
v___x_1389_ = lean_string_append(v___x_1386_, v___x_1388_);
lean_dec_ref(v___x_1388_);
v___x_1390_ = ((lean_object*)(l_Lean_Parser_getBinaryAlias___redArg___closed__0));
v___x_1391_ = lean_string_append(v___x_1389_, v___x_1390_);
v___x_1392_ = lean_mk_io_user_error(v___x_1391_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 1);
lean_ctor_set(v___x_1369_, 0, v___x_1392_);
v___x_1394_ = v___x_1369_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg___boxed(lean_object* v_mapRef_1397_, lean_object* v_aliasName_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1397_, v_aliasName_1398_);
lean_dec(v_mapRef_1397_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object* v_00_u03b1_1401_, lean_object* v_mapRef_1402_, lean_object* v_aliasName_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1402_, v_aliasName_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___boxed(lean_object* v_00_u03b1_1406_, lean_object* v_mapRef_1407_, lean_object* v_aliasName_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Parser_getBinaryAlias(v_00_u03b1_1406_, v_mapRef_1407_, v_aliasName_1408_);
lean_dec(v_mapRef_1407_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = lean_box(1);
v___x_1413_ = lean_st_mk_ref(v___x_1412_);
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = lean_box(1);
v___x_1419_ = lean_st_mk_ref(v___x_1418_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = lean_box(1);
v___x_1425_ = lean_st_mk_ref(v___x_1424_);
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object* v_a_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(lean_object* v_t_1429_, lean_object* v_k_1430_, lean_object* v_fallback_1431_){
_start:
{
if (lean_obj_tag(v_t_1429_) == 0)
{
lean_object* v_k_1432_; lean_object* v_v_1433_; lean_object* v_l_1434_; lean_object* v_r_1435_; uint8_t v___x_1436_; 
v_k_1432_ = lean_ctor_get(v_t_1429_, 1);
v_v_1433_ = lean_ctor_get(v_t_1429_, 2);
v_l_1434_ = lean_ctor_get(v_t_1429_, 3);
v_r_1435_ = lean_ctor_get(v_t_1429_, 4);
v___x_1436_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1430_, v_k_1432_);
switch(v___x_1436_)
{
case 0:
{
v_t_1429_ = v_l_1434_;
goto _start;
}
case 1:
{
lean_inc(v_v_1433_);
return v_v_1433_;
}
default: 
{
v_t_1429_ = v_r_1435_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_1431_);
return v_fallback_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg___boxed(lean_object* v_t_1439_, lean_object* v_k_1440_, lean_object* v_fallback_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1439_, v_k_1440_, v_fallback_1441_);
lean_dec(v_fallback_1441_);
lean_dec(v_k_1440_);
lean_dec(v_t_1439_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo(lean_object* v_aliasName_1449_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1451_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1452_ = lean_st_ref_get(v___x_1451_);
v___x_1453_ = ((lean_object*)(l_Lean_Parser_getParserAliasInfo___closed__1));
v___x_1454_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v___x_1452_, v_aliasName_1449_, v___x_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo___boxed(lean_object* v_aliasName_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_Parser_getParserAliasInfo(v_aliasName_1456_);
lean_dec(v_aliasName_1456_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(lean_object* v_00_u03b4_1459_, lean_object* v_t_1460_, lean_object* v_k_1461_, lean_object* v_fallback_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1460_, v_k_1461_, v_fallback_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___boxed(lean_object* v_00_u03b4_1464_, lean_object* v_t_1465_, lean_object* v_k_1466_, lean_object* v_fallback_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(v_00_u03b4_1464_, v_t_1465_, v_k_1466_, v_fallback_1467_);
lean_dec(v_fallback_1467_);
lean_dec(v_k_1466_);
lean_dec(v_t_1465_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object* v_aliasName_1469_, lean_object* v_declName_1470_, lean_object* v_p_1471_, lean_object* v_kind_x3f_1472_, lean_object* v_info_1473_){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = l_Lean_Parser_parserAliasesRef;
lean_inc(v_aliasName_1469_);
v___x_1492_ = l_Lean_Parser_registerAliasCore___redArg(v___x_1491_, v_aliasName_1469_, v_p_1471_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_dec_ref_known(v___x_1492_, 1);
if (lean_obj_tag(v_kind_x3f_1472_) == 1)
{
lean_object* v_val_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_val_1493_ = lean_ctor_get(v_kind_x3f_1472_, 0);
lean_inc(v_val_1493_);
lean_dec_ref_known(v_kind_x3f_1472_, 1);
v___x_1494_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1495_ = lean_st_ref_take(v___x_1494_);
lean_inc(v_aliasName_1469_);
v___x_1496_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1469_, v_val_1493_, v___x_1495_);
v___x_1497_ = lean_st_ref_put(v___x_1494_, v___x_1496_);
goto v___jp_1475_;
}
else
{
lean_dec(v_kind_x3f_1472_);
goto v___jp_1475_;
}
}
else
{
lean_dec_ref(v_info_1473_);
lean_dec(v_kind_x3f_1472_);
lean_dec(v_declName_1470_);
lean_dec(v_aliasName_1469_);
return v___x_1492_;
}
v___jp_1475_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v_stackSz_x3f_1478_; uint8_t v_autoGroupArgs_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1489_; 
v___x_1476_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1477_ = lean_st_ref_take(v___x_1476_);
v_stackSz_x3f_1478_ = lean_ctor_get(v_info_1473_, 1);
v_autoGroupArgs_1479_ = lean_ctor_get_uint8(v_info_1473_, sizeof(void*)*2);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_info_1473_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v_info_1473_, 0);
lean_dec(v_unused_1490_);
v___x_1481_ = v_info_1473_;
v_isShared_1482_ = v_isSharedCheck_1489_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_stackSz_x3f_1478_);
lean_dec(v_info_1473_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1489_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v_declName_1470_);
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_declName_1470_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_stackSz_x3f_1478_);
lean_ctor_set_uint8(v_reuseFailAlloc_1488_, sizeof(void*)*2, v_autoGroupArgs_1479_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1469_, v___x_1484_, v___x_1477_);
v___x_1486_ = lean_st_ref_put(v___x_1476_, v___x_1485_);
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias___boxed(lean_object* v_aliasName_1498_, lean_object* v_declName_1499_, lean_object* v_p_1500_, lean_object* v_kind_x3f_1501_, lean_object* v_info_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_Parser_registerAlias(v_aliasName_1498_, v_declName_1499_, v_p_1500_, v_kind_x3f_1501_, v_info_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue___lam__0(lean_object* v_p_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v_p_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0(lean_object* v_p_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_p_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0(lean_object* v_p_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_p_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object* v_aliasName_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1535_; 
v___x_1519_ = l_Lean_Parser_parserAliasesRef;
v___x_1520_ = l_Lean_Parser_getAlias___redArg(v___x_1519_, v_aliasName_1517_);
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1535_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1535_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
if (lean_obj_tag(v_a_1521_) == 1)
{
uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
lean_dec_ref_known(v_a_1521_, 1);
v___x_1525_ = 1;
v___x_1526_ = lean_box(v___x_1525_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1526_);
v___x_1528_ = v___x_1523_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
else
{
uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
lean_dec(v_a_1521_);
v___x_1530_ = 0;
v___x_1531_ = lean_box(v___x_1530_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1531_);
v___x_1533_ = v___x_1523_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object* v_aliasName_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Parser_isParserAlias(v_aliasName_1536_);
lean_dec(v_aliasName_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object* v_aliasName_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1541_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1542_ = lean_st_ref_get(v___x_1541_);
v___x_1543_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1542_, v_aliasName_1539_);
lean_dec(v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f___boxed(lean_object* v_aliasName_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v_aliasName_1545_);
lean_dec(v_aliasName_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object* v_aliasName_1548_){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = l_Lean_Parser_parserAliasesRef;
v___x_1551_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1550_, v_aliasName_1548_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1559_; 
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v___x_1551_, 0);
lean_dec(v_unused_1560_);
v___x_1553_ = v___x_1551_;
v_isShared_1554_ = v_isSharedCheck_1559_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v___x_1551_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1559_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1555_ = lean_box(0);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1555_);
v___x_1557_ = v___x_1553_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
v_a_1561_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1551_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1551_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias___boxed(lean_object* v_aliasName_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Parser_ensureUnaryParserAlias(v_aliasName_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object* v_aliasName_1572_){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = l_Lean_Parser_parserAliasesRef;
v___x_1575_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1574_, v_aliasName_1572_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1583_; 
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v___x_1575_, 0);
lean_dec(v_unused_1584_);
v___x_1577_ = v___x_1575_;
v_isShared_1578_ = v_isSharedCheck_1583_;
goto v_resetjp_1576_;
}
else
{
lean_dec(v___x_1575_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1583_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = lean_box(0);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1579_);
v___x_1581_ = v___x_1577_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_a_1585_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1575_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1575_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias___boxed(lean_object* v_aliasName_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Parser_ensureBinaryParserAlias(v_aliasName_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object* v_aliasName_1596_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = l_Lean_Parser_parserAliasesRef;
v___x_1599_ = l_Lean_Parser_getConstAlias___redArg(v___x_1598_, v_aliasName_1596_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1607_; 
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v___x_1599_, 0);
lean_dec(v_unused_1608_);
v___x_1601_ = v___x_1599_;
v_isShared_1602_ = v_isSharedCheck_1607_;
goto v_resetjp_1600_;
}
else
{
lean_dec(v___x_1599_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1607_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_box(0);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1603_);
v___x_1605_ = v___x_1601_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
v_a_1609_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1599_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1599_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias___boxed(lean_object* v_aliasName_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_Parser_ensureConstantParserAlias(v_aliasName_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* v_constName_1628_, lean_object* v_compileParserDescr_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v_env_1641_; lean_object* v_opts_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; 
v_env_1641_ = lean_ctor_get(v_a_1630_, 0);
v_opts_1642_ = lean_ctor_get(v_a_1630_, 1);
v___x_1643_ = 0;
lean_inc(v_constName_1628_);
lean_inc_ref(v_env_1641_);
v___x_1644_ = l_Lean_Environment_find_x3f(v_env_1641_, v_constName_1628_, v___x_1643_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v___x_1645_; uint8_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec_ref(v_compileParserDescr_1629_);
v___x_1645_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_1646_ = 1;
v___x_1647_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1628_, v___x_1646_);
v___x_1648_ = lean_string_append(v___x_1645_, v___x_1647_);
lean_dec_ref(v___x_1647_);
v___x_1649_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_1650_ = lean_string_append(v___x_1648_, v___x_1649_);
v___x_1651_ = lean_mk_io_user_error(v___x_1650_);
v___x_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
else
{
lean_object* v_val_1653_; lean_object* v___x_1654_; 
v_val_1653_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_val_1653_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1654_ = l_Lean_ConstantInfo_type(v_val_1653_);
lean_dec(v_val_1653_);
if (lean_obj_tag(v___x_1654_) == 4)
{
lean_object* v_declName_1655_; 
v_declName_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_declName_1655_);
lean_dec_ref_known(v___x_1654_, 2);
if (lean_obj_tag(v_declName_1655_) == 1)
{
lean_object* v_pre_1656_; 
v_pre_1656_ = lean_ctor_get(v_declName_1655_, 0);
lean_inc(v_pre_1656_);
if (lean_obj_tag(v_pre_1656_) == 1)
{
lean_object* v_pre_1657_; 
v_pre_1657_ = lean_ctor_get(v_pre_1656_, 0);
switch(lean_obj_tag(v_pre_1657_))
{
case 1:
{
lean_object* v_pre_1658_; 
lean_inc_ref(v_pre_1657_);
lean_dec_ref(v_compileParserDescr_1629_);
v_pre_1658_ = lean_ctor_get(v_pre_1657_, 0);
if (lean_obj_tag(v_pre_1658_) == 0)
{
lean_object* v_str_1659_; lean_object* v_str_1660_; lean_object* v_str_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v_str_1659_ = lean_ctor_get(v_declName_1655_, 1);
lean_inc_ref(v_str_1659_);
lean_dec_ref_known(v_declName_1655_, 2);
v_str_1660_ = lean_ctor_get(v_pre_1656_, 1);
lean_inc_ref(v_str_1660_);
lean_dec_ref_known(v_pre_1656_, 2);
v_str_1661_ = lean_ctor_get(v_pre_1657_, 1);
lean_inc_ref(v_str_1661_);
lean_dec_ref_known(v_pre_1657_, 2);
v___x_1662_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1663_ = lean_string_dec_eq(v_str_1661_, v___x_1662_);
lean_dec_ref(v_str_1661_);
if (v___x_1663_ == 0)
{
lean_dec_ref(v_str_1660_);
lean_dec_ref(v_str_1659_);
goto v___jp_1632_;
}
else
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_1665_ = lean_string_dec_eq(v_str_1660_, v___x_1664_);
lean_dec_ref(v_str_1660_);
if (v___x_1665_ == 0)
{
lean_dec_ref(v_str_1659_);
goto v___jp_1632_;
}
else
{
lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1666_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_1667_ = lean_string_dec_eq(v_str_1659_, v___x_1666_);
if (v___x_1667_ == 0)
{
uint8_t v___x_1668_; 
v___x_1668_ = lean_string_dec_eq(v_str_1659_, v___x_1664_);
lean_dec_ref(v_str_1659_);
if (v___x_1668_ == 0)
{
goto v___jp_1632_;
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = l_Lean_Environment_evalConst___redArg(v_env_1641_, v_opts_1642_, v_constName_1628_, v___x_1668_);
lean_dec(v_constName_1628_);
v___x_1670_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1669_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1680_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1680_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1680_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1675_ = lean_box(v___x_1668_);
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v_a_1671_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1676_);
v___x_1678_ = v___x_1673_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
v_a_1681_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1670_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1670_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec_ref(v_str_1659_);
v___x_1689_ = l_Lean_Environment_evalConst___redArg(v_env_1641_, v_opts_1642_, v_constName_1628_, v___x_1667_);
lean_dec(v_constName_1628_);
v___x_1690_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1700_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1700_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1700_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1695_ = lean_box(v___x_1643_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v_a_1691_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1696_);
v___x_1698_ = v___x_1693_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
v_a_1701_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1690_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1690_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1657_, 2);
lean_dec_ref_known(v_pre_1656_, 2);
lean_dec_ref_known(v_declName_1655_, 2);
goto v___jp_1632_;
}
}
case 0:
{
lean_object* v_str_1709_; lean_object* v_str_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_str_1709_ = lean_ctor_get(v_declName_1655_, 1);
lean_inc_ref(v_str_1709_);
lean_dec_ref_known(v_declName_1655_, 2);
v_str_1710_ = lean_ctor_get(v_pre_1656_, 1);
lean_inc_ref(v_str_1710_);
lean_dec_ref_known(v_pre_1656_, 2);
v___x_1711_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1712_ = lean_string_dec_eq(v_str_1710_, v___x_1711_);
lean_dec_ref(v_str_1710_);
if (v___x_1712_ == 0)
{
lean_dec_ref(v_str_1709_);
lean_dec_ref(v_compileParserDescr_1629_);
goto v___jp_1632_;
}
else
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_1714_ = lean_string_dec_eq(v_str_1709_, v___x_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1715_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_1716_ = lean_string_dec_eq(v_str_1709_, v___x_1715_);
lean_dec_ref(v_str_1709_);
if (v___x_1716_ == 0)
{
lean_dec_ref(v_compileParserDescr_1629_);
goto v___jp_1632_;
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = l_Lean_Environment_evalConst___redArg(v_env_1641_, v_opts_1642_, v_constName_1628_, v___x_1716_);
lean_dec(v_constName_1628_);
v___x_1718_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1717_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
lean_inc_ref(v_a_1630_);
v___x_1720_ = lean_apply_3(v_compileParserDescr_1629_, v_a_1719_, v_a_1630_, lean_box(0));
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1730_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1723_ = v___x_1720_;
v_isShared_1724_ = v_isSharedCheck_1730_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1730_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1725_ = lean_box(v___x_1714_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v_a_1721_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1726_);
v___x_1728_ = v___x_1723_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
v_a_1731_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1720_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1720_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec_ref(v_compileParserDescr_1629_);
v_a_1739_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1718_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1718_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec_ref(v_str_1709_);
v___x_1747_ = l_Lean_Environment_evalConst___redArg(v_env_1641_, v_opts_1642_, v_constName_1628_, v___x_1714_);
lean_dec(v_constName_1628_);
v___x_1748_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1747_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
lean_inc_ref(v_a_1630_);
v___x_1750_ = lean_apply_3(v_compileParserDescr_1629_, v_a_1749_, v_a_1630_, lean_box(0));
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1760_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1760_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1760_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1755_ = lean_box(v___x_1714_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v_a_1751_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1756_);
v___x_1758_ = v___x_1753_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1750_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1750_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v_compileParserDescr_1629_);
v_a_1769_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1748_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1748_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_pre_1656_, 2);
lean_dec_ref_known(v_declName_1655_, 2);
lean_dec_ref(v_compileParserDescr_1629_);
goto v___jp_1632_;
}
}
}
else
{
lean_dec_ref_known(v_declName_1655_, 2);
lean_dec(v_pre_1656_);
lean_dec_ref(v_compileParserDescr_1629_);
goto v___jp_1632_;
}
}
else
{
lean_dec(v_declName_1655_);
lean_dec_ref(v_compileParserDescr_1629_);
goto v___jp_1632_;
}
}
else
{
lean_dec_ref(v___x_1654_);
lean_dec_ref(v_compileParserDescr_1629_);
goto v___jp_1632_;
}
}
v___jp_1632_:
{
lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1633_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__0));
v___x_1634_ = 1;
v___x_1635_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1628_, v___x_1634_);
v___x_1636_ = lean_string_append(v___x_1633_, v___x_1635_);
lean_dec_ref(v___x_1635_);
v___x_1637_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1));
v___x_1638_ = lean_string_append(v___x_1636_, v___x_1637_);
v___x_1639_ = lean_mk_io_user_error(v___x_1638_);
v___x_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object* v_constName_1777_, lean_object* v_compileParserDescr_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1777_, v_compileParserDescr_1778_, v_a_1779_);
lean_dec_ref(v_a_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed(lean_object* v_categories_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1782_, v_a_1783_, v_a_1784_);
lean_dec_ref(v_a_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(lean_object* v_categories_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
switch(lean_obj_tag(v_a_1788_))
{
case 0:
{
lean_object* v_name_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec_ref(v_categories_1787_);
v_name_1791_ = lean_ctor_get(v_a_1788_, 0);
lean_inc(v_name_1791_);
lean_dec_ref_known(v_a_1788_, 1);
v___x_1792_ = l_Lean_Parser_parserAliasesRef;
v___x_1793_ = l_Lean_Parser_getConstAlias___redArg(v___x_1792_, v_name_1791_);
return v___x_1793_;
}
case 1:
{
lean_object* v_name_1794_; lean_object* v_p_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v_name_1794_ = lean_ctor_get(v_a_1788_, 0);
lean_inc(v_name_1794_);
v_p_1795_ = lean_ctor_get(v_a_1788_, 1);
lean_inc_ref(v_p_1795_);
lean_dec_ref_known(v_a_1788_, 2);
v___x_1796_ = l_Lean_Parser_parserAliasesRef;
v___x_1797_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1796_, v_name_1794_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1799_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref_known(v___x_1797_, 1);
v___x_1799_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1787_, v_p_1795_, v_a_1789_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1808_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = lean_apply_1(v_a_1798_, v_a_1800_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1804_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
else
{
lean_dec(v_a_1798_);
return v___x_1799_;
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec_ref(v_p_1795_);
lean_dec_ref(v_categories_1787_);
v_a_1809_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1797_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1797_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
case 2:
{
lean_object* v_name_1817_; lean_object* v_p_u2081_1818_; lean_object* v_p_u2082_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_name_1817_ = lean_ctor_get(v_a_1788_, 0);
lean_inc(v_name_1817_);
v_p_u2081_1818_ = lean_ctor_get(v_a_1788_, 1);
lean_inc_ref(v_p_u2081_1818_);
v_p_u2082_1819_ = lean_ctor_get(v_a_1788_, 2);
lean_inc_ref(v_p_u2082_1819_);
lean_dec_ref_known(v_a_1788_, 3);
v___x_1820_ = l_Lean_Parser_parserAliasesRef;
v___x_1821_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1820_, v_name_1817_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1823_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___x_1821_, 1);
lean_inc_ref(v_categories_1787_);
v___x_1823_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1787_, v_p_u2081_1818_, v_a_1789_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v___x_1823_, 1);
v___x_1825_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1787_, v_p_u2082_1819_, v_a_1789_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1834_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1834_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1834_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1830_ = lean_apply_2(v_a_1822_, v_a_1824_, v_a_1826_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1830_);
v___x_1832_ = v___x_1828_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
else
{
lean_dec(v_a_1824_);
lean_dec(v_a_1822_);
return v___x_1825_;
}
}
else
{
lean_dec(v_a_1822_);
lean_dec_ref(v_p_u2082_1819_);
lean_dec_ref(v_categories_1787_);
return v___x_1823_;
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec_ref(v_p_u2082_1819_);
lean_dec_ref(v_p_u2081_1818_);
lean_dec_ref(v_categories_1787_);
v_a_1835_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1821_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1821_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
case 3:
{
lean_object* v_kind_1843_; lean_object* v_prec_1844_; lean_object* v_p_1845_; lean_object* v___x_1846_; 
v_kind_1843_ = lean_ctor_get(v_a_1788_, 0);
lean_inc(v_kind_1843_);
v_prec_1844_ = lean_ctor_get(v_a_1788_, 1);
lean_inc(v_prec_1844_);
v_p_1845_ = lean_ctor_get(v_a_1788_, 2);
lean_inc_ref(v_p_1845_);
lean_dec_ref_known(v_a_1788_, 3);
v___x_1846_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1787_, v_p_1845_, v_a_1789_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1855_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = l_Lean_Parser_leadingNode(v_kind_1843_, v_prec_1844_, v_a_1847_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1851_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
else
{
lean_dec(v_prec_1844_);
lean_dec(v_kind_1843_);
return v___x_1846_;
}
}
case 4:
{
lean_object* v_kind_1856_; lean_object* v_prec_1857_; lean_object* v_lhsPrec_1858_; lean_object* v_p_1859_; lean_object* v___x_1860_; 
v_kind_1856_ = lean_ctor_get(v_a_1788_, 0);
lean_inc(v_kind_1856_);
v_prec_1857_ = lean_ctor_get(v_a_1788_, 1);
lean_inc(v_prec_1857_);
v_lhsPrec_1858_ = lean_ctor_get(v_a_1788_, 2);
lean_inc(v_lhsPrec_1858_);
v_p_1859_ = lean_ctor_get(v_a_1788_, 3);
lean_inc_ref(v_p_1859_);
lean_dec_ref_known(v_a_1788_, 4);
v___x_1860_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1787_, v_p_1859_, v_a_1789_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1869_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = l_Lean_Parser_trailingNode(v_kind_1856_, v_prec_1857_, v_lhsPrec_1858_, v_a_1861_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1865_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_dec(v_lhsPrec_1858_);
lean_dec(v_prec_1857_);
lean_dec(v_kind_1856_);
return v___x_1860_;
}
}
case 5:
{
lean_object* v_val_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v_categories_1787_);
v_val_1870_ = lean_ctor_get(v_a_1788_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_a_1788_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1872_ = v_a_1788_;
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_val_1870_);
lean_dec(v_a_1788_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = l_Lean_Parser_symbol(v_val_1870_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set_tag(v___x_1872_, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1874_);
v___x_1876_ = v___x_1872_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
case 6:
{
lean_object* v_val_1879_; uint8_t v_includeIdent_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec_ref(v_categories_1787_);
v_val_1879_ = lean_ctor_get(v_a_1788_, 0);
lean_inc_ref(v_val_1879_);
v_includeIdent_1880_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*1);
lean_dec_ref_known(v_a_1788_, 1);
v___x_1881_ = l_Lean_Parser_nonReservedSymbol(v_val_1879_, v_includeIdent_1880_);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
case 7:
{
lean_object* v_catName_1883_; lean_object* v_rbp_1884_; lean_object* v___x_1885_; 
v_catName_1883_ = lean_ctor_get(v_a_1788_, 0);
lean_inc(v_catName_1883_);
v_rbp_1884_ = lean_ctor_get(v_a_1788_, 1);
lean_inc(v_rbp_1884_);
lean_dec_ref_known(v_a_1788_, 2);
v___x_1885_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_1787_, v_catName_1883_);
lean_dec_ref(v_categories_1787_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_dec(v_rbp_1884_);
v___x_1886_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_1883_);
v___x_1887_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1886_);
return v___x_1887_;
}
else
{
lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1895_; 
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v___x_1885_, 0);
lean_dec(v_unused_1896_);
v___x_1889_ = v___x_1885_;
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
else
{
lean_dec(v___x_1885_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = l_Lean_Parser_categoryParser(v_catName_1883_, v_rbp_1884_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set_tag(v___x_1889_, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
case 8:
{
lean_object* v_declName_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v_declName_1897_ = lean_ctor_get(v_a_1788_, 0);
lean_inc(v_declName_1897_);
lean_dec_ref_known(v_a_1788_, 1);
v___x_1898_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed), 4, 1);
lean_closure_set(v___x_1898_, 0, v_categories_1787_);
v___x_1899_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_declName_1897_, v___x_1898_, v_a_1789_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1908_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_snd_1904_; lean_object* v___x_1906_; 
v_snd_1904_ = lean_ctor_get(v_a_1900_, 1);
lean_inc(v_snd_1904_);
lean_dec(v_a_1900_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v_snd_1904_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_snd_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1899_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1899_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
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
case 9:
{
lean_object* v_name_1917_; lean_object* v_kind_1918_; lean_object* v_p_1919_; lean_object* v___x_1920_; 
v_name_1917_ = lean_ctor_get(v_a_1788_, 0);
lean_inc_ref(v_name_1917_);
v_kind_1918_ = lean_ctor_get(v_a_1788_, 1);
lean_inc(v_kind_1918_);
v_p_1919_ = lean_ctor_get(v_a_1788_, 2);
lean_inc_ref(v_p_1919_);
lean_dec_ref_known(v_a_1788_, 3);
v___x_1920_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1787_, v_p_1919_, v_a_1789_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1931_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1931_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1931_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
uint8_t v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1925_ = 1;
lean_inc(v_kind_1918_);
v___x_1926_ = l_Lean_Parser_nodeWithAntiquot(v_name_1917_, v_kind_1918_, v_a_1921_, v___x_1925_);
v___x_1927_ = l_Lean_Parser_withCache(v_kind_1918_, v___x_1926_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1927_);
v___x_1929_ = v___x_1923_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
else
{
lean_dec(v_kind_1918_);
lean_dec_ref(v_name_1917_);
return v___x_1920_;
}
}
case 10:
{
lean_object* v_p_1932_; lean_object* v_sep_1933_; lean_object* v_psep_1934_; uint8_t v_allowTrailingSep_1935_; lean_object* v___x_1936_; 
v_p_1932_ = lean_ctor_get(v_a_1788_, 0);
lean_inc_ref(v_p_1932_);
v_sep_1933_ = lean_ctor_get(v_a_1788_, 1);
lean_inc_ref(v_sep_1933_);
v_psep_1934_ = lean_ctor_get(v_a_1788_, 2);
lean_inc_ref(v_psep_1934_);
v_allowTrailingSep_1935_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1788_, 3);
lean_inc_ref(v_categories_1787_);
v___x_1936_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1787_, v_p_1932_, v_a_1789_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1938_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1938_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1787_, v_psep_1934_, v_a_1789_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1947_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1947_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1947_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1943_ = l_Lean_Parser_sepBy(v_a_1937_, v_sep_1933_, v_a_1939_, v_allowTrailingSep_1935_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1943_);
v___x_1945_ = v___x_1941_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_dec(v_a_1937_);
lean_dec_ref(v_sep_1933_);
return v___x_1938_;
}
}
else
{
lean_dec_ref(v_psep_1934_);
lean_dec_ref(v_sep_1933_);
lean_dec_ref(v_categories_1787_);
return v___x_1936_;
}
}
case 11:
{
lean_object* v_p_1948_; lean_object* v_sep_1949_; lean_object* v_psep_1950_; uint8_t v_allowTrailingSep_1951_; lean_object* v___x_1952_; 
v_p_1948_ = lean_ctor_get(v_a_1788_, 0);
lean_inc_ref(v_p_1948_);
v_sep_1949_ = lean_ctor_get(v_a_1788_, 1);
lean_inc_ref(v_sep_1949_);
v_psep_1950_ = lean_ctor_get(v_a_1788_, 2);
lean_inc_ref(v_psep_1950_);
v_allowTrailingSep_1951_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1788_, 3);
lean_inc_ref(v_categories_1787_);
v___x_1952_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1787_, v_p_1948_, v_a_1789_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1954_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1787_, v_psep_1950_, v_a_1789_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1963_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1959_ = l_Lean_Parser_sepBy1(v_a_1953_, v_sep_1949_, v_a_1955_, v_allowTrailingSep_1951_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1959_);
v___x_1961_ = v___x_1957_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
else
{
lean_dec(v_a_1953_);
lean_dec_ref(v_sep_1949_);
return v___x_1954_;
}
}
else
{
lean_dec_ref(v_psep_1950_);
lean_dec_ref(v_sep_1949_);
lean_dec_ref(v_categories_1787_);
return v___x_1952_;
}
}
default: 
{
lean_object* v_val_1964_; lean_object* v_asciiVal_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_dec_ref(v_categories_1787_);
v_val_1964_ = lean_ctor_get(v_a_1788_, 0);
lean_inc_ref(v_val_1964_);
v_asciiVal_1965_ = lean_ctor_get(v_a_1788_, 1);
lean_inc_ref(v_asciiVal_1965_);
lean_dec_ref_known(v_a_1788_, 2);
v___x_1966_ = l_Lean_Parser_unicodeSymbol___redArg(v_val_1964_, v_asciiVal_1965_);
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object* v_categories_1968_, lean_object* v_d_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1968_, v_d_1969_, v_a_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object* v_categories_1973_, lean_object* v_d_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Parser_compileParserDescr(v_categories_1973_, v_d_1974_, v_a_1975_);
lean_dec_ref(v_a_1975_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0(lean_object* v_categories_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1978_, v___y_1979_, v___y_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0___boxed(lean_object* v_categories_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_Parser_mkParserOfConstant___lam__0(v_categories_1983_, v___y_1984_, v___y_1985_);
lean_dec_ref(v___y_1985_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* v_categories_1988_, lean_object* v_constName_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v___f_1992_; lean_object* v___x_1993_; 
v___f_1992_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserOfConstant___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1992_, 0, v_categories_1988_);
v___x_1993_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1989_, v___f_1992_, v_a_1990_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___boxed(lean_object* v_categories_1994_, lean_object* v_constName_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_Parser_mkParserOfConstant(v_categories_1994_, v_constName_1995_, v_a_1996_);
lean_dec_ref(v_a_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2000_ = lean_box(0);
v___x_2001_ = lean_st_mk_ref(v___x_2000_);
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object* v_a_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object* v_hook_2005_){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2007_ = l_Lean_Parser_parserAttributeHooks;
v___x_2008_ = lean_st_ref_take(v___x_2007_);
v___x_2009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2009_, 0, v_hook_2005_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = lean_st_ref_put(v___x_2007_, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook___boxed(lean_object* v_hook_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Parser_registerParserAttributeHook(v_hook_2012_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(lean_object* v_catName_2015_, lean_object* v_declName_2016_, uint8_t v_builtin_2017_, lean_object* v_as_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
if (lean_obj_tag(v_as_2018_) == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v_declName_2016_);
lean_dec(v_catName_2015_);
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
return v___x_2023_;
}
else
{
lean_object* v_head_2024_; lean_object* v_tail_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_head_2024_ = lean_ctor_get(v_as_2018_, 0);
lean_inc(v_head_2024_);
v_tail_2025_ = lean_ctor_get(v_as_2018_, 1);
lean_inc(v_tail_2025_);
lean_dec_ref_known(v_as_2018_, 2);
v___x_2026_ = lean_box(v_builtin_2017_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2019_);
lean_inc(v_declName_2016_);
lean_inc(v_catName_2015_);
v___x_2027_ = lean_apply_6(v_head_2024_, v_catName_2015_, v_declName_2016_, v___x_2026_, v___y_2019_, v___y_2020_, lean_box(0));
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_dec_ref_known(v___x_2027_, 1);
v_as_2018_ = v_tail_2025_;
goto _start;
}
else
{
lean_dec(v_tail_2025_);
lean_dec(v_declName_2016_);
lean_dec(v_catName_2015_);
return v___x_2027_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0___boxed(lean_object* v_catName_2029_, lean_object* v_declName_2030_, lean_object* v_builtin_2031_, lean_object* v_as_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
uint8_t v_builtin_boxed_2036_; lean_object* v_res_2037_; 
v_builtin_boxed_2036_ = lean_unbox(v_builtin_2031_);
v_res_2037_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2029_, v_declName_2030_, v_builtin_boxed_2036_, v_as_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object* v_catName_2038_, lean_object* v_declName_2039_, uint8_t v_builtin_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = l_Lean_Parser_parserAttributeHooks;
v___x_2045_ = lean_st_ref_get(v___x_2044_);
v___x_2046_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2038_, v_declName_2039_, v_builtin_2040_, v___x_2045_, v_a_2041_, v_a_2042_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object* v_catName_2047_, lean_object* v_declName_2048_, lean_object* v_builtin_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
uint8_t v_builtin_boxed_2053_; lean_object* v_res_2054_; 
v_builtin_boxed_2053_ = lean_unbox(v_builtin_2049_);
v_res_2054_ = l_Lean_Parser_runParserAttributeHooks(v_catName_2047_, v_declName_2048_, v_builtin_boxed_2053_, v_a_2050_, v_a_2051_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2055_, lean_object* v_decl_2056_, lean_object* v_stx_2057_, uint8_t v_x_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2057_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2062_) == 0)
{
uint8_t v___x_2063_; lean_object* v___x_2064_; 
lean_dec_ref_known(v___x_2062_, 1);
v___x_2063_ = 1;
v___x_2064_ = l_Lean_Parser_runParserAttributeHooks(v___x_2055_, v_decl_2056_, v___x_2063_, v___y_2059_, v___y_2060_);
return v___x_2064_;
}
else
{
lean_dec(v_decl_2056_);
lean_dec(v___x_2055_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2065_, lean_object* v_decl_2066_, lean_object* v_stx_2067_, lean_object* v_x_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
uint8_t v_x_1076__boxed_2072_; lean_object* v_res_2073_; 
v_x_1076__boxed_2072_ = lean_unbox(v_x_2068_);
v_res_2073_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2065_, v_decl_2066_, v_stx_2067_, v_x_1076__boxed_2072_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2073_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2074_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2078_ = lean_unsigned_to_nat(0u);
v___x_2079_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
lean_ctor_set(v___x_2079_, 2, v___x_2078_);
lean_ctor_set(v___x_2079_, 3, v___x_2078_);
lean_ctor_set(v___x_2079_, 4, v___x_2077_);
lean_ctor_set(v___x_2079_, 5, v___x_2077_);
lean_ctor_set(v___x_2079_, 6, v___x_2077_);
lean_ctor_set(v___x_2079_, 7, v___x_2077_);
lean_ctor_set(v___x_2079_, 8, v___x_2077_);
lean_ctor_set(v___x_2079_, 9, v___x_2077_);
lean_ctor_set(v___x_2079_, 10, v___x_2077_);
return v___x_2079_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_unsigned_to_nat(32u);
v___x_2081_ = lean_mk_empty_array_with_capacity(v___x_2080_);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2083_ = ((size_t)5ULL);
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = lean_unsigned_to_nat(32u);
v___x_2086_ = lean_mk_empty_array_with_capacity(v___x_2085_);
v___x_2087_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2088_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
lean_ctor_set(v___x_2088_, 1, v___x_2086_);
lean_ctor_set(v___x_2088_, 2, v___x_2084_);
lean_ctor_set(v___x_2088_, 3, v___x_2084_);
lean_ctor_set_usize(v___x_2088_, 4, v___x_2083_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2089_ = lean_box(1);
v___x_2090_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2091_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___x_2090_);
lean_ctor_set(v___x_2092_, 2, v___x_2089_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v___x_2097_; lean_object* v_toCold_2098_; lean_object* v_env_2099_; lean_object* v_options_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2097_ = lean_st_ref_get(v___y_2095_);
v_toCold_2098_ = lean_ctor_get(v___y_2094_, 0);
v_env_2099_ = lean_ctor_get(v___x_2097_, 0);
lean_inc_ref(v_env_2099_);
lean_dec(v___x_2097_);
v_options_2100_ = lean_ctor_get(v_toCold_2098_, 2);
v___x_2101_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_2102_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2100_);
v___x_2103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2103_, 0, v_env_2099_);
lean_ctor_set(v___x_2103_, 1, v___x_2101_);
lean_ctor_set(v___x_2103_, 2, v___x_2102_);
lean_ctor_set(v___x_2103_, 3, v_options_2100_);
v___x_2104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v_msgData_2093_);
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_ref_2115_; lean_object* v___x_2116_; lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2125_; 
v_ref_2115_ = lean_ctor_get(v___y_2112_, 2);
v___x_2116_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msg_2111_, v___y_2112_, v___y_2113_);
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2125_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2125_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
lean_inc(v_ref_2115_);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v_ref_2115_);
lean_ctor_set(v___x_2121_, 1, v_a_2117_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set_tag(v___x_2119_, 1);
lean_ctor_set(v___x_2119_, 0, v___x_2121_);
v___x_2123_ = v___x_2119_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
return v_res_2130_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2133_ = l_Lean_stringToMessageData(v___x_2132_);
return v___x_2133_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2136_ = l_Lean_stringToMessageData(v___x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2137_, lean_object* v_decl_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2142_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2143_ = l_Lean_MessageData_ofName(v___x_2137_);
v___x_2144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2142_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2144_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2146_, v___y_2139_, v___y_2140_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2148_, lean_object* v_decl_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2148_, v_decl_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v_decl_2149_);
return v_res_2153_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = lean_unsigned_to_nat(3646333153u);
v___x_2197_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2198_ = l_Lean_Name_num___override(v___x_2197_, v___x_2196_);
return v___x_2198_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2201_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2202_ = l_Lean_Name_str___override(v___x_2201_, v___x_2200_);
return v___x_2202_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2205_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2206_ = l_Lean_Name_str___override(v___x_2205_, v___x_2204_);
return v___x_2206_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = lean_unsigned_to_nat(2u);
v___x_2208_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2209_ = l_Lean_Name_num___override(v___x_2208_, v___x_2207_);
return v___x_2209_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2216_ = 0;
v___x_2217_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2218_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2219_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2220_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v___x_2218_);
lean_ctor_set(v___x_2220_, 2, v___x_2217_);
lean_ctor_set_uint8(v___x_2220_, sizeof(void*)*3, v___x_2216_);
return v___x_2220_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2221_; lean_object* v___f_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___f_2221_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___f_2222_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2223_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set(v___x_2224_, 1, v___f_2222_);
lean_ctor_set(v___x_2224_, 2, v___f_2221_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2227_ = l_Lean_registerBuiltinAttribute(v___x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v_a_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2230_, lean_object* v_msg_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2231_, v___y_2232_, v___y_2233_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2236_, lean_object* v_msg_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(v_00_u03b1_2236_, v_msg_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2242_, lean_object* v_decl_2243_, lean_object* v_stx_2244_, uint8_t v_x_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2244_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2249_) == 0)
{
uint8_t v___x_2250_; lean_object* v___x_2251_; 
lean_dec_ref_known(v___x_2249_, 1);
v___x_2250_ = 0;
v___x_2251_ = l_Lean_Parser_runParserAttributeHooks(v___x_2242_, v_decl_2243_, v___x_2250_, v___y_2246_, v___y_2247_);
return v___x_2251_;
}
else
{
lean_dec(v_decl_2243_);
lean_dec(v___x_2242_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2252_, lean_object* v_decl_2253_, lean_object* v_stx_2254_, lean_object* v_x_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
uint8_t v_x_211__boxed_2259_; lean_object* v_res_2260_; 
v_x_211__boxed_2259_ = lean_unbox(v_x_2255_);
v_res_2260_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2252_, v_decl_2253_, v_stx_2254_, v_x_211__boxed_2259_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2261_, lean_object* v_decl_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2266_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2267_ = l_Lean_MessageData_ofName(v___x_2261_);
v___x_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2266_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2270_, v___y_2263_, v___y_2264_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2272_, lean_object* v_decl_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2272_, v_decl_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v_decl_2273_);
return v_res_2277_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = lean_unsigned_to_nat(3789407938u);
v___x_2281_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2282_ = l_Lean_Name_num___override(v___x_2281_, v___x_2280_);
return v___x_2282_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2284_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2285_ = l_Lean_Name_str___override(v___x_2284_, v___x_2283_);
return v___x_2285_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2287_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2288_ = l_Lean_Name_str___override(v___x_2287_, v___x_2286_);
return v___x_2288_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = lean_unsigned_to_nat(2u);
v___x_2290_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2291_ = l_Lean_Name_num___override(v___x_2290_, v___x_2289_);
return v___x_2291_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2298_ = 0;
v___x_2299_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2300_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2301_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2302_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
lean_ctor_set(v___x_2302_, 1, v___x_2300_);
lean_ctor_set(v___x_2302_, 2, v___x_2299_);
lean_ctor_set_uint8(v___x_2302_, sizeof(void*)*3, v___x_2298_);
return v___x_2302_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2303_; lean_object* v___f_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___f_2303_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___f_2304_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2305_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v___f_2304_);
lean_ctor_set(v___x_2306_, 2, v___f_2303_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2309_ = l_Lean_registerBuiltinAttribute(v___x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object* v_s_2312_, lean_object* v_x_2313_, lean_object* v_a_2314_){
_start:
{
switch(lean_obj_tag(v_x_2313_))
{
case 0:
{
lean_object* v_val_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2324_; 
lean_dec_ref(v_s_2312_);
v_val_2316_ = lean_ctor_get(v_x_2313_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_x_2313_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2318_ = v_x_2313_;
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_val_2316_);
lean_dec(v_x_2313_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_val_2316_);
v___x_2321_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
}
}
case 1:
{
lean_object* v_val_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v_s_2312_);
v_val_2325_ = lean_ctor_get(v_x_2313_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_x_2313_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2327_ = v_x_2313_;
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_val_2325_);
lean_dec(v_x_2313_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_val_2325_);
v___x_2330_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
return v___x_2331_;
}
}
}
case 2:
{
lean_object* v_catName_2334_; lean_object* v_declName_2335_; uint8_t v_behavior_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2344_; 
lean_dec_ref(v_s_2312_);
v_catName_2334_ = lean_ctor_get(v_x_2313_, 0);
v_declName_2335_ = lean_ctor_get(v_x_2313_, 1);
v_behavior_2336_ = lean_ctor_get_uint8(v_x_2313_, sizeof(void*)*2);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_x_2313_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2338_ = v_x_2313_;
v_isShared_2339_ = v_isSharedCheck_2344_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_declName_2335_);
lean_inc(v_catName_2334_);
lean_dec(v_x_2313_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2344_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_catName_2334_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_declName_2335_);
lean_ctor_set_uint8(v_reuseFailAlloc_2343_, sizeof(void*)*2, v_behavior_2336_);
v___x_2341_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
return v___x_2342_;
}
}
}
default: 
{
lean_object* v_catName_2345_; lean_object* v_declName_2346_; lean_object* v_prio_2347_; lean_object* v_categories_2348_; lean_object* v___x_2349_; 
v_catName_2345_ = lean_ctor_get(v_x_2313_, 0);
lean_inc(v_catName_2345_);
v_declName_2346_ = lean_ctor_get(v_x_2313_, 1);
lean_inc_n(v_declName_2346_, 2);
v_prio_2347_ = lean_ctor_get(v_x_2313_, 2);
lean_inc(v_prio_2347_);
lean_dec_ref_known(v_x_2313_, 3);
v_categories_2348_ = lean_ctor_get(v_s_2312_, 2);
lean_inc_ref(v_categories_2348_);
lean_dec_ref(v_s_2312_);
v___x_2349_ = l_Lean_Parser_mkParserOfConstant(v_categories_2348_, v_declName_2346_, v_a_2314_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2361_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2361_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2361_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v_fst_2354_; lean_object* v_snd_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; lean_object* v___x_2359_; 
v_fst_2354_ = lean_ctor_get(v_a_2350_, 0);
lean_inc(v_fst_2354_);
v_snd_2355_ = lean_ctor_get(v_a_2350_, 1);
lean_inc(v_snd_2355_);
lean_dec(v_a_2350_);
v___x_2356_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_2356_, 0, v_catName_2345_);
lean_ctor_set(v___x_2356_, 1, v_declName_2346_);
lean_ctor_set(v___x_2356_, 2, v_snd_2355_);
lean_ctor_set(v___x_2356_, 3, v_prio_2347_);
v___x_2357_ = lean_unbox(v_fst_2354_);
lean_dec(v_fst_2354_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*4, v___x_2357_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2356_);
v___x_2359_ = v___x_2352_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2356_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec(v_prio_2347_);
lean_dec(v_declName_2346_);
lean_dec(v_catName_2345_);
v_a_2362_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2349_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2349_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object* v_s_2370_, lean_object* v_x_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(v_s_2370_, v_x_2371_, v_a_2372_);
lean_dec_ref(v_a_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v_x_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2377_, 0, v_a_2376_);
lean_inc_ref_n(v___x_2377_, 2);
v___x_2378_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
lean_ctor_set(v___x_2378_, 2, v___x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_x_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v_x_2379_, v_a_2380_);
lean_dec_ref(v_x_2379_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v___y_2382_){
_start:
{
lean_inc_ref(v___y_2382_);
return v___y_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v___y_2383_);
lean_dec_ref(v___y_2383_);
return v_res_2384_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2395_; lean_object* v___f_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___f_2395_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___f_2396_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2397_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2398_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2399_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2400_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed), 1, 0);
v___x_2401_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2402_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
lean_ctor_set(v___x_2402_, 1, v___x_2400_);
lean_ctor_set(v___x_2402_, 2, v___x_2399_);
lean_ctor_set(v___x_2402_, 3, v___x_2398_);
lean_ctor_set(v___x_2402_, 4, v___x_2397_);
lean_ctor_set(v___x_2402_, 5, v___f_2396_);
lean_ctor_set(v___x_2402_, 6, v___f_2395_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_);
v___x_2405_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object* v_env_2408_, lean_object* v_catName_2409_){
_start:
{
lean_object* v___x_2410_; lean_object* v_ext_2411_; lean_object* v_toEnvExtension_2412_; lean_object* v_asyncMode_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v_categories_2416_; lean_object* v___x_2417_; 
v___x_2410_ = l_Lean_Parser_parserExtension;
v_ext_2411_ = lean_ctor_get(v___x_2410_, 1);
v_toEnvExtension_2412_ = lean_ctor_get(v_ext_2411_, 0);
v_asyncMode_2413_ = lean_ctor_get(v_toEnvExtension_2412_, 2);
v___x_2414_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2415_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2414_, v___x_2410_, v_env_2408_, v_asyncMode_2413_);
v_categories_2416_ = lean_ctor_get(v___x_2415_, 2);
lean_inc_ref(v_categories_2416_);
lean_dec(v___x_2415_);
v___x_2417_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2416_, v_catName_2409_);
lean_dec_ref(v_categories_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object* v_env_2418_, lean_object* v_catName_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_Parser_getParserCategory_x3f(v_env_2418_, v_catName_2419_);
lean_dec(v_catName_2419_);
return v_res_2420_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object* v_env_2421_, lean_object* v_catName_2422_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_Parser_getParserCategory_x3f(v_env_2421_, v_catName_2422_);
if (lean_obj_tag(v___x_2423_) == 0)
{
uint8_t v___x_2424_; 
v___x_2424_ = 0;
return v___x_2424_;
}
else
{
uint8_t v___x_2425_; 
lean_dec_ref_known(v___x_2423_, 1);
v___x_2425_ = 1;
return v___x_2425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object* v_env_2426_, lean_object* v_catName_2427_){
_start:
{
uint8_t v_res_2428_; lean_object* v_r_2429_; 
v_res_2428_ = l_Lean_Parser_isParserCategory(v_env_2426_, v_catName_2427_);
lean_dec(v_catName_2427_);
v_r_2429_ = lean_box(v_res_2428_);
return v_r_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object* v_env_2430_, lean_object* v_catName_2431_, lean_object* v_declName_2432_, uint8_t v_behavior_2433_){
_start:
{
uint8_t v___x_2434_; 
lean_inc_ref(v_env_2430_);
v___x_2434_ = l_Lean_Parser_isParserCategory(v_env_2430_, v_catName_2431_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2435_ = l_Lean_Parser_parserExtension;
v___x_2436_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2436_, 0, v_catName_2431_);
lean_ctor_set(v___x_2436_, 1, v_declName_2432_);
lean_ctor_set_uint8(v___x_2436_, sizeof(void*)*2, v_behavior_2433_);
v___x_2437_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2435_, v_env_2430_, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
return v___x_2438_;
}
else
{
lean_object* v___x_2439_; 
lean_dec(v_declName_2432_);
lean_dec_ref(v_env_2430_);
v___x_2439_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_2431_);
return v___x_2439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* v_env_2440_, lean_object* v_catName_2441_, lean_object* v_declName_2442_, lean_object* v_behavior_2443_){
_start:
{
uint8_t v_behavior_boxed_2444_; lean_object* v_res_2445_; 
v_behavior_boxed_2444_ = lean_unbox(v_behavior_2443_);
v_res_2445_ = l_Lean_Parser_addParserCategory(v_env_2440_, v_catName_2441_, v_declName_2442_, v_behavior_boxed_2444_);
return v_res_2445_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object* v_env_2446_, lean_object* v_catName_2447_){
_start:
{
lean_object* v___x_2448_; lean_object* v_ext_2449_; lean_object* v_toEnvExtension_2450_; lean_object* v_asyncMode_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v_categories_2454_; lean_object* v___x_2455_; 
v___x_2448_ = l_Lean_Parser_parserExtension;
v_ext_2449_ = lean_ctor_get(v___x_2448_, 1);
v_toEnvExtension_2450_ = lean_ctor_get(v_ext_2449_, 0);
v_asyncMode_2451_ = lean_ctor_get(v_toEnvExtension_2450_, 2);
v___x_2452_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2453_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2452_, v___x_2448_, v_env_2446_, v_asyncMode_2451_);
v_categories_2454_ = lean_ctor_get(v___x_2453_, 2);
lean_inc_ref(v_categories_2454_);
lean_dec(v___x_2453_);
v___x_2455_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2454_, v_catName_2447_);
lean_dec_ref(v_categories_2454_);
if (lean_obj_tag(v___x_2455_) == 0)
{
uint8_t v___x_2456_; 
v___x_2456_ = 0;
return v___x_2456_;
}
else
{
lean_object* v_val_2457_; uint8_t v_behavior_2458_; 
v_val_2457_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_val_2457_);
lean_dec_ref_known(v___x_2455_, 1);
v_behavior_2458_ = lean_ctor_get_uint8(v_val_2457_, sizeof(void*)*3);
lean_dec(v_val_2457_);
return v_behavior_2458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object* v_env_2459_, lean_object* v_catName_2460_){
_start:
{
uint8_t v_res_2461_; lean_object* v_r_2462_; 
v_res_2461_ = l_Lean_Parser_leadingIdentBehavior(v_env_2459_, v_catName_2460_);
lean_dec(v_catName_2460_);
v_r_2462_ = lean_box(v_res_2461_);
return v_r_2462_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(lean_object* v_x_2463_, lean_object* v_x_2464_){
_start:
{
if (lean_obj_tag(v_x_2464_) == 0)
{
return v_x_2463_;
}
else
{
lean_object* v_head_2465_; lean_object* v_tail_2466_; lean_object* v___x_2467_; 
v_head_2465_ = lean_ctor_get(v_x_2464_, 0);
lean_inc_n(v_head_2465_, 2);
v_tail_2466_ = lean_ctor_get(v_x_2464_, 1);
lean_inc(v_tail_2466_);
lean_dec_ref_known(v_x_2464_, 2);
v___x_2467_ = l_Lean_Data_Trie_insert___redArg(v_x_2463_, v_head_2465_, v_head_2465_);
lean_dec(v_head_2465_);
v_x_2463_ = v___x_2467_;
v_x_2464_ = v_tail_2466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__0(lean_object* v_info_2469_, lean_object* v_ctx_2470_){
_start:
{
lean_object* v_toInputContext_2471_; lean_object* v_toParserModuleContext_2472_; lean_object* v_toCacheableParserContext_2473_; lean_object* v_tokens_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2485_; 
v_toInputContext_2471_ = lean_ctor_get(v_ctx_2470_, 0);
v_toParserModuleContext_2472_ = lean_ctor_get(v_ctx_2470_, 1);
v_toCacheableParserContext_2473_ = lean_ctor_get(v_ctx_2470_, 2);
v_tokens_2474_ = lean_ctor_get(v_ctx_2470_, 3);
v_isSharedCheck_2485_ = !lean_is_exclusive(v_ctx_2470_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2476_ = v_ctx_2470_;
v_isShared_2477_ = v_isSharedCheck_2485_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_tokens_2474_);
lean_inc(v_toCacheableParserContext_2473_);
lean_inc(v_toParserModuleContext_2472_);
lean_inc(v_toInputContext_2471_);
lean_dec(v_ctx_2470_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2485_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v_collectTokens_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
v_collectTokens_2478_ = lean_ctor_get(v_info_2469_, 0);
lean_inc_ref(v_collectTokens_2478_);
lean_dec_ref(v_info_2469_);
v___x_2479_ = lean_box(0);
v___x_2480_ = lean_apply_1(v_collectTokens_2478_, v___x_2479_);
v___x_2481_ = l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(v_tokens_2474_, v___x_2480_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 3, v___x_2481_);
v___x_2483_ = v___x_2476_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_toInputContext_2471_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_toParserModuleContext_2472_);
lean_ctor_set(v_reuseFailAlloc_2484_, 2, v_toCacheableParserContext_2473_);
lean_ctor_set(v_reuseFailAlloc_2484_, 3, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1(lean_object* v_categories_2486_, lean_object* v_declName_2487_, lean_object* v___x_2488_, lean_object* v_ctx_2489_, lean_object* v_s_2490_, lean_object* v_evalFallback_x3f_2491_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_Parser_mkParserOfConstant(v_categories_2486_, v_declName_2487_, v___x_2488_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v_snd_2495_; lean_object* v_info_2496_; lean_object* v_fn_2497_; lean_object* v___f_2498_; lean_object* v___x_2499_; 
lean_dec(v_evalFallback_x3f_2491_);
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v_snd_2495_ = lean_ctor_get(v_a_2494_, 1);
lean_inc(v_snd_2495_);
lean_dec(v_a_2494_);
v_info_2496_ = lean_ctor_get(v_snd_2495_, 0);
lean_inc_ref(v_info_2496_);
v_fn_2497_ = lean_ctor_get(v_snd_2495_, 1);
lean_inc_ref(v_fn_2497_);
lean_dec(v_snd_2495_);
v___f_2498_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__0), 2, 1);
lean_closure_set(v___f_2498_, 0, v_info_2496_);
v___x_2499_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2498_, v_fn_2497_, v_ctx_2489_, v_s_2490_);
return v___x_2499_;
}
else
{
if (lean_obj_tag(v_evalFallback_x3f_2491_) == 1)
{
lean_object* v_val_2500_; lean_object* v___x_2501_; 
lean_dec_ref_known(v___x_2493_, 1);
v_val_2500_ = lean_ctor_get(v_evalFallback_x3f_2491_, 0);
lean_inc(v_val_2500_);
lean_dec_ref_known(v_evalFallback_x3f_2491_, 1);
v___x_2501_ = lean_apply_2(v_val_2500_, v_ctx_2489_, v_s_2490_);
return v___x_2501_;
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; lean_object* v___x_2506_; 
lean_dec(v_evalFallback_x3f_2491_);
lean_dec_ref(v_ctx_2489_);
v_a_2502_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2493_, 1);
v___x_2503_ = lean_io_error_to_string(v_a_2502_);
v___x_2504_ = lean_box(0);
v___x_2505_ = 1;
v___x_2506_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2490_, v___x_2503_, v___x_2504_, v___x_2505_);
return v___x_2506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed(lean_object* v_categories_2507_, lean_object* v_declName_2508_, lean_object* v___x_2509_, lean_object* v_ctx_2510_, lean_object* v_s_2511_, lean_object* v_evalFallback_x3f_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Parser_evalParserConstUnsafe___lam__1(v_categories_2507_, v_declName_2508_, v___x_2509_, v_ctx_2510_, v_s_2511_, v_evalFallback_x3f_2512_);
lean_dec_ref(v___x_2509_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* v_declName_2515_, lean_object* v_evalFallback_x3f_2516_, lean_object* v_ctx_2517_, lean_object* v_s_2518_){
_start:
{
lean_object* v_toParserModuleContext_2519_; lean_object* v_env_2520_; lean_object* v_options_2521_; lean_object* v___x_2522_; lean_object* v_ext_2523_; lean_object* v_toEnvExtension_2524_; lean_object* v_asyncMode_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v_categories_2528_; lean_object* v___x_2529_; lean_object* v___f_2530_; lean_object* v___x_2531_; 
v_toParserModuleContext_2519_ = lean_ctor_get(v_ctx_2517_, 1);
v_env_2520_ = lean_ctor_get(v_toParserModuleContext_2519_, 0);
v_options_2521_ = lean_ctor_get(v_toParserModuleContext_2519_, 1);
v___x_2522_ = l_Lean_Parser_parserExtension;
v_ext_2523_ = lean_ctor_get(v___x_2522_, 1);
v_toEnvExtension_2524_ = lean_ctor_get(v_ext_2523_, 0);
v_asyncMode_2525_ = lean_ctor_get(v_toEnvExtension_2524_, 2);
v___x_2526_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref_n(v_env_2520_, 2);
v___x_2527_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2526_, v___x_2522_, v_env_2520_, v_asyncMode_2525_);
v_categories_2528_ = lean_ctor_get(v___x_2527_, 2);
lean_inc_ref(v_categories_2528_);
lean_dec(v___x_2527_);
lean_inc_ref(v_options_2521_);
v___x_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2529_, 0, v_env_2520_);
lean_ctor_set(v___x_2529_, 1, v_options_2521_);
v___f_2530_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2530_, 0, v_categories_2528_);
lean_closure_set(v___f_2530_, 1, v_declName_2515_);
lean_closure_set(v___f_2530_, 2, v___x_2529_);
lean_closure_set(v___f_2530_, 3, v_ctx_2517_);
lean_closure_set(v___f_2530_, 4, v_s_2518_);
lean_closure_set(v___f_2530_, 5, v_evalFallback_x3f_2516_);
v___x_2531_ = l_unsafeBaseIO___redArg(v___f_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object* v_name_2532_, lean_object* v_decl_2533_, lean_object* v_ref_2534_){
_start:
{
lean_object* v_defValue_2536_; lean_object* v_descr_2537_; lean_object* v_deprecation_x3f_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_defValue_2536_ = lean_ctor_get(v_decl_2533_, 0);
v_descr_2537_ = lean_ctor_get(v_decl_2533_, 1);
v_deprecation_x3f_2538_ = lean_ctor_get(v_decl_2533_, 2);
v___x_2539_ = lean_alloc_ctor(1, 0, 1);
v___x_2540_ = lean_unbox(v_defValue_2536_);
lean_ctor_set_uint8(v___x_2539_, 0, v___x_2540_);
lean_inc(v_deprecation_x3f_2538_);
lean_inc_ref(v_descr_2537_);
lean_inc_n(v_name_2532_, 2);
v___x_2541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2541_, 0, v_name_2532_);
lean_ctor_set(v___x_2541_, 1, v_ref_2534_);
lean_ctor_set(v___x_2541_, 2, v___x_2539_);
lean_ctor_set(v___x_2541_, 3, v_descr_2537_);
lean_ctor_set(v___x_2541_, 4, v_deprecation_x3f_2538_);
v___x_2542_ = lean_register_option(v_name_2532_, v___x_2541_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2550_; 
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2550_ == 0)
{
lean_object* v_unused_2551_; 
v_unused_2551_ = lean_ctor_get(v___x_2542_, 0);
lean_dec(v_unused_2551_);
v___x_2544_ = v___x_2542_;
v_isShared_2545_ = v_isSharedCheck_2550_;
goto v_resetjp_2543_;
}
else
{
lean_dec(v___x_2542_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2550_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v___x_2548_; 
lean_inc(v_defValue_2536_);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v_name_2532_);
lean_ctor_set(v___x_2546_, 1, v_defValue_2536_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2546_);
v___x_2548_ = v___x_2544_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec(v_name_2532_);
v_a_2552_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2542_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2542_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2560_, lean_object* v_decl_2561_, lean_object* v_ref_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v_name_2560_, v_decl_2561_, v_ref_2562_);
lean_dec_ref(v_decl_2561_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2582_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2583_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2584_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2585_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v___x_2582_, v___x_2583_, v___x_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object* v_a_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(lean_object* v_o_2591_, lean_object* v_k_2592_, uint8_t v_v_2593_){
_start:
{
lean_object* v_map_2594_; uint8_t v_hasTrace_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2609_; 
v_map_2594_ = lean_ctor_get(v_o_2591_, 0);
v_hasTrace_2595_ = lean_ctor_get_uint8(v_o_2591_, sizeof(void*)*1);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_o_2591_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2597_ = v_o_2591_;
v_isShared_2598_ = v_isSharedCheck_2609_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_map_2594_);
lean_dec(v_o_2591_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2609_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2599_, 0, v_v_2593_);
lean_inc(v_k_2592_);
v___x_2600_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2592_, v___x_2599_, v_map_2594_);
if (v_hasTrace_2595_ == 0)
{
lean_object* v___x_2601_; uint8_t v___x_2602_; lean_object* v___x_2604_; 
v___x_2601_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_2602_ = l_Lean_Name_isPrefixOf(v___x_2601_, v_k_2592_);
lean_dec(v_k_2592_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2600_);
v___x_2604_ = v___x_2597_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2600_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_ctor_set_uint8(v___x_2604_, sizeof(void*)*1, v___x_2602_);
return v___x_2604_;
}
}
else
{
lean_object* v___x_2607_; 
lean_dec(v_k_2592_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2600_);
v___x_2607_ = v___x_2597_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2600_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*1, v_hasTrace_2595_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___boxed(lean_object* v_o_2610_, lean_object* v_k_2611_, lean_object* v_v_2612_){
_start:
{
uint8_t v_v_boxed_2613_; lean_object* v_res_2614_; 
v_v_boxed_2613_ = lean_unbox(v_v_2612_);
v_res_2614_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_o_2610_, v_k_2611_, v_v_boxed_2613_);
return v_res_2614_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(lean_object* v_opts_2615_, lean_object* v_opt_2616_){
_start:
{
lean_object* v_name_2617_; lean_object* v_defValue_2618_; lean_object* v_map_2619_; lean_object* v___x_2620_; 
v_name_2617_ = lean_ctor_get(v_opt_2616_, 0);
v_defValue_2618_ = lean_ctor_get(v_opt_2616_, 1);
v_map_2619_ = lean_ctor_get(v_opts_2615_, 0);
v___x_2620_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2619_, v_name_2617_);
if (lean_obj_tag(v___x_2620_) == 0)
{
uint8_t v___x_2621_; 
v___x_2621_ = lean_unbox(v_defValue_2618_);
return v___x_2621_;
}
else
{
lean_object* v_val_2622_; 
v_val_2622_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_val_2622_);
lean_dec_ref_known(v___x_2620_, 1);
if (lean_obj_tag(v_val_2622_) == 1)
{
uint8_t v_v_2623_; 
v_v_2623_ = lean_ctor_get_uint8(v_val_2622_, 0);
lean_dec_ref_known(v_val_2622_, 0);
return v_v_2623_;
}
else
{
uint8_t v___x_2624_; 
lean_dec(v_val_2622_);
v___x_2624_ = lean_unbox(v_defValue_2618_);
return v___x_2624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1___boxed(lean_object* v_opts_2625_, lean_object* v_opt_2626_){
_start:
{
uint8_t v_res_2627_; lean_object* v_r_2628_; 
v_res_2627_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_opts_2625_, v_opt_2626_);
lean_dec_ref(v_opt_2626_);
lean_dec_ref(v_opts_2625_);
v_r_2628_ = lean_box(v_res_2627_);
return v_r_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0(uint8_t v_suppressInsideQuot_2634_, lean_object* v_ctx_2635_){
_start:
{
lean_object* v_toParserModuleContext_2636_; lean_object* v_toInputContext_2637_; lean_object* v_toCacheableParserContext_2638_; lean_object* v_tokens_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2659_; 
v_toParserModuleContext_2636_ = lean_ctor_get(v_ctx_2635_, 1);
v_toInputContext_2637_ = lean_ctor_get(v_ctx_2635_, 0);
v_toCacheableParserContext_2638_ = lean_ctor_get(v_ctx_2635_, 2);
v_tokens_2639_ = lean_ctor_get(v_ctx_2635_, 3);
v_isSharedCheck_2659_ = !lean_is_exclusive(v_ctx_2635_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2641_ = v_ctx_2635_;
v_isShared_2642_ = v_isSharedCheck_2659_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_tokens_2639_);
lean_inc(v_toCacheableParserContext_2638_);
lean_inc(v_toParserModuleContext_2636_);
lean_inc(v_toInputContext_2637_);
lean_dec(v_ctx_2635_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2659_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_env_2643_; lean_object* v_options_2644_; lean_object* v_currNamespace_2645_; lean_object* v_openDecls_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2658_; 
v_env_2643_ = lean_ctor_get(v_toParserModuleContext_2636_, 0);
v_options_2644_ = lean_ctor_get(v_toParserModuleContext_2636_, 1);
v_currNamespace_2645_ = lean_ctor_get(v_toParserModuleContext_2636_, 2);
v_openDecls_2646_ = lean_ctor_get(v_toParserModuleContext_2636_, 3);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_toParserModuleContext_2636_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2648_ = v_toParserModuleContext_2636_;
v_isShared_2649_ = v_isSharedCheck_2658_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_openDecls_2646_);
lean_inc(v_currNamespace_2645_);
lean_inc(v_options_2644_);
lean_inc(v_env_2643_);
lean_dec(v_toParserModuleContext_2636_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2658_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2650_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_2651_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_2644_, v___x_2650_, v_suppressInsideQuot_2634_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 1, v___x_2651_);
v___x_2653_ = v___x_2648_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_env_2643_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2657_, 2, v_currNamespace_2645_);
lean_ctor_set(v_reuseFailAlloc_2657_, 3, v_openDecls_2646_);
v___x_2653_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2655_; 
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 1, v___x_2653_);
v___x_2655_ = v___x_2641_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_toInputContext_2637_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_toCacheableParserContext_2638_);
lean_ctor_set(v_reuseFailAlloc_2656_, 3, v_tokens_2639_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0___boxed(lean_object* v_suppressInsideQuot_2660_, lean_object* v_ctx_2661_){
_start:
{
uint8_t v_suppressInsideQuot_boxed_2662_; lean_object* v_res_2663_; 
v_suppressInsideQuot_boxed_2662_ = lean_unbox(v_suppressInsideQuot_2660_);
v_res_2663_ = l_Lean_Parser_evalInsideQuot___lam__0(v_suppressInsideQuot_boxed_2662_, v_ctx_2661_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object* v_fn_2664_, lean_object* v_declName_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_toCacheableParserContext_2668_; lean_object* v_toParserModuleContext_2669_; lean_object* v_quotDepth_2670_; uint8_t v_suppressInsideQuot_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; 
v_toCacheableParserContext_2668_ = lean_ctor_get(v___y_2666_, 2);
v_toParserModuleContext_2669_ = lean_ctor_get(v___y_2666_, 1);
v_quotDepth_2670_ = lean_ctor_get(v_toCacheableParserContext_2668_, 1);
v_suppressInsideQuot_2671_ = lean_ctor_get_uint8(v_toCacheableParserContext_2668_, sizeof(void*)*4);
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = lean_nat_dec_lt(v___x_2672_, v_quotDepth_2670_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; 
lean_dec(v_declName_2665_);
v___x_2674_ = lean_apply_2(v_fn_2664_, v___y_2666_, v___y_2667_);
return v___x_2674_;
}
else
{
if (v_suppressInsideQuot_2671_ == 0)
{
lean_object* v_env_2675_; lean_object* v_options_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_env_2675_ = lean_ctor_get(v_toParserModuleContext_2669_, 0);
v_options_2676_ = lean_ctor_get(v_toParserModuleContext_2669_, 1);
v___x_2677_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_2678_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_2676_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; 
lean_dec(v_declName_2665_);
v___x_2679_ = lean_apply_2(v_fn_2664_, v___y_2666_, v___y_2667_);
return v___x_2679_;
}
else
{
uint8_t v___x_2680_; 
lean_inc(v_declName_2665_);
lean_inc_ref(v_env_2675_);
v___x_2680_ = l_Lean_Environment_contains(v_env_2675_, v_declName_2665_, v___x_2678_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; 
lean_dec(v_declName_2665_);
v___x_2681_ = lean_apply_2(v_fn_2664_, v___y_2666_, v___y_2667_);
return v___x_2681_;
}
else
{
lean_object* v___x_2682_; lean_object* v___f_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2682_ = lean_box(v_suppressInsideQuot_2671_);
v___f_2683_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2683_, 0, v___x_2682_);
v___x_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2684_, 0, v_fn_2664_);
v___x_2685_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_2685_, 0, v_declName_2665_);
lean_closure_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2683_, v___x_2685_, v___y_2666_, v___y_2667_);
return v___x_2686_;
}
}
}
else
{
lean_object* v___x_2687_; 
lean_dec(v_declName_2665_);
v___x_2687_ = lean_apply_2(v_fn_2664_, v___y_2666_, v___y_2667_);
return v___x_2687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object* v_declName_2688_, lean_object* v_p_2689_){
_start:
{
lean_object* v_info_2690_; lean_object* v_fn_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2699_; 
v_info_2690_ = lean_ctor_get(v_p_2689_, 0);
v_fn_2691_ = lean_ctor_get(v_p_2689_, 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_p_2689_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2693_ = v_p_2689_;
v_isShared_2694_ = v_isSharedCheck_2699_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_fn_2691_);
lean_inc(v_info_2690_);
lean_dec(v_p_2689_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2699_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___f_2695_; lean_object* v___x_2697_; 
v___f_2695_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__1), 4, 2);
lean_closure_set(v___f_2695_, 0, v_fn_2691_);
lean_closure_set(v___f_2695_, 1, v_declName_2688_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v___f_2695_);
v___x_2697_ = v___x_2693_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_info_2690_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___f_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object* v_catName_2700_, lean_object* v_declName_2701_, uint8_t v_leading_2702_, lean_object* v_p_2703_, lean_object* v_prio_2704_){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v_p_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2706_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_2707_ = lean_st_ref_get(v___x_2706_);
lean_inc_n(v_declName_2701_, 2);
v_p_2708_ = l_Lean_Parser_evalInsideQuot(v_declName_2701_, v_p_2703_);
lean_inc_ref(v_p_2708_);
v___x_2709_ = l_Lean_Parser_addParser(v___x_2707_, v_catName_2700_, v_declName_2701_, v_leading_2702_, v_p_2708_, v_prio_2704_);
v___x_2710_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_2709_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v_info_2715_; lean_object* v_collectKinds_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2712_ = lean_st_ref_swap(v___x_2706_, v_a_2711_);
lean_dec(v___x_2712_);
v___x_2713_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_2714_ = lean_st_ref_take(v___x_2713_);
v_info_2715_ = lean_ctor_get(v_p_2708_, 0);
lean_inc_ref(v_info_2715_);
lean_dec_ref(v_p_2708_);
v_collectKinds_2716_ = lean_ctor_get(v_info_2715_, 1);
lean_inc_ref(v_collectKinds_2716_);
v___x_2717_ = lean_apply_1(v_collectKinds_2716_, v___x_2714_);
v___x_2718_ = lean_st_ref_put(v___x_2713_, v___x_2717_);
v___x_2719_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_2715_, v_declName_2701_);
return v___x_2719_;
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v_p_2708_);
lean_dec(v_declName_2701_);
v_a_2720_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2710_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2710_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* v_catName_2728_, lean_object* v_declName_2729_, lean_object* v_leading_2730_, lean_object* v_p_2731_, lean_object* v_prio_2732_, lean_object* v_a_2733_){
_start:
{
uint8_t v_leading_boxed_2734_; lean_object* v_res_2735_; 
v_leading_boxed_2734_ = lean_unbox(v_leading_2730_);
v_res_2735_ = l_Lean_Parser_addBuiltinParser(v_catName_2728_, v_declName_2729_, v_leading_boxed_2734_, v_p_2731_, v_prio_2732_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* v_catName_2736_, lean_object* v_declName_2737_, lean_object* v_p_2738_, lean_object* v_prio_2739_){
_start:
{
uint8_t v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = 1;
v___x_2742_ = l_Lean_Parser_addBuiltinParser(v_catName_2736_, v_declName_2737_, v___x_2741_, v_p_2738_, v_prio_2739_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object* v_catName_2743_, lean_object* v_declName_2744_, lean_object* v_p_2745_, lean_object* v_prio_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_Parser_addBuiltinLeadingParser(v_catName_2743_, v_declName_2744_, v_p_2745_, v_prio_2746_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* v_catName_2749_, lean_object* v_declName_2750_, lean_object* v_p_2751_, lean_object* v_prio_2752_){
_start:
{
uint8_t v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = 0;
v___x_2755_ = l_Lean_Parser_addBuiltinParser(v_catName_2749_, v_declName_2750_, v___x_2754_, v_p_2751_, v_prio_2752_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object* v_catName_2756_, lean_object* v_declName_2757_, lean_object* v_p_2758_, lean_object* v_prio_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_Parser_addBuiltinTrailingParser(v_catName_2756_, v_declName_2757_, v_p_2758_, v_prio_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object* v_kind_2762_){
_start:
{
uint8_t v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2763_ = 1;
lean_inc(v_kind_2762_);
v___x_2764_ = l_Lean_Name_toString(v_kind_2762_, v___x_2763_);
v___x_2765_ = l_Lean_Parser_mkAntiquot(v___x_2764_, v_kind_2762_, v___x_2763_, v___x_2763_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object* v_kind_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v___x_2769_; lean_object* v_fn_2770_; lean_object* v___x_2771_; 
v___x_2769_ = l_Lean_Parser_mkCategoryAntiquotParser(v_kind_2766_);
v_fn_2770_ = lean_ctor_get(v___x_2769_, 1);
lean_inc_ref(v_fn_2770_);
lean_dec_ref(v___x_2769_);
v___x_2771_ = lean_apply_2(v_fn_2770_, v_a_2767_, v_a_2768_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl___lam__0(lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2775_; lean_object* v_fn_2776_; lean_object* v___x_2777_; 
v___x_2775_ = l_Lean_Parser_mkCategoryAntiquotParser(v___y_2772_);
v_fn_2776_ = lean_ctor_get(v___x_2775_, 1);
lean_inc_ref(v_fn_2776_);
lean_dec_ref(v___x_2775_);
v___x_2777_ = lean_apply_2(v_fn_2776_, v___y_2773_, v___y_2774_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* v_catName_2786_, lean_object* v_ctx_2787_, lean_object* v_s_2788_){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; uint8_t v___x_2792_; lean_object* v___y_2794_; 
v___x_2789_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2790_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__1));
v___x_2791_ = lean_name_eq(v_catName_2786_, v___x_2790_);
v___x_2792_ = 1;
if (v___x_2791_ == 0)
{
v___y_2794_ = v_catName_2786_;
goto v___jp_2793_;
}
else
{
lean_object* v___x_2816_; 
lean_dec(v_catName_2786_);
v___x_2816_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__5));
v___y_2794_ = v___x_2816_;
goto v___jp_2793_;
}
v___jp_2793_:
{
lean_object* v_toParserModuleContext_2795_; lean_object* v_env_2796_; lean_object* v___x_2797_; lean_object* v_ext_2798_; lean_object* v_toEnvExtension_2799_; lean_object* v_asyncMode_2800_; lean_object* v___x_2801_; lean_object* v_categories_2802_; lean_object* v___x_2803_; 
v_toParserModuleContext_2795_ = lean_ctor_get(v_ctx_2787_, 1);
v_env_2796_ = lean_ctor_get(v_toParserModuleContext_2795_, 0);
v___x_2797_ = l_Lean_Parser_parserExtension;
v_ext_2798_ = lean_ctor_get(v___x_2797_, 1);
v_toEnvExtension_2799_ = lean_ctor_get(v_ext_2798_, 0);
v_asyncMode_2800_ = lean_ctor_get(v_toEnvExtension_2799_, 2);
lean_inc_ref(v_env_2796_);
v___x_2801_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2789_, v___x_2797_, v_env_2796_, v_asyncMode_2800_);
v_categories_2802_ = lean_ctor_get(v___x_2801_, 2);
lean_inc_ref(v_categories_2802_);
lean_dec(v___x_2801_);
v___x_2803_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2802_, v___y_2794_);
lean_dec_ref(v_categories_2802_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
lean_dec_ref(v_ctx_2787_);
v___x_2804_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__2));
v___x_2805_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2794_, v___x_2792_);
v___x_2806_ = lean_string_append(v___x_2804_, v___x_2805_);
lean_dec_ref(v___x_2805_);
v___x_2807_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__3));
v___x_2808_ = lean_string_append(v___x_2806_, v___x_2807_);
v___x_2809_ = lean_box(0);
v___x_2810_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2788_, v___x_2808_, v___x_2809_, v___x_2792_);
return v___x_2810_;
}
else
{
lean_object* v_val_2811_; lean_object* v_tables_2812_; uint8_t v_behavior_2813_; lean_object* v___f_2814_; lean_object* v___x_2815_; 
v_val_2811_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_val_2811_);
lean_dec_ref_known(v___x_2803_, 1);
v_tables_2812_ = lean_ctor_get(v_val_2811_, 2);
lean_inc_ref(v_tables_2812_);
v_behavior_2813_ = lean_ctor_get_uint8(v_val_2811_, sizeof(void*)*3);
lean_dec(v_val_2811_);
lean_inc(v___y_2794_);
v___f_2814_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl___lam__0), 3, 1);
lean_closure_set(v___f_2814_, 0, v___y_2794_);
v___x_2815_ = l_Lean_Parser_prattParser(v___y_2794_, v_tables_2812_, v_behavior_2813_, v___f_2814_, v_ctx_2787_, v_s_2788_);
return v___x_2815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2819_ = l_Lean_Parser_categoryParserFnRef;
v___x_2820_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_));
v___x_2821_ = lean_st_ref_swap(v___x_2819_, v___x_2820_);
lean_dec(v___x_2821_);
v___x_2822_ = lean_box(0);
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object* v_a_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
return v_res_2825_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2826_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
v___x_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object* v_ext_2831_, lean_object* v_b_2832_, uint8_t v_kind_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_toCold_2837_; lean_object* v_currNamespace_2838_; lean_object* v___x_2839_; lean_object* v_env_2840_; lean_object* v_nextMacroScope_2841_; lean_object* v_ngen_2842_; lean_object* v_auxDeclNGen_2843_; lean_object* v_traceState_2844_; lean_object* v_messages_2845_; lean_object* v_infoState_2846_; lean_object* v_snapshotTasks_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2859_; 
v_toCold_2837_ = lean_ctor_get(v___y_2834_, 0);
v_currNamespace_2838_ = lean_ctor_get(v_toCold_2837_, 4);
v___x_2839_ = lean_st_ref_take(v___y_2835_);
v_env_2840_ = lean_ctor_get(v___x_2839_, 0);
v_nextMacroScope_2841_ = lean_ctor_get(v___x_2839_, 1);
v_ngen_2842_ = lean_ctor_get(v___x_2839_, 2);
v_auxDeclNGen_2843_ = lean_ctor_get(v___x_2839_, 3);
v_traceState_2844_ = lean_ctor_get(v___x_2839_, 4);
v_messages_2845_ = lean_ctor_get(v___x_2839_, 6);
v_infoState_2846_ = lean_ctor_get(v___x_2839_, 7);
v_snapshotTasks_2847_ = lean_ctor_get(v___x_2839_, 8);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2859_ == 0)
{
lean_object* v_unused_2860_; 
v_unused_2860_ = lean_ctor_get(v___x_2839_, 5);
lean_dec(v_unused_2860_);
v___x_2849_ = v___x_2839_;
v_isShared_2850_ = v_isSharedCheck_2859_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_snapshotTasks_2847_);
lean_inc(v_infoState_2846_);
lean_inc(v_messages_2845_);
lean_inc(v_traceState_2844_);
lean_inc(v_auxDeclNGen_2843_);
lean_inc(v_ngen_2842_);
lean_inc(v_nextMacroScope_2841_);
lean_inc(v_env_2840_);
lean_dec(v___x_2839_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2859_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
lean_inc(v_currNamespace_2838_);
v___x_2851_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2840_, v_ext_2831_, v_b_2832_, v_kind_2833_, v_currNamespace_2838_);
v___x_2852_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 5, v___x_2852_);
lean_ctor_set(v___x_2849_, 0, v___x_2851_);
v___x_2854_ = v___x_2849_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2851_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_nextMacroScope_2841_);
lean_ctor_set(v_reuseFailAlloc_2858_, 2, v_ngen_2842_);
lean_ctor_set(v_reuseFailAlloc_2858_, 3, v_auxDeclNGen_2843_);
lean_ctor_set(v_reuseFailAlloc_2858_, 4, v_traceState_2844_);
lean_ctor_set(v_reuseFailAlloc_2858_, 5, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2858_, 6, v_messages_2845_);
lean_ctor_set(v_reuseFailAlloc_2858_, 7, v_infoState_2846_);
lean_ctor_set(v_reuseFailAlloc_2858_, 8, v_snapshotTasks_2847_);
v___x_2854_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2855_ = lean_st_ref_put(v___y_2835_, v___x_2854_);
v___x_2856_ = lean_box(0);
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
return v___x_2857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object* v_ext_2861_, lean_object* v_b_2862_, lean_object* v_kind_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
uint8_t v_kind_boxed_2867_; lean_object* v_res_2868_; 
v_kind_boxed_2867_ = lean_unbox(v_kind_2863_);
v_res_2868_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2861_, v_b_2862_, v_kind_boxed_2867_, v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object* v_00_u03b1_2869_, lean_object* v_00_u03b2_2870_, lean_object* v_00_u03c3_2871_, lean_object* v_ext_2872_, lean_object* v_b_2873_, uint8_t v_kind_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2872_, v_b_2873_, v_kind_2874_, v___y_2875_, v___y_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object* v_00_u03b1_2879_, lean_object* v_00_u03b2_2880_, lean_object* v_00_u03c3_2881_, lean_object* v_ext_2882_, lean_object* v_b_2883_, lean_object* v_kind_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
uint8_t v_kind_boxed_2888_; lean_object* v_res_2889_; 
v_kind_boxed_2888_ = lean_unbox(v_kind_2884_);
v_res_2889_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(v_00_u03b1_2879_, v_00_u03b2_2880_, v_00_u03c3_2881_, v_ext_2882_, v_b_2883_, v_kind_boxed_2888_, v___y_2885_, v___y_2886_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object* v_x_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
if (lean_obj_tag(v_x_2890_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_a_2894_ = lean_ctor_get(v_x_2890_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v_x_2890_, 1);
v___x_2895_ = l_Lean_stringToMessageData(v_a_2894_);
v___x_2896_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2895_, v___y_2891_, v___y_2892_);
return v___x_2896_;
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
v_a_2897_ = lean_ctor_get(v_x_2890_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_x_2890_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v_x_2890_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v_x_2890_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
lean_ctor_set_tag(v___x_2899_, 0);
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object* v_x_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object* v_tk_2910_, uint8_t v_kind_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v___x_2915_; lean_object* v_env_2916_; lean_object* v___x_2917_; lean_object* v_ext_2918_; lean_object* v_toEnvExtension_2919_; lean_object* v_asyncMode_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v_tokens_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2915_ = lean_st_ref_get(v_a_2913_);
v_env_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc_ref(v_env_2916_);
lean_dec(v___x_2915_);
v___x_2917_ = l_Lean_Parser_parserExtension;
v_ext_2918_ = lean_ctor_get(v___x_2917_, 1);
v_toEnvExtension_2919_ = lean_ctor_get(v_ext_2918_, 0);
v_asyncMode_2920_ = lean_ctor_get(v_toEnvExtension_2919_, 2);
v___x_2921_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2922_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2921_, v___x_2917_, v_env_2916_, v_asyncMode_2920_);
v_tokens_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc_ref(v_tokens_2923_);
lean_dec(v___x_2922_);
lean_inc_ref(v_tk_2910_);
v___x_2924_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_2923_, v_tk_2910_);
v___x_2925_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v___x_2924_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_dec_ref_known(v___x_2925_, 1);
v___x_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2926_, 0, v_tk_2910_);
v___x_2927_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_2917_, v___x_2926_, v_kind_2911_, v_a_2912_, v_a_2913_);
return v___x_2927_;
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec_ref(v_tk_2910_);
v_a_2928_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2925_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2925_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object* v_tk_2936_, lean_object* v_kind_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
uint8_t v_kind_boxed_2941_; lean_object* v_res_2942_; 
v_kind_boxed_2941_ = lean_unbox(v_kind_2937_);
v_res_2942_ = l_Lean_Parser_addToken(v_tk_2936_, v_kind_boxed_2941_, v_a_2938_, v_a_2939_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_object* v_00_u03b1_2943_, lean_object* v_x_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2944_, v___y_2945_, v___y_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_x_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(v_00_u03b1_2949_, v_x_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object* v_env_2955_, lean_object* v_k_2956_){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2957_ = l_Lean_Parser_parserExtension;
v___x_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2958_, 0, v_k_2956_);
v___x_2959_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2957_, v_env_2955_, v___x_2958_);
return v___x_2959_;
}
}
static uint8_t _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0(void){
_start:
{
lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2960_ = lean_box(0);
v___x_2961_ = lean_internal_is_stage0(v___x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object* v_env_2962_, lean_object* v_k_2963_){
_start:
{
lean_object* v___x_2964_; lean_object* v_ext_2965_; lean_object* v_toEnvExtension_2966_; lean_object* v_asyncMode_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v_kinds_2970_; uint8_t v___x_2971_; 
v___x_2964_ = l_Lean_Parser_parserExtension;
v_ext_2965_ = lean_ctor_get(v___x_2964_, 1);
v_toEnvExtension_2966_ = lean_ctor_get(v_ext_2965_, 0);
v_asyncMode_2967_ = lean_ctor_get(v_toEnvExtension_2966_, 2);
v___x_2968_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_2962_);
v___x_2969_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2968_, v___x_2964_, v_env_2962_, v_asyncMode_2967_);
v_kinds_2970_ = lean_ctor_get(v___x_2969_, 1);
lean_inc_ref(v_kinds_2970_);
lean_dec(v___x_2969_);
v___x_2971_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_2970_, v_k_2963_);
lean_dec_ref(v_kinds_2970_);
if (v___x_2971_ == 0)
{
uint8_t v___x_2972_; 
v___x_2972_ = lean_uint8_once(&l_Lean_Parser_isValidSyntaxNodeKind___closed__0, &l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once, _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0);
if (v___x_2972_ == 0)
{
lean_dec(v_k_2963_);
lean_dec_ref(v_env_2962_);
return v___x_2972_;
}
else
{
uint8_t v___x_2973_; 
v___x_2973_ = l_Lean_Environment_contains(v_env_2962_, v_k_2963_, v___x_2972_);
return v___x_2973_;
}
}
else
{
lean_dec(v_k_2963_);
lean_dec_ref(v_env_2962_);
return v___x_2971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* v_env_2974_, lean_object* v_k_2975_){
_start:
{
uint8_t v_res_2976_; lean_object* v_r_2977_; 
v_res_2976_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_2974_, v_k_2975_);
v_r_2977_ = lean_box(v_res_2976_);
return v_r_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds___lam__0(lean_object* v_ks_2978_, lean_object* v_k_2979_, lean_object* v_x_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2981_, 0, v_k_2979_);
lean_ctor_set(v___x_2981_, 1, v_ks_2978_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2982_, lean_object* v_keys_2983_, lean_object* v_vals_2984_, lean_object* v_i_2985_, lean_object* v_acc_2986_){
_start:
{
lean_object* v___x_2987_; uint8_t v___x_2988_; 
v___x_2987_ = lean_array_get_size(v_keys_2983_);
v___x_2988_ = lean_nat_dec_lt(v_i_2985_, v___x_2987_);
if (v___x_2988_ == 0)
{
lean_dec(v_i_2985_);
lean_dec(v_f_2982_);
return v_acc_2986_;
}
else
{
lean_object* v_k_2989_; lean_object* v_v_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_k_2989_ = lean_array_fget_borrowed(v_keys_2983_, v_i_2985_);
v_v_2990_ = lean_array_fget_borrowed(v_vals_2984_, v_i_2985_);
lean_inc(v_f_2982_);
lean_inc(v_v_2990_);
lean_inc(v_k_2989_);
v___x_2991_ = lean_apply_3(v_f_2982_, v_acc_2986_, v_k_2989_, v_v_2990_);
v___x_2992_ = lean_unsigned_to_nat(1u);
v___x_2993_ = lean_nat_add(v_i_2985_, v___x_2992_);
lean_dec(v_i_2985_);
v_i_2985_ = v___x_2993_;
v_acc_2986_ = v___x_2991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2995_, lean_object* v_keys_2996_, lean_object* v_vals_2997_, lean_object* v_i_2998_, lean_object* v_acc_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2995_, v_keys_2996_, v_vals_2997_, v_i_2998_, v_acc_2999_);
lean_dec_ref(v_vals_2997_);
lean_dec_ref(v_keys_2996_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3001_, lean_object* v_as_3002_, size_t v_i_3003_, size_t v_stop_3004_, lean_object* v_b_3005_){
_start:
{
lean_object* v___y_3007_; uint8_t v___x_3011_; 
v___x_3011_ = lean_usize_dec_eq(v_i_3003_, v_stop_3004_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_array_uget_borrowed(v_as_3002_, v_i_3003_);
switch(lean_obj_tag(v___x_3012_))
{
case 0:
{
lean_object* v_key_3013_; lean_object* v_val_3014_; lean_object* v___x_3015_; 
v_key_3013_ = lean_ctor_get(v___x_3012_, 0);
v_val_3014_ = lean_ctor_get(v___x_3012_, 1);
lean_inc(v_f_3001_);
lean_inc(v_val_3014_);
lean_inc(v_key_3013_);
v___x_3015_ = lean_apply_3(v_f_3001_, v_b_3005_, v_key_3013_, v_val_3014_);
v___y_3007_ = v___x_3015_;
goto v___jp_3006_;
}
case 1:
{
lean_object* v_node_3016_; lean_object* v___x_3017_; 
v_node_3016_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_f_3001_);
v___x_3017_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3001_, v_node_3016_, v_b_3005_);
v___y_3007_ = v___x_3017_;
goto v___jp_3006_;
}
default: 
{
v___y_3007_ = v_b_3005_;
goto v___jp_3006_;
}
}
}
else
{
lean_dec(v_f_3001_);
return v_b_3005_;
}
v___jp_3006_:
{
size_t v___x_3008_; size_t v___x_3009_; 
v___x_3008_ = ((size_t)1ULL);
v___x_3009_ = lean_usize_add(v_i_3003_, v___x_3008_);
v_i_3003_ = v___x_3009_;
v_b_3005_ = v___y_3007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3018_, lean_object* v_x_3019_, lean_object* v_x_3020_){
_start:
{
if (lean_obj_tag(v_x_3019_) == 0)
{
lean_object* v_es_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; 
v_es_3021_ = lean_ctor_get(v_x_3019_, 0);
v___x_3022_ = lean_unsigned_to_nat(0u);
v___x_3023_ = lean_array_get_size(v_es_3021_);
v___x_3024_ = lean_nat_dec_lt(v___x_3022_, v___x_3023_);
if (v___x_3024_ == 0)
{
lean_dec(v_f_3018_);
return v_x_3020_;
}
else
{
size_t v___x_3025_; size_t v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = ((size_t)0ULL);
v___x_3026_ = lean_usize_of_nat(v___x_3023_);
v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3018_, v_es_3021_, v___x_3025_, v___x_3026_, v_x_3020_);
return v___x_3027_;
}
}
else
{
lean_object* v_ks_3028_; lean_object* v_vs_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v_ks_3028_ = lean_ctor_get(v_x_3019_, 0);
v_vs_3029_ = lean_ctor_get(v_x_3019_, 1);
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3018_, v_ks_3028_, v_vs_3029_, v___x_3030_, v_x_3020_);
return v___x_3031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3032_, lean_object* v_x_3033_, lean_object* v_x_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3032_, v_x_3033_, v_x_3034_);
lean_dec_ref(v_x_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3036_, lean_object* v_as_3037_, lean_object* v_i_3038_, lean_object* v_stop_3039_, lean_object* v_b_3040_){
_start:
{
size_t v_i_boxed_3041_; size_t v_stop_boxed_3042_; lean_object* v_res_3043_; 
v_i_boxed_3041_ = lean_unbox_usize(v_i_3038_);
lean_dec(v_i_3038_);
v_stop_boxed_3042_ = lean_unbox_usize(v_stop_3039_);
lean_dec(v_stop_3039_);
v_res_3043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3036_, v_as_3037_, v_i_boxed_3041_, v_stop_boxed_3042_, v_b_3040_);
lean_dec_ref(v_as_3037_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object* v_f_3044_, lean_object* v_x1_3045_, lean_object* v_x2_3046_, lean_object* v_x3_3047_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_apply_3(v_f_3044_, v_x1_3045_, v_x2_3046_, v_x3_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object* v_map_3049_, lean_object* v_f_3050_, lean_object* v_init_3051_){
_start:
{
lean_object* v___f_3052_; lean_object* v___x_3053_; 
v___f_3052_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3052_, 0, v_f_3050_);
v___x_3053_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v___f_3052_, v_map_3049_, v_init_3051_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object* v_map_3054_, lean_object* v_f_3055_, lean_object* v_init_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3054_, v_f_3055_, v_init_3056_);
lean_dec_ref(v_map_3054_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* v_env_3059_){
_start:
{
lean_object* v___x_3060_; lean_object* v_ext_3061_; lean_object* v_toEnvExtension_3062_; lean_object* v_asyncMode_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v_kinds_3066_; lean_object* v___f_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3060_ = l_Lean_Parser_parserExtension;
v_ext_3061_ = lean_ctor_get(v___x_3060_, 1);
v_toEnvExtension_3062_ = lean_ctor_get(v_ext_3061_, 0);
v_asyncMode_3063_ = lean_ctor_get(v_toEnvExtension_3062_, 2);
v___x_3064_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3065_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3064_, v___x_3060_, v_env_3059_, v_asyncMode_3063_);
v_kinds_3066_ = lean_ctor_get(v___x_3065_, 1);
lean_inc_ref(v_kinds_3066_);
lean_dec(v___x_3065_);
v___f_3067_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKinds___closed__0));
v___x_3068_ = lean_box(0);
v___x_3069_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_kinds_3066_, v___f_3067_, v___x_3068_);
lean_dec_ref(v_kinds_3066_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object* v_00_u03c3_3070_, lean_object* v_00_u03b2_3071_, lean_object* v_map_3072_, lean_object* v_f_3073_, lean_object* v_init_3074_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3072_, v_f_3073_, v_init_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object* v_00_u03c3_3076_, lean_object* v_00_u03b2_3077_, lean_object* v_map_3078_, lean_object* v_f_3079_, lean_object* v_init_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(v_00_u03c3_3076_, v_00_u03b2_3077_, v_map_3078_, v_f_3079_, v_init_3080_);
lean_dec_ref(v_map_3078_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object* v_map_3082_, lean_object* v_f_3083_, lean_object* v_init_3084_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3083_, v_map_3082_, v_init_3084_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object* v_map_3086_, lean_object* v_f_3087_, lean_object* v_init_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(v_map_3086_, v_f_3087_, v_init_3088_);
lean_dec_ref(v_map_3086_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object* v_00_u03c3_3090_, lean_object* v_00_u03b2_3091_, lean_object* v_map_3092_, lean_object* v_f_3093_, lean_object* v_init_3094_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3093_, v_map_3092_, v_init_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3096_, lean_object* v_00_u03b2_3097_, lean_object* v_map_3098_, lean_object* v_f_3099_, lean_object* v_init_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(v_00_u03c3_3096_, v_00_u03b2_3097_, v_map_3098_, v_f_3099_, v_init_3100_);
lean_dec_ref(v_map_3098_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3102_, lean_object* v_00_u03b1_3103_, lean_object* v_00_u03b2_3104_, lean_object* v_f_3105_, lean_object* v_x_3106_, lean_object* v_x_3107_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3105_, v_x_3106_, v_x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3109_, lean_object* v_00_u03b1_3110_, lean_object* v_00_u03b2_3111_, lean_object* v_f_3112_, lean_object* v_x_3113_, lean_object* v_x_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(v_00_u03c3_3109_, v_00_u03b1_3110_, v_00_u03b2_3111_, v_f_3112_, v_x_3113_, v_x_3114_);
lean_dec_ref(v_x_3113_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3116_, lean_object* v_00_u03b2_3117_, lean_object* v_00_u03c3_3118_, lean_object* v_f_3119_, lean_object* v_as_3120_, size_t v_i_3121_, size_t v_stop_3122_, lean_object* v_b_3123_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3119_, v_as_3120_, v_i_3121_, v_stop_3122_, v_b_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3125_, lean_object* v_00_u03b2_3126_, lean_object* v_00_u03c3_3127_, lean_object* v_f_3128_, lean_object* v_as_3129_, lean_object* v_i_3130_, lean_object* v_stop_3131_, lean_object* v_b_3132_){
_start:
{
size_t v_i_boxed_3133_; size_t v_stop_boxed_3134_; lean_object* v_res_3135_; 
v_i_boxed_3133_ = lean_unbox_usize(v_i_3130_);
lean_dec(v_i_3130_);
v_stop_boxed_3134_ = lean_unbox_usize(v_stop_3131_);
lean_dec(v_stop_3131_);
v_res_3135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3125_, v_00_u03b2_3126_, v_00_u03c3_3127_, v_f_3128_, v_as_3129_, v_i_boxed_3133_, v_stop_boxed_3134_, v_b_3132_);
lean_dec_ref(v_as_3129_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3136_, lean_object* v_00_u03b1_3137_, lean_object* v_00_u03b2_3138_, lean_object* v_f_3139_, lean_object* v_keys_3140_, lean_object* v_vals_3141_, lean_object* v_heq_3142_, lean_object* v_i_3143_, lean_object* v_acc_3144_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3139_, v_keys_3140_, v_vals_3141_, v_i_3143_, v_acc_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3146_, lean_object* v_00_u03b1_3147_, lean_object* v_00_u03b2_3148_, lean_object* v_f_3149_, lean_object* v_keys_3150_, lean_object* v_vals_3151_, lean_object* v_heq_3152_, lean_object* v_i_3153_, lean_object* v_acc_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3146_, v_00_u03b1_3147_, v_00_u03b2_3148_, v_f_3149_, v_keys_3150_, v_vals_3151_, v_heq_3152_, v_i_3153_, v_acc_3154_);
lean_dec_ref(v_vals_3151_);
lean_dec_ref(v_keys_3150_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* v_env_3156_){
_start:
{
lean_object* v___x_3157_; lean_object* v_ext_3158_; lean_object* v_toEnvExtension_3159_; lean_object* v_asyncMode_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v_tokens_3163_; 
v___x_3157_ = l_Lean_Parser_parserExtension;
v_ext_3158_ = lean_ctor_get(v___x_3157_, 1);
v_toEnvExtension_3159_ = lean_ctor_get(v_ext_3158_, 0);
v_asyncMode_3160_ = lean_ctor_get(v_toEnvExtension_3159_, 2);
v___x_3161_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3162_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3161_, v___x_3157_, v_env_3156_, v_asyncMode_3160_);
v_tokens_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc_ref(v_tokens_3163_);
lean_dec(v___x_3162_);
return v_tokens_3163_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__8));
v___x_3189_ = l_Lean_mkAtom(v___x_3188_);
return v___x_3189_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3190_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__10, &l_Lean_Parser_mkInputContext___auto__1___closed__10_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__10);
v___x_3191_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3192_ = lean_array_push(v___x_3191_, v___x_3190_);
return v___x_3192_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3203_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3204_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3205_ = lean_array_push(v___x_3204_, v___x_3203_);
return v___x_3205_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3206_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__15, &l_Lean_Parser_mkInputContext___auto__1___closed__15_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__15);
v___x_3207_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__13));
v___x_3208_ = lean_box(2);
v___x_3209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v___x_3207_);
lean_ctor_set(v___x_3209_, 2, v___x_3206_);
return v___x_3209_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__16, &l_Lean_Parser_mkInputContext___auto__1___closed__16_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__16);
v___x_3211_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__11, &l_Lean_Parser_mkInputContext___auto__1___closed__11_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__11);
v___x_3212_ = lean_array_push(v___x_3211_, v___x_3210_);
return v___x_3212_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3214_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__17, &l_Lean_Parser_mkInputContext___auto__1___closed__17_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__17);
v___x_3215_ = lean_array_push(v___x_3214_, v___x_3213_);
return v___x_3215_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3217_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__18, &l_Lean_Parser_mkInputContext___auto__1___closed__18_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__18);
v___x_3218_ = lean_array_push(v___x_3217_, v___x_3216_);
return v___x_3218_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3219_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3220_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__19, &l_Lean_Parser_mkInputContext___auto__1___closed__19_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__19);
v___x_3221_ = lean_array_push(v___x_3220_, v___x_3219_);
return v___x_3221_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3222_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3223_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__20, &l_Lean_Parser_mkInputContext___auto__1___closed__20_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__20);
v___x_3224_ = lean_array_push(v___x_3223_, v___x_3222_);
return v___x_3224_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3225_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__21, &l_Lean_Parser_mkInputContext___auto__1___closed__21_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__21);
v___x_3226_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__9));
v___x_3227_ = lean_box(2);
v___x_3228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set(v___x_3228_, 1, v___x_3226_);
lean_ctor_set(v___x_3228_, 2, v___x_3225_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__22, &l_Lean_Parser_mkInputContext___auto__1___closed__22_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__22);
v___x_3230_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3231_ = lean_array_push(v___x_3230_, v___x_3229_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3232_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__23, &l_Lean_Parser_mkInputContext___auto__1___closed__23_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__23);
v___x_3233_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3234_ = lean_box(2);
v___x_3235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3234_);
lean_ctor_set(v___x_3235_, 1, v___x_3233_);
lean_ctor_set(v___x_3235_, 2, v___x_3232_);
return v___x_3235_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3236_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__24, &l_Lean_Parser_mkInputContext___auto__1___closed__24_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__24);
v___x_3237_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3238_ = lean_array_push(v___x_3237_, v___x_3236_);
return v___x_3238_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3239_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__25, &l_Lean_Parser_mkInputContext___auto__1___closed__25_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__25);
v___x_3240_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3241_ = lean_box(2);
v___x_3242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
lean_ctor_set(v___x_3242_, 1, v___x_3240_);
lean_ctor_set(v___x_3242_, 2, v___x_3239_);
return v___x_3242_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__26, &l_Lean_Parser_mkInputContext___auto__1___closed__26_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__26);
v___x_3244_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3245_ = lean_array_push(v___x_3244_, v___x_3243_);
return v___x_3245_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3246_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__27, &l_Lean_Parser_mkInputContext___auto__1___closed__27_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__27);
v___x_3247_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3248_ = lean_box(2);
v___x_3249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
lean_ctor_set(v___x_3249_, 1, v___x_3247_);
lean_ctor_set(v___x_3249_, 2, v___x_3246_);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1(void){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__28, &l_Lean_Parser_mkInputContext___auto__1___closed__28_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__28);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object* v_input_3251_, lean_object* v_fileName_3252_, uint8_t v_normalizeLineEndings_3253_, lean_object* v_endPos_3254_){
_start:
{
lean_object* v_fst_3256_; lean_object* v_snd_3257_; lean_object* v_text_3263_; 
v_text_3263_ = l_Lean_FileMap_ofString(v_input_3251_);
if (v_normalizeLineEndings_3253_ == 0)
{
v_fst_3256_ = v_text_3263_;
v_snd_3257_ = v_endPos_3254_;
goto v___jp_3255_;
}
else
{
lean_object* v_source_3264_; lean_object* v_endPos_x27_3265_; lean_object* v___x_3266_; lean_object* v_text_3267_; lean_object* v___x_3268_; 
v_source_3264_ = lean_ctor_get(v_text_3263_, 0);
lean_inc_ref(v_source_3264_);
v_endPos_x27_3265_ = l_Lean_FileMap_toPosition(v_text_3263_, v_endPos_3254_);
lean_dec(v_endPos_3254_);
v___x_3266_ = l_String_crlfToLf(v_source_3264_);
lean_dec_ref(v_source_3264_);
v_text_3267_ = l_Lean_FileMap_ofString(v___x_3266_);
v___x_3268_ = l_Lean_FileMap_ofPosition(v_text_3267_, v_endPos_x27_3265_);
v_fst_3256_ = v_text_3267_;
v_snd_3257_ = v___x_3268_;
goto v___jp_3255_;
}
v___jp_3255_:
{
lean_object* v_source_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; 
v_source_3258_ = lean_ctor_get(v_fst_3256_, 0);
lean_inc_ref(v_source_3258_);
v___x_3259_ = lean_string_utf8_byte_size(v_source_3258_);
v___x_3260_ = lean_nat_dec_le(v_snd_3257_, v___x_3259_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
lean_dec(v_snd_3257_);
v___x_3261_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3261_, 0, v_source_3258_);
lean_ctor_set(v___x_3261_, 1, v_fileName_3252_);
lean_ctor_set(v___x_3261_, 2, v_fst_3256_);
lean_ctor_set(v___x_3261_, 3, v___x_3259_);
return v___x_3261_;
}
else
{
lean_object* v___x_3262_; 
v___x_3262_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3262_, 0, v_source_3258_);
lean_ctor_set(v___x_3262_, 1, v_fileName_3252_);
lean_ctor_set(v___x_3262_, 2, v_fst_3256_);
lean_ctor_set(v___x_3262_, 3, v_snd_3257_);
return v___x_3262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object* v_input_3269_, lean_object* v_fileName_3270_, lean_object* v_normalizeLineEndings_3271_, lean_object* v_endPos_3272_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3273_; lean_object* v_res_3274_; 
v_normalizeLineEndings_boxed_3273_ = lean_unbox(v_normalizeLineEndings_3271_);
v_res_3274_ = l_Lean_Parser_mkInputContext___redArg(v_input_3269_, v_fileName_3270_, v_normalizeLineEndings_boxed_3273_, v_endPos_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object* v_input_3275_, lean_object* v_fileName_3276_, uint8_t v_normalizeLineEndings_3277_, lean_object* v_endPos_3278_, lean_object* v_endPos__valid_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Lean_Parser_mkInputContext___redArg(v_input_3275_, v_fileName_3276_, v_normalizeLineEndings_3277_, v_endPos_3278_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object* v_input_3281_, lean_object* v_fileName_3282_, lean_object* v_normalizeLineEndings_3283_, lean_object* v_endPos_3284_, lean_object* v_endPos__valid_3285_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3286_; lean_object* v_res_3287_; 
v_normalizeLineEndings_boxed_3286_ = lean_unbox(v_normalizeLineEndings_3283_);
v_res_3287_ = l_Lean_Parser_mkInputContext(v_input_3281_, v_fileName_3282_, v_normalizeLineEndings_boxed_3286_, v_endPos_3284_, v_endPos__valid_3285_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* v_input_3290_){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3291_ = l_Lean_Parser_SyntaxStack_empty;
v___x_3292_ = lean_unsigned_to_nat(0u);
v___x_3293_ = l_Lean_Parser_initCacheForInput(v_input_3290_);
v___x_3294_ = lean_box(0);
v___x_3295_ = ((lean_object*)(l_Lean_Parser_mkParserState___closed__0));
v___x_3296_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3291_);
lean_ctor_set(v___x_3296_, 1, v___x_3292_);
lean_ctor_set(v___x_3296_, 2, v___x_3292_);
lean_ctor_set(v___x_3296_, 3, v___x_3293_);
lean_ctor_set(v___x_3296_, 4, v___x_3294_);
lean_ctor_set(v___x_3296_, 5, v___x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* v_input_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_Parser_mkParserState(v_input_3297_);
lean_dec_ref(v_input_3297_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* v_env_3301_, lean_object* v_catName_3302_, lean_object* v_input_3303_, lean_object* v_fileName_3304_){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v_p_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; lean_object* v_ictx_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v_s_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3305_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__0));
v___x_3306_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 1);
lean_closure_set(v___x_3306_, 0, v_catName_3302_);
v_p_3307_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_3307_, 0, v___x_3305_);
lean_closure_set(v_p_3307_, 1, v___x_3306_);
v___x_3308_ = 1;
v___x_3309_ = lean_string_utf8_byte_size(v_input_3303_);
lean_inc_ref(v_input_3303_);
v_ictx_3310_ = l_Lean_Parser_mkInputContext___redArg(v_input_3303_, v_fileName_3304_, v___x_3308_, v___x_3309_);
v___x_3311_ = l_Lean_Options_empty;
v___x_3312_ = lean_box(0);
v___x_3313_ = lean_box(0);
lean_inc_ref(v_env_3301_);
v___x_3314_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3314_, 0, v_env_3301_);
lean_ctor_set(v___x_3314_, 1, v___x_3311_);
lean_ctor_set(v___x_3314_, 2, v___x_3312_);
lean_ctor_set(v___x_3314_, 3, v___x_3313_);
v___x_3315_ = l_Lean_Parser_getTokenTable(v_env_3301_);
v___x_3316_ = l_Lean_Parser_mkParserState(v_input_3303_);
lean_dec_ref(v_input_3303_);
lean_inc_ref(v_ictx_3310_);
v_s_3317_ = l_Lean_Parser_ParserFn_run(v_p_3307_, v_ictx_3310_, v___x_3314_, v___x_3315_, v___x_3316_);
lean_inc_ref(v_s_3317_);
v___x_3318_ = l_Lean_Parser_ParserState_allErrors(v_s_3317_);
v___x_3319_ = lean_array_get_size(v___x_3318_);
lean_dec_ref(v___x_3318_);
v___x_3320_ = lean_unsigned_to_nat(0u);
v___x_3321_ = lean_nat_dec_eq(v___x_3319_, v___x_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3310_, v_s_3317_);
v___x_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
return v___x_3323_;
}
else
{
lean_object* v_stxStack_3324_; lean_object* v_pos_3325_; uint8_t v___x_3326_; 
v_stxStack_3324_ = lean_ctor_get(v_s_3317_, 0);
lean_inc_ref(v_stxStack_3324_);
v_pos_3325_ = lean_ctor_get(v_s_3317_, 2);
lean_inc(v_pos_3325_);
v___x_3326_ = l_Lean_Parser_InputContext_atEnd(v_ictx_3310_, v_pos_3325_);
lean_dec(v_pos_3325_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
lean_dec_ref(v_stxStack_3324_);
v___x_3327_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__1));
v___x_3328_ = l_Lean_Parser_ParserState_mkError(v_s_3317_, v___x_3327_);
v___x_3329_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3310_, v___x_3328_);
v___x_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
return v___x_3330_;
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
lean_dec_ref(v_s_3317_);
lean_dec_ref(v_ictx_3310_);
v___x_3331_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3324_);
lean_dec_ref(v_stxStack_3324_);
v___x_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
return v___x_3332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* v_addFnName_3333_, lean_object* v_catName_3334_, lean_object* v_declName_3335_, lean_object* v_prio_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v_val_3352_; lean_object* v___x_3353_; 
v___x_3340_ = lean_box(0);
v___x_3341_ = l_Lean_mkConst(v_addFnName_3333_, v___x_3340_);
v___x_3342_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_catName_3334_);
lean_inc_n(v_declName_3335_, 2);
v___x_3343_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3335_);
v___x_3344_ = l_Lean_mkConst(v_declName_3335_, v___x_3340_);
v___x_3345_ = l_Lean_mkRawNatLit(v_prio_3336_);
v___x_3346_ = lean_unsigned_to_nat(4u);
v___x_3347_ = lean_mk_empty_array_with_capacity(v___x_3346_);
v___x_3348_ = lean_array_push(v___x_3347_, v___x_3342_);
v___x_3349_ = lean_array_push(v___x_3348_, v___x_3343_);
v___x_3350_ = lean_array_push(v___x_3349_, v___x_3344_);
v___x_3351_ = lean_array_push(v___x_3350_, v___x_3345_);
v_val_3352_ = l_Lean_mkAppN(v___x_3341_, v___x_3351_);
lean_dec_ref(v___x_3351_);
v___x_3353_ = l_Lean_declareBuiltin(v_declName_3335_, v_val_3352_, v_a_3337_, v_a_3338_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object* v_addFnName_3354_, lean_object* v_catName_3355_, lean_object* v_declName_3356_, lean_object* v_prio_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3354_, v_catName_3355_, v_declName_3356_, v_prio_3357_, v_a_3358_, v_a_3359_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* v_catName_3367_, lean_object* v_declName_3368_, lean_object* v_prio_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = ((lean_object*)(l_Lean_Parser_declareLeadingBuiltinParser___closed__1));
v___x_3374_ = l_Lean_Parser_declareBuiltinParser(v___x_3373_, v_catName_3367_, v_declName_3368_, v_prio_3369_, v_a_3370_, v_a_3371_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object* v_catName_3375_, lean_object* v_declName_3376_, lean_object* v_prio_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3375_, v_declName_3376_, v_prio_3377_, v_a_3378_, v_a_3379_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* v_catName_3387_, lean_object* v_declName_3388_, lean_object* v_prio_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = ((lean_object*)(l_Lean_Parser_declareTrailingBuiltinParser___closed__1));
v___x_3394_ = l_Lean_Parser_declareBuiltinParser(v___x_3393_, v_catName_3387_, v_declName_3388_, v_prio_3389_, v_a_3390_, v_a_3391_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object* v_catName_3395_, lean_object* v_declName_3396_, lean_object* v_prio_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3395_, v_declName_3396_, v_prio_3397_, v_a_3398_, v_a_3399_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* v_args_3408_){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3409_ = l_Lean_Syntax_getNumArgs(v_args_3408_);
v___x_3410_ = lean_unsigned_to_nat(0u);
v___x_3411_ = lean_nat_dec_eq(v___x_3409_, v___x_3410_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; uint8_t v___x_3413_; 
v___x_3412_ = lean_unsigned_to_nat(1u);
v___x_3413_ = lean_nat_dec_eq(v___x_3409_, v___x_3412_);
lean_dec(v___x_3409_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; 
v___x_3414_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__1));
return v___x_3414_;
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = l_Lean_Syntax_getArg(v_args_3408_, v___x_3410_);
v___x_3416_ = l_Lean_Syntax_isNatLit_x3f(v___x_3415_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3417_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__2));
v___x_3418_ = l_Lean_Syntax_formatStx(v___x_3415_, v___x_3416_, v___x_3411_);
v___x_3419_ = l_Std_Format_defWidth;
v___x_3420_ = l_Std_Format_pretty(v___x_3418_, v___x_3419_, v___x_3410_, v___x_3410_);
v___x_3421_ = lean_string_append(v___x_3417_, v___x_3420_);
lean_dec_ref(v___x_3420_);
v___x_3422_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3423_ = lean_string_append(v___x_3421_, v___x_3422_);
v___x_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
return v___x_3424_;
}
else
{
lean_object* v_val_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_dec(v___x_3415_);
v_val_3425_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3416_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_val_3425_);
lean_dec(v___x_3416_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_val_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
}
else
{
lean_object* v___x_3433_; 
lean_dec(v___x_3409_);
v___x_3433_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__3));
return v___x_3433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* v_args_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Lean_Parser_getParserPriority(v_args_3434_);
lean_dec(v_args_3434_);
return v_res_3435_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0));
v___x_3438_ = l_Lean_stringToMessageData(v___x_3437_);
return v___x_3438_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2));
v___x_3441_ = l_Lean_stringToMessageData(v___x_3440_);
return v___x_3441_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3443_ = l_Lean_stringToMessageData(v___x_3442_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object* v_name_3447_, uint8_t v_kind_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___y_3458_; 
v___x_3452_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1);
v___x_3453_ = l_Lean_MessageData_ofName(v_name_3447_);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
switch(v_kind_3448_)
{
case 0:
{
lean_object* v___x_3465_; 
v___x_3465_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5));
v___y_3458_ = v___x_3465_;
goto v___jp_3457_;
}
case 1:
{
lean_object* v___x_3466_; 
v___x_3466_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6));
v___y_3458_ = v___x_3466_;
goto v___jp_3457_;
}
default: 
{
lean_object* v___x_3467_; 
v___x_3467_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7));
v___y_3458_ = v___x_3467_;
goto v___jp_3457_;
}
}
v___jp_3457_:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_inc_ref(v___y_3458_);
v___x_3459_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3459_, 0, v___y_3458_);
v___x_3460_ = l_Lean_MessageData_ofFormat(v___x_3459_);
v___x_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3456_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3461_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
v___x_3464_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3463_, v___y_3449_, v___y_3450_);
return v___x_3464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object* v_name_3468_, lean_object* v_kind_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
uint8_t v_kind_boxed_3473_; lean_object* v_res_3474_; 
v_kind_boxed_3473_ = lean_unbox(v_kind_3469_);
v_res_3474_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3468_, v_kind_boxed_3473_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3475_, lean_object* v_msg_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v_toCold_3480_; lean_object* v_currRecDepth_3481_; lean_object* v_ref_3482_; uint8_t v_diag_3483_; uint8_t v_suppressElabErrors_3484_; lean_object* v_ref_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_toCold_3480_ = lean_ctor_get(v___y_3477_, 0);
v_currRecDepth_3481_ = lean_ctor_get(v___y_3477_, 1);
v_ref_3482_ = lean_ctor_get(v___y_3477_, 2);
v_diag_3483_ = lean_ctor_get_uint8(v___y_3477_, sizeof(void*)*3);
v_suppressElabErrors_3484_ = lean_ctor_get_uint8(v___y_3477_, sizeof(void*)*3 + 1);
v_ref_3485_ = l_Lean_replaceRef(v_ref_3475_, v_ref_3482_);
lean_inc(v_currRecDepth_3481_);
lean_inc_ref(v_toCold_3480_);
v___x_3486_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3486_, 0, v_toCold_3480_);
lean_ctor_set(v___x_3486_, 1, v_currRecDepth_3481_);
lean_ctor_set(v___x_3486_, 2, v_ref_3485_);
lean_ctor_set_uint8(v___x_3486_, sizeof(void*)*3, v_diag_3483_);
lean_ctor_set_uint8(v___x_3486_, sizeof(void*)*3 + 1, v_suppressElabErrors_3484_);
v___x_3487_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_3476_, v___x_3486_, v___y_3478_);
lean_dec_ref_known(v___x_3486_, 3);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3488_, lean_object* v_msg_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3488_, v_msg_3489_, v___y_3490_, v___y_3491_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v_ref_3488_);
return v_res_3493_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_3496_ = l_Lean_stringToMessageData(v___x_3495_);
return v___x_3496_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_3499_ = l_Lean_stringToMessageData(v___x_3498_);
return v___x_3499_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_3502_ = l_Lean_stringToMessageData(v___x_3501_);
return v___x_3502_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_3505_ = l_Lean_stringToMessageData(v___x_3504_);
return v___x_3505_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_3508_ = l_Lean_stringToMessageData(v___x_3507_);
return v___x_3508_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_3511_ = l_Lean_stringToMessageData(v___x_3510_);
return v___x_3511_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_3514_ = l_Lean_stringToMessageData(v___x_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_3515_, lean_object* v_declHint_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; lean_object* v_env_3520_; uint8_t v___x_3521_; 
v___x_3519_ = lean_st_ref_get(v___y_3517_);
v_env_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc_ref(v_env_3520_);
lean_dec(v___x_3519_);
v___x_3521_ = l_Lean_Name_isAnonymous(v_declHint_3516_);
if (v___x_3521_ == 0)
{
uint8_t v_isExporting_3522_; 
v_isExporting_3522_ = lean_ctor_get_uint8(v_env_3520_, sizeof(void*)*8);
if (v_isExporting_3522_ == 0)
{
lean_object* v___x_3523_; 
lean_dec_ref(v_env_3520_);
lean_dec(v_declHint_3516_);
v___x_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3523_, 0, v_msg_3515_);
return v___x_3523_;
}
else
{
lean_object* v___x_3524_; uint8_t v___x_3525_; 
lean_inc_ref(v_env_3520_);
v___x_3524_ = l_Lean_Environment_setExporting(v_env_3520_, v___x_3521_);
lean_inc(v_declHint_3516_);
lean_inc_ref(v___x_3524_);
v___x_3525_ = l_Lean_Environment_contains(v___x_3524_, v_declHint_3516_, v_isExporting_3522_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; 
lean_dec_ref(v___x_3524_);
lean_dec_ref(v_env_3520_);
lean_dec(v_declHint_3516_);
v___x_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_msg_3515_);
return v___x_3526_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v_c_3532_; lean_object* v___x_3533_; 
v___x_3527_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_3528_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_3529_ = l_Lean_Options_empty;
v___x_3530_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3524_);
lean_ctor_set(v___x_3530_, 1, v___x_3527_);
lean_ctor_set(v___x_3530_, 2, v___x_3528_);
lean_ctor_set(v___x_3530_, 3, v___x_3529_);
lean_inc(v_declHint_3516_);
v___x_3531_ = l_Lean_MessageData_ofConstName(v_declHint_3516_, v___x_3521_);
v_c_3532_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3532_, 0, v___x_3530_);
lean_ctor_set(v_c_3532_, 1, v___x_3531_);
v___x_3533_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3520_, v_declHint_3516_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
lean_dec_ref(v_env_3520_);
lean_dec(v_declHint_3516_);
v___x_3534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
lean_ctor_set(v___x_3535_, 1, v_c_3532_);
v___x_3536_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3535_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
v___x_3538_ = l_Lean_MessageData_note(v___x_3537_);
v___x_3539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3539_, 0, v_msg_3515_);
lean_ctor_set(v___x_3539_, 1, v___x_3538_);
v___x_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
return v___x_3540_;
}
else
{
lean_object* v_val_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3576_; 
v_val_3541_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3543_ = v___x_3533_;
v_isShared_3544_ = v_isSharedCheck_3576_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_val_3541_);
lean_dec(v___x_3533_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3576_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v_mod_3548_; uint8_t v___x_3549_; 
v___x_3545_ = lean_box(0);
v___x_3546_ = l_Lean_Environment_header(v_env_3520_);
lean_dec_ref(v_env_3520_);
v___x_3547_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3546_);
v_mod_3548_ = lean_array_get(v___x_3545_, v___x_3547_, v_val_3541_);
lean_dec(v_val_3541_);
lean_dec_ref(v___x_3547_);
v___x_3549_ = l_Lean_isPrivateName(v_declHint_3516_);
lean_dec(v_declHint_3516_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_3551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
lean_ctor_set(v___x_3551_, 1, v_c_3532_);
v___x_3552_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_3553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3551_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
v___x_3554_ = l_Lean_MessageData_ofName(v_mod_3548_);
v___x_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3553_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
v___x_3556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_3557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3555_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = l_Lean_MessageData_note(v___x_3557_);
v___x_3559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3559_, 0, v_msg_3515_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
if (v_isShared_3544_ == 0)
{
lean_ctor_set_tag(v___x_3543_, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3559_);
v___x_3561_ = v___x_3543_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3563_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
lean_ctor_set(v___x_3564_, 1, v_c_3532_);
v___x_3565_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = l_Lean_MessageData_ofName(v_mod_3548_);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = l_Lean_MessageData_note(v___x_3570_);
v___x_3572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3572_, 0, v_msg_3515_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
if (v_isShared_3544_ == 0)
{
lean_ctor_set_tag(v___x_3543_, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3572_);
v___x_3574_ = v___x_3543_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3572_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3577_; 
lean_dec_ref(v_env_3520_);
lean_dec(v_declHint_3516_);
v___x_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3577_, 0, v_msg_3515_);
return v___x_3577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_3578_, lean_object* v_declHint_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3578_, v_declHint_3579_, v___y_3580_);
lean_dec(v___y_3580_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_3583_, lean_object* v_declHint_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v___x_3588_; lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3598_; 
v___x_3588_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3583_, v_declHint_3584_, v___y_3586_);
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3591_ = v___x_3588_;
v_isShared_3592_ = v_isSharedCheck_3598_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3588_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3598_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3593_ = l_Lean_unknownIdentifierMessageTag;
v___x_3594_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
lean_ctor_set(v___x_3594_, 1, v_a_3589_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v___x_3594_);
v___x_3596_ = v___x_3591_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_3599_, lean_object* v_declHint_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3599_, v_declHint_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3605_, lean_object* v_msg_3606_, lean_object* v_declHint_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v___x_3611_; lean_object* v_a_3612_; lean_object* v___x_3613_; 
v___x_3611_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3606_, v_declHint_3607_, v___y_3608_, v___y_3609_);
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref(v___x_3611_);
v___x_3613_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3605_, v_a_3612_, v___y_3608_, v___y_3609_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3614_, lean_object* v_msg_3615_, lean_object* v_declHint_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3614_, v_msg_3615_, v_declHint_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v_ref_3614_);
return v_res_3620_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_3622_ = l_Lean_stringToMessageData(v___x_3621_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3623_, lean_object* v_constName_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; uint8_t v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3628_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3629_ = 0;
lean_inc(v_constName_3624_);
v___x_3630_ = l_Lean_MessageData_ofConstName(v_constName_3624_, v___x_3629_);
v___x_3631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3628_);
lean_ctor_set(v___x_3631_, 1, v___x_3630_);
v___x_3632_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3631_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
v___x_3634_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3623_, v___x_3633_, v_constName_3624_, v___y_3625_, v___y_3626_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3635_, lean_object* v_constName_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3635_, v_constName_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v_ref_3635_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object* v_constName_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_ref_3645_; lean_object* v___x_3646_; 
v_ref_3645_ = lean_ctor_get(v___y_3642_, 2);
v___x_3646_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3645_, v_constName_3641_, v___y_3642_, v___y_3643_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object* v_constName_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v___x_3656_; lean_object* v_env_3657_; uint8_t v___x_3658_; lean_object* v___x_3659_; 
v___x_3656_ = lean_st_ref_get(v___y_3654_);
v_env_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc_ref(v_env_3657_);
lean_dec(v___x_3656_);
v___x_3658_ = 0;
lean_inc(v_constName_3652_);
v___x_3659_ = l_Lean_Environment_find_x3f(v_env_3657_, v_constName_3652_, v___x_3658_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v___x_3660_; 
v___x_3660_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3652_, v___y_3653_, v___y_3654_);
return v___x_3660_;
}
else
{
lean_object* v_val_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec(v_constName_3652_);
v_val_3661_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3659_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_val_3661_);
lean_dec(v___x_3659_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set_tag(v___x_3663_, 0);
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_val_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object* v_constName_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
return v_res_3673_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1(void){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3675_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0));
v___x_3676_ = l_Lean_stringToMessageData(v___x_3675_);
return v___x_3676_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2));
v___x_3679_ = l_Lean_stringToMessageData(v___x_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* v_attrName_3680_, lean_object* v_catName_3681_, lean_object* v_declName_3682_, lean_object* v_stx_3683_, uint8_t v_kind_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___x_3708_; 
v___x_3708_ = l_Lean_Attribute_Builtin_getPrio(v_stx_3683_, v_a_3685_, v_a_3686_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___y_3711_; lean_object* v___y_3712_; uint8_t v___x_3740_; uint8_t v___x_3741_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
v___x_3740_ = 0;
v___x_3741_ = l_Lean_instBEqAttributeKind_beq(v_kind_3684_, v___x_3740_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; 
lean_dec(v_a_3709_);
lean_dec(v_declName_3682_);
lean_dec(v_catName_3681_);
v___x_3742_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_attrName_3680_, v_kind_3684_, v_a_3685_, v_a_3686_);
return v___x_3742_;
}
else
{
lean_dec(v_attrName_3680_);
v___y_3711_ = v_a_3685_;
v___y_3712_ = v_a_3686_;
goto v___jp_3710_;
}
v___jp_3710_:
{
lean_object* v___x_3713_; 
lean_inc(v_declName_3682_);
v___x_3713_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_declName_3682_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v___x_3715_ = l_Lean_ConstantInfo_type(v_a_3714_);
if (lean_obj_tag(v___x_3715_) == 4)
{
lean_object* v_declName_3716_; 
v_declName_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_declName_3716_);
lean_dec_ref_known(v___x_3715_, 2);
if (lean_obj_tag(v_declName_3716_) == 1)
{
lean_object* v_pre_3717_; 
v_pre_3717_ = lean_ctor_get(v_declName_3716_, 0);
lean_inc(v_pre_3717_);
if (lean_obj_tag(v_pre_3717_) == 1)
{
lean_object* v_pre_3718_; 
v_pre_3718_ = lean_ctor_get(v_pre_3717_, 0);
lean_inc(v_pre_3718_);
if (lean_obj_tag(v_pre_3718_) == 1)
{
lean_object* v_pre_3719_; 
v_pre_3719_ = lean_ctor_get(v_pre_3718_, 0);
if (lean_obj_tag(v_pre_3719_) == 0)
{
lean_object* v_str_3720_; lean_object* v_str_3721_; lean_object* v_str_3722_; lean_object* v___x_3723_; uint8_t v___x_3724_; 
v_str_3720_ = lean_ctor_get(v_declName_3716_, 1);
lean_inc_ref(v_str_3720_);
lean_dec_ref_known(v_declName_3716_, 2);
v_str_3721_ = lean_ctor_get(v_pre_3717_, 1);
lean_inc_ref(v_str_3721_);
lean_dec_ref_known(v_pre_3717_, 2);
v_str_3722_ = lean_ctor_get(v_pre_3718_, 1);
lean_inc_ref(v_str_3722_);
lean_dec_ref_known(v_pre_3718_, 2);
v___x_3723_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3724_ = lean_string_dec_eq(v_str_3722_, v___x_3723_);
lean_dec_ref(v_str_3722_);
if (v___x_3724_ == 0)
{
lean_dec_ref(v_str_3721_);
lean_dec_ref(v_str_3720_);
lean_dec(v_a_3709_);
lean_dec(v_catName_3681_);
v___y_3695_ = v_a_3714_;
v___y_3696_ = v___y_3711_;
v___y_3697_ = v___y_3712_;
goto v___jp_3694_;
}
else
{
lean_object* v___x_3725_; uint8_t v___x_3726_; 
v___x_3725_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3726_ = lean_string_dec_eq(v_str_3721_, v___x_3725_);
lean_dec_ref(v_str_3721_);
if (v___x_3726_ == 0)
{
lean_dec_ref(v_str_3720_);
lean_dec(v_a_3709_);
lean_dec(v_catName_3681_);
v___y_3695_ = v_a_3714_;
v___y_3696_ = v___y_3711_;
v___y_3697_ = v___y_3712_;
goto v___jp_3694_;
}
else
{
lean_object* v___x_3727_; uint8_t v___x_3728_; 
v___x_3727_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_3728_ = lean_string_dec_eq(v_str_3720_, v___x_3727_);
if (v___x_3728_ == 0)
{
uint8_t v___x_3729_; 
v___x_3729_ = lean_string_dec_eq(v_str_3720_, v___x_3725_);
lean_dec_ref(v_str_3720_);
if (v___x_3729_ == 0)
{
lean_dec(v_a_3709_);
lean_dec(v_catName_3681_);
v___y_3695_ = v_a_3714_;
v___y_3696_ = v___y_3711_;
v___y_3697_ = v___y_3712_;
goto v___jp_3694_;
}
else
{
lean_object* v___x_3730_; 
lean_dec(v_a_3714_);
lean_inc(v_declName_3682_);
lean_inc(v_catName_3681_);
v___x_3730_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3681_, v_declName_3682_, v_a_3709_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_dec_ref_known(v___x_3730_, 1);
v___y_3689_ = v___y_3711_;
v___y_3690_ = v___y_3712_;
goto v___jp_3688_;
}
else
{
lean_dec(v_declName_3682_);
lean_dec(v_catName_3681_);
return v___x_3730_;
}
}
}
else
{
lean_object* v___x_3731_; 
lean_dec_ref(v_str_3720_);
lean_dec(v_a_3714_);
lean_inc(v_declName_3682_);
lean_inc(v_catName_3681_);
v___x_3731_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3681_, v_declName_3682_, v_a_3709_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_dec_ref_known(v___x_3731_, 1);
v___y_3689_ = v___y_3711_;
v___y_3690_ = v___y_3712_;
goto v___jp_3688_;
}
else
{
lean_dec(v_declName_3682_);
lean_dec(v_catName_3681_);
return v___x_3731_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3718_, 2);
lean_dec_ref_known(v_pre_3717_, 2);
lean_dec_ref_known(v_declName_3716_, 2);
lean_dec(v_a_3709_);
lean_dec(v_catName_3681_);
v___y_3695_ = v_a_3714_;
v___y_3696_ = v___y_3711_;
v___y_3697_ = v___y_3712_;
goto v___jp_3694_;
}
}
else
{
lean_dec(v_pre_3718_);
lean_dec_ref_known(v_pre_3717_, 2);
lean_dec_ref_known(v_declName_3716_, 2);
lean_dec(v_a_3709_);
lean_dec(v_catName_3681_);
v___y_3695_ = v_a_3714_;
v___y_3696_ = v___y_3711_;
v___y_3697_ = v___y_3712_;
goto v___jp_3694_;
}
}
else
{
lean_dec_ref_known(v_declName_3716_, 2);
lean_dec(v_pre_3717_);
lean_dec(v_a_3709_);
lean_dec(v_catName_3681_);
v___y_3695_ = v_a_3714_;
v___y_3696_ = v___y_3711_;
v___y_3697_ = v___y_3712_;
goto v___jp_3694_;
}
}
else
{
lean_dec(v_declName_3716_);
lean_dec(v_a_3709_);
lean_dec(v_catName_3681_);
v___y_3695_ = v_a_3714_;
v___y_3696_ = v___y_3711_;
v___y_3697_ = v___y_3712_;
goto v___jp_3694_;
}
}
else
{
lean_dec_ref(v___x_3715_);
lean_dec(v_a_3709_);
lean_dec(v_catName_3681_);
v___y_3695_ = v_a_3714_;
v___y_3696_ = v___y_3711_;
v___y_3697_ = v___y_3712_;
goto v___jp_3694_;
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec(v_a_3709_);
lean_dec(v_declName_3682_);
lean_dec(v_catName_3681_);
v_a_3732_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3713_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3713_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec(v_declName_3682_);
lean_dec(v_catName_3681_);
lean_dec(v_attrName_3680_);
v_a_3743_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3708_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3708_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
v___jp_3688_:
{
lean_object* v___x_3691_; 
lean_inc(v_declName_3682_);
v___x_3691_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_3682_, v___y_3689_, v___y_3690_);
if (lean_obj_tag(v___x_3691_) == 0)
{
uint8_t v___x_3692_; lean_object* v___x_3693_; 
lean_dec_ref_known(v___x_3691_, 1);
v___x_3692_ = 1;
v___x_3693_ = l_Lean_Parser_runParserAttributeHooks(v_catName_3681_, v_declName_3682_, v___x_3692_, v___y_3689_, v___y_3690_);
return v___x_3693_;
}
else
{
lean_dec(v_declName_3682_);
lean_dec(v_catName_3681_);
return v___x_3691_;
}
}
v___jp_3694_:
{
lean_object* v___x_3698_; uint8_t v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3698_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
v___x_3699_ = 0;
v___x_3700_ = l_Lean_MessageData_ofConstName(v_declName_3682_, v___x_3699_);
v___x_3701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3698_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
v___x_3703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3701_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = l_Lean_ConstantInfo_type(v___y_3695_);
lean_dec_ref(v___y_3695_);
v___x_3705_ = l_Lean_indentExpr(v___x_3704_);
v___x_3706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3703_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3706_, v___y_3696_, v___y_3697_);
return v___x_3707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* v_attrName_3751_, lean_object* v_catName_3752_, lean_object* v_declName_3753_, lean_object* v_stx_3754_, lean_object* v_kind_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_){
_start:
{
uint8_t v_kind_boxed_3759_; lean_object* v_res_3760_; 
v_kind_boxed_3759_ = lean_unbox(v_kind_3755_);
v_res_3760_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3751_, v_catName_3752_, v_declName_3753_, v_stx_3754_, v_kind_boxed_3759_, v_a_3756_, v_a_3757_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object* v_00_u03b1_3761_, lean_object* v_name_3762_, uint8_t v_kind_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3762_, v_kind_3763_, v___y_3764_, v___y_3765_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b1_3768_, lean_object* v_name_3769_, lean_object* v_kind_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
uint8_t v_kind_boxed_3774_; lean_object* v_res_3775_; 
v_kind_boxed_3774_ = lean_unbox(v_kind_3770_);
v_res_3775_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(v_00_u03b1_3768_, v_name_3769_, v_kind_boxed_3774_, v___y_3771_, v___y_3772_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object* v_00_u03b1_3776_, lean_object* v_constName_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3777_, v___y_3778_, v___y_3779_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3782_, lean_object* v_constName_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(v_00_u03b1_3782_, v_constName_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3788_, lean_object* v_ref_3789_, lean_object* v_constName_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3789_, v_constName_3790_, v___y_3791_, v___y_3792_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3795_, lean_object* v_ref_3796_, lean_object* v_constName_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(v_00_u03b1_3795_, v_ref_3796_, v_constName_3797_, v___y_3798_, v___y_3799_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v_ref_3796_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3802_, lean_object* v_ref_3803_, lean_object* v_msg_3804_, lean_object* v_declHint_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3803_, v_msg_3804_, v_declHint_3805_, v___y_3806_, v___y_3807_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3810_, lean_object* v_ref_3811_, lean_object* v_msg_3812_, lean_object* v_declHint_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3810_, v_ref_3811_, v_msg_3812_, v_declHint_3813_, v___y_3814_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v_ref_3811_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_3818_, lean_object* v_declHint_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3818_, v_declHint_3819_, v___y_3821_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_3824_, lean_object* v_declHint_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_3824_, v_declHint_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3830_, lean_object* v_ref_3831_, lean_object* v_msg_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v___x_3836_; 
v___x_3836_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3831_, v_msg_3832_, v___y_3833_, v___y_3834_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3837_, lean_object* v_ref_3838_, lean_object* v_msg_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3837_, v_ref_3838_, v_msg_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v_ref_3838_);
return v_res_3843_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2(void){
_start:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3850_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0));
v___x_3851_ = l_Lean_mkAtom(v___x_3850_);
return v___x_3851_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3852_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2);
v___x_3853_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3854_ = lean_array_push(v___x_3853_, v___x_3852_);
return v___x_3854_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7));
v___x_3864_ = l_Lean_mkAtom(v___x_3863_);
return v___x_3864_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3865_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8);
v___x_3866_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3867_ = lean_array_push(v___x_3866_, v___x_3865_);
return v___x_3867_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3868_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9);
v___x_3869_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6));
v___x_3870_ = lean_box(2);
v___x_3871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
lean_ctor_set(v___x_3871_, 1, v___x_3869_);
lean_ctor_set(v___x_3871_, 2, v___x_3868_);
return v___x_3871_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3872_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10);
v___x_3873_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3);
v___x_3874_ = lean_array_push(v___x_3873_, v___x_3872_);
return v___x_3874_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3875_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11);
v___x_3876_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1));
v___x_3877_ = lean_box(2);
v___x_3878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3877_);
lean_ctor_set(v___x_3878_, 1, v___x_3876_);
lean_ctor_set(v___x_3878_, 2, v___x_3875_);
return v___x_3878_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3879_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12);
v___x_3880_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3881_ = lean_array_push(v___x_3880_, v___x_3879_);
return v___x_3881_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14(void){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3882_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13);
v___x_3883_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3884_ = lean_box(2);
v___x_3885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3884_);
lean_ctor_set(v___x_3885_, 1, v___x_3883_);
lean_ctor_set(v___x_3885_, 2, v___x_3882_);
return v___x_3885_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3886_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14);
v___x_3887_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3888_ = lean_array_push(v___x_3887_, v___x_3886_);
return v___x_3888_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3889_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15);
v___x_3890_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3891_ = lean_box(2);
v___x_3892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
lean_ctor_set(v___x_3892_, 1, v___x_3890_);
lean_ctor_set(v___x_3892_, 2, v___x_3889_);
return v___x_3892_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3893_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16);
v___x_3894_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3895_ = lean_array_push(v___x_3894_, v___x_3893_);
return v___x_3895_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3896_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17);
v___x_3897_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3898_ = lean_box(2);
v___x_3899_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
lean_ctor_set(v___x_3899_, 1, v___x_3897_);
lean_ctor_set(v___x_3899_, 2, v___x_3896_);
return v___x_3899_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object* v_attrName_3901_, lean_object* v_decl_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3906_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3907_ = l_Lean_MessageData_ofName(v_attrName_3901_);
v___x_3908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3906_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
v___x_3909_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3908_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
v___x_3911_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3910_, v___y_3903_, v___y_3904_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object* v_attrName_3912_, lean_object* v_decl_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_3912_, v_decl_3913_, v___y_3914_, v___y_3915_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec(v_decl_3913_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object* v_attrName_3918_, lean_object* v_catName_3919_, lean_object* v_declName_3920_, lean_object* v_stx_3921_, uint8_t v_kind_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3918_, v_catName_3919_, v_declName_3920_, v_stx_3921_, v_kind_3922_, v___y_3923_, v___y_3924_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object* v_attrName_3927_, lean_object* v_catName_3928_, lean_object* v_declName_3929_, lean_object* v_stx_3930_, lean_object* v_kind_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
uint8_t v_kind_boxed_3935_; lean_object* v_res_3936_; 
v_kind_boxed_3935_ = lean_unbox(v_kind_3931_);
v_res_3936_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_3927_, v_catName_3928_, v_declName_3929_, v_stx_3930_, v_kind_boxed_3935_, v___y_3932_, v___y_3933_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
return v_res_3936_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1(void){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__0));
v___x_3939_ = lean_mk_io_user_error(v___x_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* v_attrName_3942_, lean_object* v_declName_3943_, uint8_t v_behavior_3944_, lean_object* v_ref_3945_){
_start:
{
if (lean_obj_tag(v_declName_3943_) == 1)
{
lean_object* v_pre_3950_; 
v_pre_3950_ = lean_ctor_get(v_declName_3943_, 0);
if (lean_obj_tag(v_pre_3950_) == 1)
{
lean_object* v_pre_3951_; 
v_pre_3951_ = lean_ctor_get(v_pre_3950_, 0);
if (lean_obj_tag(v_pre_3951_) == 1)
{
lean_object* v_pre_3952_; 
v_pre_3952_ = lean_ctor_get(v_pre_3951_, 0);
if (lean_obj_tag(v_pre_3952_) == 1)
{
lean_object* v_pre_3953_; 
v_pre_3953_ = lean_ctor_get(v_pre_3952_, 0);
if (lean_obj_tag(v_pre_3953_) == 0)
{
lean_object* v_str_3954_; lean_object* v_str_3955_; lean_object* v_str_3956_; lean_object* v_str_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; 
v_str_3954_ = lean_ctor_get(v_declName_3943_, 1);
v_str_3955_ = lean_ctor_get(v_pre_3950_, 1);
v_str_3956_ = lean_ctor_get(v_pre_3951_, 1);
v_str_3957_ = lean_ctor_get(v_pre_3952_, 1);
v___x_3958_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3959_ = lean_string_dec_eq(v_str_3957_, v___x_3958_);
if (v___x_3959_ == 0)
{
lean_dec_ref_known(v_declName_3943_, 2);
lean_dec(v_ref_3945_);
lean_dec(v_attrName_3942_);
goto v___jp_3947_;
}
else
{
lean_object* v___x_3960_; uint8_t v___x_3961_; 
v___x_3960_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3961_ = lean_string_dec_eq(v_str_3956_, v___x_3960_);
if (v___x_3961_ == 0)
{
lean_dec_ref_known(v_declName_3943_, 2);
lean_dec(v_ref_3945_);
lean_dec(v_attrName_3942_);
goto v___jp_3947_;
}
else
{
lean_object* v___x_3962_; uint8_t v___x_3963_; 
v___x_3962_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__2));
v___x_3963_ = lean_string_dec_eq(v_str_3955_, v___x_3962_);
if (v___x_3963_ == 0)
{
lean_dec_ref_known(v_declName_3943_, 2);
lean_dec(v_ref_3945_);
lean_dec(v_attrName_3942_);
goto v___jp_3947_;
}
else
{
lean_object* v___x_3964_; lean_object* v_catName_3965_; lean_object* v___x_3966_; 
v___x_3964_ = lean_box(0);
lean_inc_ref(v_str_3954_);
v_catName_3965_ = l_Lean_Name_str___override(v___x_3964_, v_str_3954_);
lean_inc(v_catName_3965_);
v___x_3966_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_3965_, v_declName_3943_, v_behavior_3944_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v___f_3967_; lean_object* v___f_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
lean_dec_ref_known(v___x_3966_, 1);
lean_inc_n(v_attrName_3942_, 2);
v___f_3967_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3967_, 0, v_attrName_3942_);
v___f_3968_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3968_, 0, v_attrName_3942_);
lean_closure_set(v___f_3968_, 1, v_catName_3965_);
v___x_3969_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__3));
v___x_3970_ = 1;
v___x_3971_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3971_, 0, v_ref_3945_);
lean_ctor_set(v___x_3971_, 1, v_attrName_3942_);
lean_ctor_set(v___x_3971_, 2, v___x_3969_);
lean_ctor_set_uint8(v___x_3971_, sizeof(void*)*3, v___x_3970_);
v___x_3972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
lean_ctor_set(v___x_3972_, 1, v___f_3968_);
lean_ctor_set(v___x_3972_, 2, v___f_3967_);
v___x_3973_ = l_Lean_registerBuiltinAttribute(v___x_3972_);
return v___x_3973_;
}
else
{
lean_dec(v_catName_3965_);
lean_dec(v_ref_3945_);
lean_dec(v_attrName_3942_);
return v___x_3966_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_declName_3943_, 2);
lean_dec(v_ref_3945_);
lean_dec(v_attrName_3942_);
goto v___jp_3947_;
}
}
else
{
lean_dec_ref_known(v_declName_3943_, 2);
lean_dec(v_ref_3945_);
lean_dec(v_attrName_3942_);
goto v___jp_3947_;
}
}
else
{
lean_dec_ref_known(v_declName_3943_, 2);
lean_dec(v_ref_3945_);
lean_dec(v_attrName_3942_);
goto v___jp_3947_;
}
}
else
{
lean_dec_ref_known(v_declName_3943_, 2);
lean_dec(v_ref_3945_);
lean_dec(v_attrName_3942_);
goto v___jp_3947_;
}
}
else
{
lean_dec(v_ref_3945_);
lean_dec(v_declName_3943_);
lean_dec(v_attrName_3942_);
goto v___jp_3947_;
}
v___jp_3947_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3948_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___closed__1, &l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
v___x_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
return v___x_3949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* v_attrName_3974_, lean_object* v_declName_3975_, lean_object* v_behavior_3976_, lean_object* v_ref_3977_, lean_object* v_a_3978_){
_start:
{
uint8_t v_behavior_boxed_3979_; lean_object* v_res_3980_; 
v_behavior_boxed_3979_ = lean_unbox(v_behavior_3976_);
v_res_3980_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_3974_, v_declName_3975_, v_behavior_boxed_3979_, v_ref_3977_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object* v_kind_3981_, lean_object* v_x_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v___x_3986_; lean_object* v_env_3987_; lean_object* v_nextMacroScope_3988_; lean_object* v_ngen_3989_; lean_object* v_auxDeclNGen_3990_; lean_object* v_traceState_3991_; lean_object* v_messages_3992_; lean_object* v_infoState_3993_; lean_object* v_snapshotTasks_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4006_; 
v___x_3986_ = lean_st_ref_take(v___y_3984_);
v_env_3987_ = lean_ctor_get(v___x_3986_, 0);
v_nextMacroScope_3988_ = lean_ctor_get(v___x_3986_, 1);
v_ngen_3989_ = lean_ctor_get(v___x_3986_, 2);
v_auxDeclNGen_3990_ = lean_ctor_get(v___x_3986_, 3);
v_traceState_3991_ = lean_ctor_get(v___x_3986_, 4);
v_messages_3992_ = lean_ctor_get(v___x_3986_, 6);
v_infoState_3993_ = lean_ctor_get(v___x_3986_, 7);
v_snapshotTasks_3994_ = lean_ctor_get(v___x_3986_, 8);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4006_ == 0)
{
lean_object* v_unused_4007_; 
v_unused_4007_ = lean_ctor_get(v___x_3986_, 5);
lean_dec(v_unused_4007_);
v___x_3996_ = v___x_3986_;
v_isShared_3997_ = v_isSharedCheck_4006_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_snapshotTasks_3994_);
lean_inc(v_infoState_3993_);
lean_inc(v_messages_3992_);
lean_inc(v_traceState_3991_);
lean_inc(v_auxDeclNGen_3990_);
lean_inc(v_ngen_3989_);
lean_inc(v_nextMacroScope_3988_);
lean_inc(v_env_3987_);
lean_dec(v___x_3986_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4006_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4001_; 
v___x_3998_ = l_Lean_Parser_addSyntaxNodeKind(v_env_3987_, v_kind_3981_);
v___x_3999_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 5, v___x_3999_);
lean_ctor_set(v___x_3996_, 0, v___x_3998_);
v___x_4001_ = v___x_3996_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_3998_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_nextMacroScope_3988_);
lean_ctor_set(v_reuseFailAlloc_4005_, 2, v_ngen_3989_);
lean_ctor_set(v_reuseFailAlloc_4005_, 3, v_auxDeclNGen_3990_);
lean_ctor_set(v_reuseFailAlloc_4005_, 4, v_traceState_3991_);
lean_ctor_set(v_reuseFailAlloc_4005_, 5, v___x_3999_);
lean_ctor_set(v_reuseFailAlloc_4005_, 6, v_messages_3992_);
lean_ctor_set(v_reuseFailAlloc_4005_, 7, v_infoState_3993_);
lean_ctor_set(v_reuseFailAlloc_4005_, 8, v_snapshotTasks_3994_);
v___x_4001_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4002_ = lean_st_ref_put(v___y_3984_, v___x_4001_);
v___x_4003_ = lean_box(0);
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
return v___x_4004_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object* v_kind_4008_, lean_object* v_x_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_4008_, v_x_4009_, v___y_4010_, v___y_4011_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_4014_, lean_object* v_keys_4015_, lean_object* v_vals_4016_, lean_object* v_i_4017_, lean_object* v_acc_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v___x_4022_; uint8_t v___x_4023_; 
v___x_4022_ = lean_array_get_size(v_keys_4015_);
v___x_4023_ = lean_nat_dec_lt(v_i_4017_, v___x_4022_);
if (v___x_4023_ == 0)
{
lean_object* v___x_4024_; 
lean_dec(v_i_4017_);
lean_dec_ref(v_f_4014_);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v_acc_4018_);
return v___x_4024_;
}
else
{
lean_object* v_k_4025_; lean_object* v_v_4026_; lean_object* v___x_4027_; 
v_k_4025_ = lean_array_fget_borrowed(v_keys_4015_, v_i_4017_);
v_v_4026_ = lean_array_fget_borrowed(v_vals_4016_, v_i_4017_);
lean_inc_ref(v_f_4014_);
lean_inc(v___y_4020_);
lean_inc_ref(v___y_4019_);
lean_inc(v_v_4026_);
lean_inc(v_k_4025_);
v___x_4027_ = lean_apply_6(v_f_4014_, v_acc_4018_, v_k_4025_, v_v_4026_, v___y_4019_, v___y_4020_, lean_box(0));
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref_known(v___x_4027_, 1);
v___x_4029_ = lean_unsigned_to_nat(1u);
v___x_4030_ = lean_nat_add(v_i_4017_, v___x_4029_);
lean_dec(v_i_4017_);
v_i_4017_ = v___x_4030_;
v_acc_4018_ = v_a_4028_;
goto _start;
}
else
{
lean_dec(v_i_4017_);
lean_dec_ref(v_f_4014_);
return v___x_4027_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_4032_, lean_object* v_keys_4033_, lean_object* v_vals_4034_, lean_object* v_i_4035_, lean_object* v_acc_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4032_, v_keys_4033_, v_vals_4034_, v_i_4035_, v_acc_4036_, v___y_4037_, v___y_4038_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec_ref(v_vals_4034_);
lean_dec_ref(v_keys_4033_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_4041_, lean_object* v_as_4042_, size_t v_i_4043_, size_t v_stop_4044_, lean_object* v_b_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v_a_4050_; lean_object* v___y_4055_; uint8_t v___x_4057_; 
v___x_4057_ = lean_usize_dec_eq(v_i_4043_, v_stop_4044_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; 
v___x_4058_ = lean_array_uget_borrowed(v_as_4042_, v_i_4043_);
switch(lean_obj_tag(v___x_4058_))
{
case 0:
{
lean_object* v_key_4059_; lean_object* v_val_4060_; lean_object* v___x_4061_; 
v_key_4059_ = lean_ctor_get(v___x_4058_, 0);
v_val_4060_ = lean_ctor_get(v___x_4058_, 1);
lean_inc_ref(v_f_4041_);
lean_inc(v___y_4047_);
lean_inc_ref(v___y_4046_);
lean_inc(v_val_4060_);
lean_inc(v_key_4059_);
v___x_4061_ = lean_apply_6(v_f_4041_, v_b_4045_, v_key_4059_, v_val_4060_, v___y_4046_, v___y_4047_, lean_box(0));
v___y_4055_ = v___x_4061_;
goto v___jp_4054_;
}
case 1:
{
lean_object* v_node_4062_; lean_object* v___x_4063_; 
v_node_4062_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_node_4062_);
lean_inc_ref(v_f_4041_);
v___x_4063_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4041_, v_node_4062_, v_b_4045_, v___y_4046_, v___y_4047_);
v___y_4055_ = v___x_4063_;
goto v___jp_4054_;
}
default: 
{
v_a_4050_ = v_b_4045_;
goto v___jp_4049_;
}
}
}
else
{
lean_object* v___x_4064_; 
lean_dec_ref(v_f_4041_);
v___x_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4064_, 0, v_b_4045_);
return v___x_4064_;
}
v___jp_4049_:
{
size_t v___x_4051_; size_t v___x_4052_; 
v___x_4051_ = ((size_t)1ULL);
v___x_4052_ = lean_usize_add(v_i_4043_, v___x_4051_);
v_i_4043_ = v___x_4052_;
v_b_4045_ = v_a_4050_;
goto _start;
}
v___jp_4054_:
{
if (lean_obj_tag(v___y_4055_) == 0)
{
lean_object* v_a_4056_; 
v_a_4056_ = lean_ctor_get(v___y_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___y_4055_, 1);
v_a_4050_ = v_a_4056_;
goto v___jp_4049_;
}
else
{
lean_dec_ref(v_f_4041_);
return v___y_4055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object* v_f_4065_, lean_object* v_x_4066_, lean_object* v_x_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
if (lean_obj_tag(v_x_4066_) == 0)
{
lean_object* v_es_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4084_; 
v_es_4071_ = lean_ctor_get(v_x_4066_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v_x_4066_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4073_ = v_x_4066_;
v_isShared_4074_ = v_isSharedCheck_4084_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_es_4071_);
lean_dec(v_x_4066_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4084_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; 
v___x_4075_ = lean_unsigned_to_nat(0u);
v___x_4076_ = lean_array_get_size(v_es_4071_);
v___x_4077_ = lean_nat_dec_lt(v___x_4075_, v___x_4076_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4079_; 
lean_dec_ref(v_es_4071_);
lean_dec_ref(v_f_4065_);
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 0, v_x_4067_);
v___x_4079_ = v___x_4073_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_x_4067_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
else
{
size_t v___x_4081_; size_t v___x_4082_; lean_object* v___x_4083_; 
lean_del_object(v___x_4073_);
v___x_4081_ = ((size_t)0ULL);
v___x_4082_ = lean_usize_of_nat(v___x_4076_);
v___x_4083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4065_, v_es_4071_, v___x_4081_, v___x_4082_, v_x_4067_, v___y_4068_, v___y_4069_);
lean_dec_ref(v_es_4071_);
return v___x_4083_;
}
}
}
else
{
lean_object* v_ks_4085_; lean_object* v_vs_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v_ks_4085_ = lean_ctor_get(v_x_4066_, 0);
lean_inc_ref(v_ks_4085_);
v_vs_4086_ = lean_ctor_get(v_x_4066_, 1);
lean_inc_ref(v_vs_4086_);
lean_dec_ref_known(v_x_4066_, 2);
v___x_4087_ = lean_unsigned_to_nat(0u);
v___x_4088_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4065_, v_ks_4085_, v_vs_4086_, v___x_4087_, v_x_4067_, v___y_4068_, v___y_4069_);
lean_dec_ref(v_vs_4086_);
lean_dec_ref(v_ks_4085_);
return v___x_4088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_4089_, lean_object* v_x_4090_, lean_object* v_x_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4089_, v_x_4090_, v_x_4091_, v___y_4092_, v___y_4093_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_4096_, lean_object* v_as_4097_, lean_object* v_i_4098_, lean_object* v_stop_4099_, lean_object* v_b_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
size_t v_i_boxed_4104_; size_t v_stop_boxed_4105_; lean_object* v_res_4106_; 
v_i_boxed_4104_ = lean_unbox_usize(v_i_4098_);
lean_dec(v_i_4098_);
v_stop_boxed_4105_ = lean_unbox_usize(v_stop_4099_);
lean_dec(v_stop_4099_);
v_res_4106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4096_, v_as_4097_, v_i_boxed_4104_, v_stop_boxed_4105_, v_b_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec_ref(v_as_4097_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object* v_f_4107_, lean_object* v_x_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4114_; 
lean_inc(v___y_4112_);
lean_inc_ref(v___y_4111_);
v___x_4114_ = lean_apply_5(v_f_4107_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, lean_box(0));
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object* v_f_4115_, lean_object* v_x_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4115_, v_x_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object* v_map_4123_, lean_object* v_f_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v___f_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___f_4128_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4128_, 0, v_f_4124_);
v___x_4129_ = lean_box(0);
v___x_4130_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v___f_4128_, v_map_4123_, v___x_4129_, v___y_4125_, v___y_4126_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object* v_map_4131_, lean_object* v_f_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4131_, v_f_4132_, v___y_4133_, v___y_4134_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
return v_res_4136_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4138_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0));
v___x_4139_ = l_Lean_stringToMessageData(v___x_4138_);
return v___x_4139_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4140_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_4141_ = l_Lean_stringToMessageData(v___x_4140_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t v_attrKind_4142_, lean_object* v_declName_4143_, lean_object* v_as_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
if (lean_obj_tag(v_as_4144_) == 0)
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
lean_dec(v_declName_4143_);
v___x_4148_ = lean_box(0);
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
return v___x_4149_;
}
else
{
lean_object* v_head_4150_; lean_object* v_tail_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4181_; 
v_head_4150_ = lean_ctor_get(v_as_4144_, 0);
v_tail_4151_ = lean_ctor_get(v_as_4144_, 1);
v_isSharedCheck_4181_ = !lean_is_exclusive(v_as_4144_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4153_ = v_as_4144_;
v_isShared_4154_ = v_isSharedCheck_4181_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_tail_4151_);
lean_inc(v_head_4150_);
lean_dec(v_as_4144_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4181_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___y_4156_; lean_object* v___x_4158_; 
v___x_4158_ = l_Lean_Parser_addToken(v_head_4150_, v_attrKind_4142_, v___y_4145_, v___y_4146_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_del_object(v___x_4153_);
v___y_4156_ = v___x_4158_;
goto v___jp_4155_;
}
else
{
lean_object* v_a_4159_; uint8_t v___y_4161_; uint8_t v___x_4179_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
v___x_4179_ = l_Lean_Exception_isInterrupt(v_a_4159_);
if (v___x_4179_ == 0)
{
uint8_t v___x_4180_; 
lean_inc(v_a_4159_);
v___x_4180_ = l_Lean_Exception_isRuntime(v_a_4159_);
v___y_4161_ = v___x_4180_;
goto v___jp_4160_;
}
else
{
v___y_4161_ = v___x_4179_;
goto v___jp_4160_;
}
v___jp_4160_:
{
if (v___y_4161_ == 0)
{
if (lean_obj_tag(v_a_4159_) == 0)
{
lean_object* v_msg_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4177_; 
lean_dec_ref_known(v___x_4158_, 1);
v_msg_4162_ = lean_ctor_get(v_a_4159_, 1);
v_isSharedCheck_4177_ = !lean_is_exclusive(v_a_4159_);
if (v_isSharedCheck_4177_ == 0)
{
lean_object* v_unused_4178_; 
v_unused_4178_ = lean_ctor_get(v_a_4159_, 0);
lean_dec(v_unused_4178_);
v___x_4164_ = v_a_4159_;
v_isShared_4165_ = v_isSharedCheck_4177_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_msg_4162_);
lean_dec(v_a_4159_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4177_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4169_; 
v___x_4166_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1);
lean_inc(v_declName_4143_);
v___x_4167_ = l_Lean_MessageData_ofConstName(v_declName_4143_, v___y_4161_);
if (v_isShared_4165_ == 0)
{
lean_ctor_set_tag(v___x_4164_, 7);
lean_ctor_set(v___x_4164_, 1, v___x_4167_);
lean_ctor_set(v___x_4164_, 0, v___x_4166_);
v___x_4169_ = v___x_4164_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4166_);
lean_ctor_set(v_reuseFailAlloc_4176_, 1, v___x_4167_);
v___x_4169_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
lean_object* v___x_4170_; lean_object* v___x_4172_; 
v___x_4170_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2);
if (v_isShared_4154_ == 0)
{
lean_ctor_set_tag(v___x_4153_, 7);
lean_ctor_set(v___x_4153_, 1, v___x_4170_);
lean_ctor_set(v___x_4153_, 0, v___x_4169_);
v___x_4172_ = v___x_4153_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4169_);
lean_ctor_set(v_reuseFailAlloc_4175_, 1, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4172_);
lean_ctor_set(v___x_4173_, 1, v_msg_4162_);
v___x_4174_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4173_, v___y_4145_, v___y_4146_);
v___y_4156_ = v___x_4174_;
goto v___jp_4155_;
}
}
}
}
else
{
lean_dec(v_a_4159_);
lean_del_object(v___x_4153_);
v___y_4156_ = v___x_4158_;
goto v___jp_4155_;
}
}
else
{
lean_dec(v_a_4159_);
lean_del_object(v___x_4153_);
v___y_4156_ = v___x_4158_;
goto v___jp_4155_;
}
}
}
v___jp_4155_:
{
if (lean_obj_tag(v___y_4156_) == 0)
{
lean_dec_ref_known(v___y_4156_, 1);
v_as_4144_ = v_tail_4151_;
goto _start;
}
else
{
lean_dec(v_tail_4151_);
lean_dec(v_declName_4143_);
return v___y_4156_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object* v_attrKind_4182_, lean_object* v_declName_4183_, lean_object* v_as_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
uint8_t v_attrKind_boxed_4188_; lean_object* v_res_4189_; 
v_attrKind_boxed_4188_ = lean_unbox(v_attrKind_4182_);
v_res_4189_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_boxed_4188_, v_declName_4183_, v_as_4184_, v___y_4185_, v___y_4186_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object* v_catName_4191_, lean_object* v_declName_4192_, lean_object* v_stx_4193_, uint8_t v_attrKind_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_){
_start:
{
lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___x_4203_; 
v___x_4203_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4193_, v_a_4195_, v_a_4196_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v_env_4207_; lean_object* v___x_4208_; lean_object* v_ext_4209_; lean_object* v_toEnvExtension_4210_; lean_object* v_asyncMode_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v_toCold_4214_; lean_object* v_categories_4215_; lean_object* v_env_4216_; lean_object* v_ref_4217_; lean_object* v_options_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4203_, 1);
v___x_4205_ = lean_st_ref_get(v_a_4196_);
v___x_4206_ = lean_st_ref_get(v_a_4196_);
v_env_4207_ = lean_ctor_get(v___x_4205_, 0);
lean_inc_ref(v_env_4207_);
lean_dec(v___x_4205_);
v___x_4208_ = l_Lean_Parser_parserExtension;
v_ext_4209_ = lean_ctor_get(v___x_4208_, 1);
v_toEnvExtension_4210_ = lean_ctor_get(v_ext_4209_, 0);
v_asyncMode_4211_ = lean_ctor_get(v_toEnvExtension_4210_, 2);
v___x_4212_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4213_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4212_, v___x_4208_, v_env_4207_, v_asyncMode_4211_);
v_toCold_4214_ = lean_ctor_get(v_a_4195_, 0);
v_categories_4215_ = lean_ctor_get(v___x_4213_, 2);
lean_inc_ref_n(v_categories_4215_, 2);
lean_dec(v___x_4213_);
v_env_4216_ = lean_ctor_get(v___x_4206_, 0);
lean_inc_ref(v_env_4216_);
lean_dec(v___x_4206_);
v_ref_4217_ = lean_ctor_get(v_a_4195_, 2);
v_options_4218_ = lean_ctor_get(v_toCold_4214_, 2);
lean_inc_ref(v_options_4218_);
v___x_4219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4219_, 0, v_env_4216_);
lean_ctor_set(v___x_4219_, 1, v_options_4218_);
lean_inc(v_declName_4192_);
v___x_4220_ = l_Lean_Parser_mkParserOfConstant(v_categories_4215_, v_declName_4192_, v___x_4219_);
lean_dec_ref_known(v___x_4219_, 2);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v_snd_4222_; lean_object* v_info_4223_; lean_object* v_fst_4224_; lean_object* v_collectTokens_4225_; lean_object* v_collectKinds_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v___x_4220_, 1);
v_snd_4222_ = lean_ctor_get(v_a_4221_, 1);
lean_inc(v_snd_4222_);
v_info_4223_ = lean_ctor_get(v_snd_4222_, 0);
v_fst_4224_ = lean_ctor_get(v_a_4221_, 0);
lean_inc(v_fst_4224_);
lean_dec(v_a_4221_);
v_collectTokens_4225_ = lean_ctor_get(v_info_4223_, 0);
v_collectKinds_4226_ = lean_ctor_get(v_info_4223_, 1);
v___x_4227_ = lean_box(0);
lean_inc_ref(v_collectTokens_4225_);
v___x_4228_ = lean_apply_1(v_collectTokens_4225_, v___x_4227_);
lean_inc(v_declName_4192_);
v___x_4229_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4194_, v_declName_4192_, v___x_4228_, v_a_4195_, v_a_4196_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v___f_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_dec_ref_known(v___x_4229_, 1);
v___f_4230_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0));
v___x_4231_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
lean_inc_ref(v_collectKinds_4226_);
v___x_4232_ = lean_apply_1(v_collectKinds_4226_, v___x_4231_);
v___x_4233_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v___x_4232_, v___f_4230_, v_a_4195_, v_a_4196_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v___x_4234_; uint8_t v___x_4235_; uint8_t v___x_4236_; lean_object* v___x_4237_; 
lean_dec_ref_known(v___x_4233_, 1);
lean_inc(v_a_4204_);
lean_inc(v_snd_4222_);
lean_inc_n(v_declName_4192_, 2);
lean_inc_n(v_catName_4191_, 2);
v___x_4234_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_4234_, 0, v_catName_4191_);
lean_ctor_set(v___x_4234_, 1, v_declName_4192_);
lean_ctor_set(v___x_4234_, 2, v_snd_4222_);
lean_ctor_set(v___x_4234_, 3, v_a_4204_);
v___x_4235_ = lean_unbox(v_fst_4224_);
lean_ctor_set_uint8(v___x_4234_, sizeof(void*)*4, v___x_4235_);
v___x_4236_ = lean_unbox(v_fst_4224_);
lean_dec(v_fst_4224_);
v___x_4237_ = l_Lean_Parser_addParser(v_categories_4215_, v_catName_4191_, v_declName_4192_, v___x_4236_, v_snd_4222_, v_a_4204_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4247_; 
lean_dec_ref_known(v___x_4234_, 4);
lean_dec(v_declName_4192_);
lean_dec(v_catName_4191_);
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4240_ = v___x_4237_;
v_isShared_4241_ = v_isSharedCheck_4247_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4247_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
lean_ctor_set_tag(v___x_4240_, 3);
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4244_ = l_Lean_MessageData_ofFormat(v___x_4243_);
v___x_4245_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4244_, v_a_4195_, v_a_4196_);
return v___x_4245_;
}
}
}
else
{
lean_object* v___x_4248_; 
lean_dec_ref_known(v___x_4237_, 1);
v___x_4248_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_4208_, v___x_4234_, v_attrKind_4194_, v_a_4195_, v_a_4196_);
lean_dec_ref(v___x_4248_);
v___y_4199_ = v_a_4195_;
v___y_4200_ = v_a_4196_;
goto v___jp_4198_;
}
}
else
{
lean_dec(v_fst_4224_);
lean_dec(v_snd_4222_);
lean_dec_ref(v_categories_4215_);
lean_dec(v_a_4204_);
lean_dec(v_declName_4192_);
lean_dec(v_catName_4191_);
return v___x_4233_;
}
}
else
{
lean_dec(v_fst_4224_);
lean_dec(v_snd_4222_);
lean_dec_ref(v_categories_4215_);
lean_dec(v_a_4204_);
lean_dec(v_declName_4192_);
lean_dec(v_catName_4191_);
return v___x_4229_;
}
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4260_; 
lean_dec_ref(v_categories_4215_);
lean_dec(v_a_4204_);
lean_dec(v_declName_4192_);
lean_dec(v_catName_4191_);
v_a_4249_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4251_ = v___x_4220_;
v_isShared_4252_ = v_isSharedCheck_4260_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4220_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4260_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4258_; 
v___x_4253_ = lean_io_error_to_string(v_a_4249_);
v___x_4254_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4253_);
v___x_4255_ = l_Lean_MessageData_ofFormat(v___x_4254_);
lean_inc(v_ref_4217_);
v___x_4256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4256_, 0, v_ref_4217_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 0, v___x_4256_);
v___x_4258_ = v___x_4251_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4256_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_dec(v_declName_4192_);
lean_dec(v_catName_4191_);
v_a_4261_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4203_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4203_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
v___jp_4198_:
{
uint8_t v___x_4201_; lean_object* v___x_4202_; 
v___x_4201_ = 0;
v___x_4202_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4191_, v_declName_4192_, v___x_4201_, v___y_4199_, v___y_4200_);
return v___x_4202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object* v_catName_4269_, lean_object* v_declName_4270_, lean_object* v_stx_4271_, lean_object* v_attrKind_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_){
_start:
{
uint8_t v_attrKind_boxed_4276_; lean_object* v_res_4277_; 
v_attrKind_boxed_4276_ = lean_unbox(v_attrKind_4272_);
v_res_4277_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4269_, v_declName_4270_, v_stx_4271_, v_attrKind_boxed_4276_, v_a_4273_, v_a_4274_);
lean_dec(v_a_4274_);
lean_dec_ref(v_a_4273_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* v___attrName_4278_, lean_object* v_catName_4279_, lean_object* v_declName_4280_, lean_object* v_stx_4281_, uint8_t v_attrKind_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_){
_start:
{
lean_object* v___x_4286_; 
v___x_4286_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4279_, v_declName_4280_, v_stx_4281_, v_attrKind_4282_, v_a_4283_, v_a_4284_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* v___attrName_4287_, lean_object* v_catName_4288_, lean_object* v_declName_4289_, lean_object* v_stx_4290_, lean_object* v_attrKind_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_){
_start:
{
uint8_t v_attrKind_boxed_4295_; lean_object* v_res_4296_; 
v_attrKind_boxed_4295_ = lean_unbox(v_attrKind_4291_);
v_res_4296_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4287_, v_catName_4288_, v_declName_4289_, v_stx_4290_, v_attrKind_boxed_4295_, v_a_4292_, v_a_4293_);
lean_dec(v_a_4293_);
lean_dec_ref(v_a_4292_);
lean_dec(v___attrName_4287_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object* v_00_u03b2_4297_, lean_object* v_map_4298_, lean_object* v_f_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v___x_4303_; 
v___x_4303_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4298_, v_f_4299_, v___y_4300_, v___y_4301_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b2_4304_, lean_object* v_map_4305_, lean_object* v_f_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(v_00_u03b2_4304_, v_map_4305_, v_f_4306_, v___y_4307_, v___y_4308_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object* v_map_4311_, lean_object* v_f_4312_, lean_object* v_init_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4312_, v_map_4311_, v_init_4313_, v___y_4314_, v___y_4315_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object* v_map_4318_, lean_object* v_f_4319_, lean_object* v_init_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4318_, v_f_4319_, v_init_4320_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object* v_00_u03c3_4325_, lean_object* v_00_u03b2_4326_, lean_object* v_map_4327_, lean_object* v_f_4328_, lean_object* v_init_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4328_, v_map_4327_, v_init_4329_, v___y_4330_, v___y_4331_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object* v_00_u03c3_4334_, lean_object* v_00_u03b2_4335_, lean_object* v_map_4336_, lean_object* v_f_4337_, lean_object* v_init_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(v_00_u03c3_4334_, v_00_u03b2_4335_, v_map_4336_, v_f_4337_, v_init_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_4343_, lean_object* v_00_u03b1_4344_, lean_object* v_00_u03b2_4345_, lean_object* v_f_4346_, lean_object* v_x_4347_, lean_object* v_x_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
lean_object* v___x_4352_; 
v___x_4352_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4346_, v_x_4347_, v_x_4348_, v___y_4349_, v___y_4350_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03c3_4353_, lean_object* v_00_u03b1_4354_, lean_object* v_00_u03b2_4355_, lean_object* v_f_4356_, lean_object* v_x_4357_, lean_object* v_x_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(v_00_u03c3_4353_, v_00_u03b1_4354_, v_00_u03b2_4355_, v_f_4356_, v_x_4357_, v_x_4358_, v___y_4359_, v___y_4360_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4363_, lean_object* v_00_u03b2_4364_, lean_object* v_00_u03c3_4365_, lean_object* v_f_4366_, lean_object* v_as_4367_, size_t v_i_4368_, size_t v_stop_4369_, lean_object* v_b_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4366_, v_as_4367_, v_i_4368_, v_stop_4369_, v_b_4370_, v___y_4371_, v___y_4372_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4375_, lean_object* v_00_u03b2_4376_, lean_object* v_00_u03c3_4377_, lean_object* v_f_4378_, lean_object* v_as_4379_, lean_object* v_i_4380_, lean_object* v_stop_4381_, lean_object* v_b_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
size_t v_i_boxed_4386_; size_t v_stop_boxed_4387_; lean_object* v_res_4388_; 
v_i_boxed_4386_ = lean_unbox_usize(v_i_4380_);
lean_dec(v_i_4380_);
v_stop_boxed_4387_ = lean_unbox_usize(v_stop_4381_);
lean_dec(v_stop_4381_);
v_res_4388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4375_, v_00_u03b2_4376_, v_00_u03c3_4377_, v_f_4378_, v_as_4379_, v_i_boxed_4386_, v_stop_boxed_4387_, v_b_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec_ref(v_as_4379_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_4389_, lean_object* v_00_u03b1_4390_, lean_object* v_00_u03b2_4391_, lean_object* v_f_4392_, lean_object* v_keys_4393_, lean_object* v_vals_4394_, lean_object* v_heq_4395_, lean_object* v_i_4396_, lean_object* v_acc_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v___x_4401_; 
v___x_4401_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4392_, v_keys_4393_, v_vals_4394_, v_i_4396_, v_acc_4397_, v___y_4398_, v___y_4399_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_4402_, lean_object* v_00_u03b1_4403_, lean_object* v_00_u03b2_4404_, lean_object* v_f_4405_, lean_object* v_keys_4406_, lean_object* v_vals_4407_, lean_object* v_heq_4408_, lean_object* v_i_4409_, lean_object* v_acc_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4402_, v_00_u03b1_4403_, v_00_u03b2_4404_, v_f_4405_, v_keys_4406_, v_vals_4407_, v_heq_4408_, v_i_4409_, v_acc_4410_, v___y_4411_, v___y_4412_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec_ref(v_vals_4407_);
lean_dec_ref(v_keys_4406_);
return v_res_4414_;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___auto__1(void){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object* v_catName_4416_, lean_object* v_declName_4417_, lean_object* v_stx_4418_, uint8_t v_attrKind_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v___x_4423_; 
v___x_4423_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4416_, v_declName_4417_, v_stx_4418_, v_attrKind_4419_, v___y_4420_, v___y_4421_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object* v_catName_4424_, lean_object* v_declName_4425_, lean_object* v_stx_4426_, lean_object* v_attrKind_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
uint8_t v_attrKind_boxed_4431_; lean_object* v_res_4432_; 
v_attrKind_boxed_4431_ = lean_unbox(v_attrKind_4427_);
v_res_4432_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4424_, v_declName_4425_, v_stx_4426_, v_attrKind_boxed_4431_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* v_attrName_4434_, lean_object* v_catName_4435_, lean_object* v_ref_4436_){
_start:
{
lean_object* v___f_4437_; lean_object* v___f_4438_; lean_object* v___x_4439_; uint8_t v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___f_4437_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4437_, 0, v_catName_4435_);
lean_inc(v_attrName_4434_);
v___f_4438_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4438_, 0, v_attrName_4434_);
v___x_4439_ = ((lean_object*)(l_Lean_Parser_mkParserAttributeImpl___closed__0));
v___x_4440_ = 1;
v___x_4441_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4441_, 0, v_ref_4436_);
lean_ctor_set(v___x_4441_, 1, v_attrName_4434_);
lean_ctor_set(v___x_4441_, 2, v___x_4439_);
lean_ctor_set_uint8(v___x_4441_, sizeof(void*)*3, v___x_4440_);
v___x_4442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
lean_ctor_set(v___x_4442_, 1, v___f_4437_);
lean_ctor_set(v___x_4442_, 2, v___f_4438_);
return v___x_4442_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4443_; 
v___x_4443_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* v_attrName_4444_, lean_object* v_catName_4445_, lean_object* v_ref_4446_){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4448_ = l_Lean_Parser_mkParserAttributeImpl(v_attrName_4444_, v_catName_4445_, v_ref_4446_);
v___x_4449_ = l_Lean_registerBuiltinAttribute(v___x_4448_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object* v_attrName_4450_, lean_object* v_catName_4451_, lean_object* v_ref_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4450_, v_catName_4451_, v_ref_4452_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object* v_ref_4458_, lean_object* v_args_4459_){
_start:
{
if (lean_obj_tag(v_args_4459_) == 1)
{
lean_object* v_head_4462_; 
v_head_4462_ = lean_ctor_get(v_args_4459_, 0);
lean_inc(v_head_4462_);
if (lean_obj_tag(v_head_4462_) == 2)
{
lean_object* v_tail_4463_; 
v_tail_4463_ = lean_ctor_get(v_args_4459_, 1);
lean_inc(v_tail_4463_);
lean_dec_ref_known(v_args_4459_, 2);
if (lean_obj_tag(v_tail_4463_) == 1)
{
lean_object* v_head_4464_; 
v_head_4464_ = lean_ctor_get(v_tail_4463_, 0);
lean_inc(v_head_4464_);
if (lean_obj_tag(v_head_4464_) == 2)
{
lean_object* v_tail_4465_; 
v_tail_4465_ = lean_ctor_get(v_tail_4463_, 1);
lean_inc(v_tail_4465_);
lean_dec_ref_known(v_tail_4463_, 2);
if (lean_obj_tag(v_tail_4465_) == 0)
{
lean_object* v_v_4466_; lean_object* v_v_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4475_; 
v_v_4466_ = lean_ctor_get(v_head_4462_, 0);
lean_inc(v_v_4466_);
lean_dec_ref_known(v_head_4462_, 1);
v_v_4467_ = lean_ctor_get(v_head_4464_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v_head_4464_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4469_ = v_head_4464_;
v_isShared_4470_ = v_isSharedCheck_4475_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_v_4467_);
lean_dec(v_head_4464_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4475_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4471_; lean_object* v___x_4473_; 
v___x_4471_ = l_Lean_Parser_mkParserAttributeImpl(v_v_4466_, v_v_4467_, v_ref_4458_);
if (v_isShared_4470_ == 0)
{
lean_ctor_set_tag(v___x_4469_, 1);
lean_ctor_set(v___x_4469_, 0, v___x_4471_);
v___x_4473_ = v___x_4469_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4471_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
else
{
lean_dec(v_tail_4465_);
lean_dec_ref_known(v_head_4464_, 1);
lean_dec_ref_known(v_head_4462_, 1);
lean_dec(v_ref_4458_);
goto v___jp_4460_;
}
}
else
{
lean_dec(v_head_4464_);
lean_dec_ref_known(v_tail_4463_, 2);
lean_dec_ref_known(v_head_4462_, 1);
lean_dec(v_ref_4458_);
goto v___jp_4460_;
}
}
else
{
lean_dec_ref_known(v_head_4462_, 1);
lean_dec(v_tail_4463_);
lean_dec(v_ref_4458_);
goto v___jp_4460_;
}
}
else
{
lean_dec_ref_known(v_args_4459_, 2);
lean_dec(v_head_4462_);
lean_dec(v_ref_4458_);
goto v___jp_4460_;
}
}
else
{
lean_dec(v_args_4459_);
lean_dec(v_ref_4458_);
goto v___jp_4460_;
}
v___jp_4460_:
{
lean_object* v___x_4461_; 
v___x_4461_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
return v___x_4461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___f_4481_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4482_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4483_ = l_Lean_registerAttributeImplBuilder(v___x_4482_, v___f_4481_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object* v_a_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
return v_res_4485_;
}
}
static lean_object* _init_l_Lean_Parser_registerParserCategory___auto__1(void){
_start:
{
lean_object* v___x_4486_; 
v___x_4486_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object* v_env_4487_, lean_object* v_attrName_4488_, lean_object* v_catName_4489_, uint8_t v_behavior_4490_, lean_object* v_ref_4491_){
_start:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
lean_inc(v_ref_4491_);
lean_inc(v_catName_4489_);
v___x_4493_ = l_Lean_Parser_addParserCategory(v_env_4487_, v_catName_4489_, v_ref_4491_, v_behavior_4490_);
v___x_4494_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_4493_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4508_; 
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4497_ = v___x_4494_;
v_isShared_4498_ = v_isSharedCheck_4508_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4494_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4508_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; lean_object* v___x_4501_; 
v___x_4499_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
if (v_isShared_4498_ == 0)
{
lean_ctor_set_tag(v___x_4497_, 2);
lean_ctor_set(v___x_4497_, 0, v_attrName_4488_);
v___x_4501_ = v___x_4497_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_attrName_4488_);
v___x_4501_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4502_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4502_, 0, v_catName_4489_);
v___x_4503_ = lean_box(0);
v___x_4504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4502_);
lean_ctor_set(v___x_4504_, 1, v___x_4503_);
v___x_4505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4501_);
lean_ctor_set(v___x_4505_, 1, v___x_4504_);
v___x_4506_ = l_Lean_registerAttributeOfBuilder(v_a_4495_, v___x_4499_, v_ref_4491_, v___x_4505_);
return v___x_4506_;
}
}
}
else
{
lean_dec(v_ref_4491_);
lean_dec(v_catName_4489_);
lean_dec(v_attrName_4488_);
return v___x_4494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* v_env_4509_, lean_object* v_attrName_4510_, lean_object* v_catName_4511_, lean_object* v_behavior_4512_, lean_object* v_ref_4513_, lean_object* v_a_4514_){
_start:
{
uint8_t v_behavior_boxed_4515_; lean_object* v_res_4516_; 
v_behavior_boxed_4515_ = lean_unbox(v_behavior_4512_);
v_res_4516_ = l_Lean_Parser_registerParserCategory(v_env_4509_, v_attrName_4510_, v_catName_4511_, v_behavior_boxed_4515_, v_ref_4513_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4539_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4540_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4541_ = 0;
v___x_4542_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4543_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4539_, v___x_4540_, v___x_4541_, v___x_4542_);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object* v_a_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
return v_res_4545_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4551_ = lean_unsigned_to_nat(3431364690u);
v___x_4552_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4553_ = l_Lean_Name_num___override(v___x_4552_, v___x_4551_);
return v___x_4553_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4554_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4555_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4556_ = l_Lean_Name_str___override(v___x_4555_, v___x_4554_);
return v___x_4556_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4557_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4558_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4559_ = l_Lean_Name_str___override(v___x_4558_, v___x_4557_);
return v___x_4559_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4560_ = lean_unsigned_to_nat(2u);
v___x_4561_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4562_ = l_Lean_Name_num___override(v___x_4561_, v___x_4560_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4564_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4565_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4566_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4567_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4564_, v___x_4565_, v___x_4566_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object* v_a_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
return v_res_4569_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4579_ = lean_unsigned_to_nat(2342493449u);
v___x_4580_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4581_ = l_Lean_Name_num___override(v___x_4580_, v___x_4579_);
return v___x_4581_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4582_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4583_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4584_ = l_Lean_Name_str___override(v___x_4583_, v___x_4582_);
return v___x_4584_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4585_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4586_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4587_ = l_Lean_Name_str___override(v___x_4586_, v___x_4585_);
return v___x_4587_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4588_ = lean_unsigned_to_nat(2u);
v___x_4589_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4590_ = l_Lean_Name_num___override(v___x_4589_, v___x_4588_);
return v___x_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; uint8_t v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4592_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4593_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4594_ = 0;
v___x_4595_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4596_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4592_, v___x_4593_, v___x_4594_, v___x_4595_);
return v___x_4596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object* v_a_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
return v_res_4598_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4604_ = lean_unsigned_to_nat(3226070615u);
v___x_4605_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4606_ = l_Lean_Name_num___override(v___x_4605_, v___x_4604_);
return v___x_4606_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4607_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4608_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4609_ = l_Lean_Name_str___override(v___x_4608_, v___x_4607_);
return v___x_4609_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4610_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4611_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4612_ = l_Lean_Name_str___override(v___x_4611_, v___x_4610_);
return v___x_4612_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4613_ = lean_unsigned_to_nat(2u);
v___x_4614_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4615_ = l_Lean_Name_num___override(v___x_4614_, v___x_4613_);
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4617_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4618_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4619_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4620_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4617_, v___x_4618_, v___x_4619_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object* v_a_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* v_rbp_4623_){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4624_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4625_ = l_Lean_Parser_categoryParser(v___x_4624_, v_rbp_4623_);
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t v_addOpenSimple_4626_, lean_object* v_x_4627_, lean_object* v_x_4628_){
_start:
{
if (lean_obj_tag(v_x_4628_) == 0)
{
return v_x_4627_;
}
else
{
lean_object* v_head_4629_; lean_object* v_tail_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4653_; 
v_head_4629_ = lean_ctor_get(v_x_4628_, 0);
v_tail_4630_ = lean_ctor_get(v_x_4628_, 1);
v_isSharedCheck_4653_ = !lean_is_exclusive(v_x_4628_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4632_ = v_x_4628_;
v_isShared_4633_ = v_isSharedCheck_4653_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_tail_4630_);
lean_inc(v_head_4629_);
lean_dec(v_x_4628_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4653_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v_fst_4634_; lean_object* v_snd_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4652_; 
v_fst_4634_ = lean_ctor_get(v_x_4627_, 0);
v_snd_4635_ = lean_ctor_get(v_x_4627_, 1);
v_isSharedCheck_4652_ = !lean_is_exclusive(v_x_4627_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4637_ = v_x_4627_;
v_isShared_4638_ = v_isSharedCheck_4652_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_snd_4635_);
lean_inc(v_fst_4634_);
lean_dec(v_x_4627_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4652_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___y_4640_; 
if (v_addOpenSimple_4626_ == 0)
{
lean_del_object(v___x_4632_);
v___y_4640_ = v_snd_4635_;
goto v___jp_4639_;
}
else
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4650_; 
v___x_4647_ = lean_box(0);
lean_inc(v_head_4629_);
v___x_4648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4648_, 0, v_head_4629_);
lean_ctor_set(v___x_4648_, 1, v___x_4647_);
if (v_isShared_4633_ == 0)
{
lean_ctor_set(v___x_4632_, 1, v_snd_4635_);
lean_ctor_set(v___x_4632_, 0, v___x_4648_);
v___x_4650_ = v___x_4632_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4648_);
lean_ctor_set(v_reuseFailAlloc_4651_, 1, v_snd_4635_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
v___y_4640_ = v___x_4650_;
goto v___jp_4639_;
}
}
v___jp_4639_:
{
lean_object* v___x_4641_; lean_object* v_env_4642_; lean_object* v___x_4644_; 
v___x_4641_ = l_Lean_Parser_parserExtension;
v_env_4642_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v___x_4641_, v_fst_4634_, v_head_4629_);
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 1, v___y_4640_);
lean_ctor_set(v___x_4637_, 0, v_env_4642_);
v___x_4644_ = v___x_4637_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_env_4642_);
lean_ctor_set(v_reuseFailAlloc_4646_, 1, v___y_4640_);
v___x_4644_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
v_x_4627_ = v___x_4644_;
v_x_4628_ = v_tail_4630_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object* v_addOpenSimple_4654_, lean_object* v_x_4655_, lean_object* v_x_4656_){
_start:
{
uint8_t v_addOpenSimple_boxed_4657_; lean_object* v_res_4658_; 
v_addOpenSimple_boxed_4657_ = lean_unbox(v_addOpenSimple_4654_);
v_res_4658_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_boxed_4657_, v_x_4655_, v_x_4656_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t v_addOpenSimple_4659_, lean_object* v_as_4660_, size_t v_i_4661_, size_t v_stop_4662_, lean_object* v_b_4663_){
_start:
{
uint8_t v___x_4664_; 
v___x_4664_ = lean_usize_dec_eq(v_i_4661_, v_stop_4662_);
if (v___x_4664_ == 0)
{
lean_object* v_toParserModuleContext_4665_; lean_object* v_toInputContext_4666_; lean_object* v_toCacheableParserContext_4667_; lean_object* v_tokens_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4695_; 
v_toParserModuleContext_4665_ = lean_ctor_get(v_b_4663_, 1);
v_toInputContext_4666_ = lean_ctor_get(v_b_4663_, 0);
v_toCacheableParserContext_4667_ = lean_ctor_get(v_b_4663_, 2);
v_tokens_4668_ = lean_ctor_get(v_b_4663_, 3);
v_isSharedCheck_4695_ = !lean_is_exclusive(v_b_4663_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4670_ = v_b_4663_;
v_isShared_4671_ = v_isSharedCheck_4695_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_tokens_4668_);
lean_inc(v_toCacheableParserContext_4667_);
lean_inc(v_toParserModuleContext_4665_);
lean_inc(v_toInputContext_4666_);
lean_dec(v_b_4663_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4695_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v_env_4672_; lean_object* v_options_4673_; lean_object* v_currNamespace_4674_; lean_object* v_openDecls_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4694_; 
v_env_4672_ = lean_ctor_get(v_toParserModuleContext_4665_, 0);
v_options_4673_ = lean_ctor_get(v_toParserModuleContext_4665_, 1);
v_currNamespace_4674_ = lean_ctor_get(v_toParserModuleContext_4665_, 2);
v_openDecls_4675_ = lean_ctor_get(v_toParserModuleContext_4665_, 3);
v_isSharedCheck_4694_ = !lean_is_exclusive(v_toParserModuleContext_4665_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4677_ = v_toParserModuleContext_4665_;
v_isShared_4678_ = v_isSharedCheck_4694_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_openDecls_4675_);
lean_inc(v_currNamespace_4674_);
lean_inc(v_options_4673_);
lean_inc(v_env_4672_);
lean_dec(v_toParserModuleContext_4665_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4694_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4679_; lean_object* v_nss_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v_fst_4683_; lean_object* v_snd_4684_; lean_object* v___x_4686_; 
v___x_4679_ = lean_array_uget_borrowed(v_as_4660_, v_i_4661_);
lean_inc(v___x_4679_);
lean_inc(v_openDecls_4675_);
lean_inc(v_currNamespace_4674_);
lean_inc_ref(v_env_4672_);
v_nss_4680_ = l_Lean_ResolveName_resolveNamespace(v_env_4672_, v_currNamespace_4674_, v_openDecls_4675_, v___x_4679_);
v___x_4681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4681_, 0, v_env_4672_);
lean_ctor_set(v___x_4681_, 1, v_openDecls_4675_);
v___x_4682_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4659_, v___x_4681_, v_nss_4680_);
v_fst_4683_ = lean_ctor_get(v___x_4682_, 0);
lean_inc(v_fst_4683_);
v_snd_4684_ = lean_ctor_get(v___x_4682_, 1);
lean_inc(v_snd_4684_);
lean_dec_ref(v___x_4682_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 3, v_snd_4684_);
lean_ctor_set(v___x_4677_, 0, v_fst_4683_);
v___x_4686_ = v___x_4677_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_fst_4683_);
lean_ctor_set(v_reuseFailAlloc_4693_, 1, v_options_4673_);
lean_ctor_set(v_reuseFailAlloc_4693_, 2, v_currNamespace_4674_);
lean_ctor_set(v_reuseFailAlloc_4693_, 3, v_snd_4684_);
v___x_4686_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
lean_object* v___x_4688_; 
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 1, v___x_4686_);
v___x_4688_ = v___x_4670_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_toInputContext_4666_);
lean_ctor_set(v_reuseFailAlloc_4692_, 1, v___x_4686_);
lean_ctor_set(v_reuseFailAlloc_4692_, 2, v_toCacheableParserContext_4667_);
lean_ctor_set(v_reuseFailAlloc_4692_, 3, v_tokens_4668_);
v___x_4688_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
size_t v___x_4689_; size_t v___x_4690_; 
v___x_4689_ = ((size_t)1ULL);
v___x_4690_ = lean_usize_add(v_i_4661_, v___x_4689_);
v_i_4661_ = v___x_4690_;
v_b_4663_ = v___x_4688_;
goto _start;
}
}
}
}
}
else
{
return v_b_4663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object* v_addOpenSimple_4696_, lean_object* v_as_4697_, lean_object* v_i_4698_, lean_object* v_stop_4699_, lean_object* v_b_4700_){
_start:
{
uint8_t v_addOpenSimple_boxed_4701_; size_t v_i_boxed_4702_; size_t v_stop_boxed_4703_; lean_object* v_res_4704_; 
v_addOpenSimple_boxed_4701_ = lean_unbox(v_addOpenSimple_4696_);
v_i_boxed_4702_ = lean_unbox_usize(v_i_4698_);
lean_dec(v_i_4698_);
v_stop_boxed_4703_ = lean_unbox_usize(v_stop_4699_);
lean_dec(v_stop_4699_);
v_res_4704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_boxed_4701_, v_as_4697_, v_i_boxed_4702_, v_stop_boxed_4703_, v_b_4700_);
lean_dec_ref(v_as_4697_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object* v___x_4705_, lean_object* v_ids_4706_, uint8_t v_addOpenSimple_4707_, lean_object* v_c_4708_){
_start:
{
lean_object* v___y_4710_; lean_object* v___x_4729_; lean_object* v___x_4730_; uint8_t v___x_4731_; 
v___x_4729_ = lean_unsigned_to_nat(0u);
v___x_4730_ = lean_array_get_size(v_ids_4706_);
v___x_4731_ = lean_nat_dec_lt(v___x_4729_, v___x_4730_);
if (v___x_4731_ == 0)
{
v___y_4710_ = v_c_4708_;
goto v___jp_4709_;
}
else
{
uint8_t v___x_4732_; 
v___x_4732_ = lean_nat_dec_le(v___x_4730_, v___x_4730_);
if (v___x_4732_ == 0)
{
if (v___x_4731_ == 0)
{
v___y_4710_ = v_c_4708_;
goto v___jp_4709_;
}
else
{
size_t v___x_4733_; size_t v___x_4734_; lean_object* v___x_4735_; 
v___x_4733_ = ((size_t)0ULL);
v___x_4734_ = lean_usize_of_nat(v___x_4730_);
v___x_4735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4707_, v_ids_4706_, v___x_4733_, v___x_4734_, v_c_4708_);
v___y_4710_ = v___x_4735_;
goto v___jp_4709_;
}
}
else
{
size_t v___x_4736_; size_t v___x_4737_; lean_object* v___x_4738_; 
v___x_4736_ = ((size_t)0ULL);
v___x_4737_ = lean_usize_of_nat(v___x_4730_);
v___x_4738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4707_, v_ids_4706_, v___x_4736_, v___x_4737_, v_c_4708_);
v___y_4710_ = v___x_4738_;
goto v___jp_4709_;
}
}
v___jp_4709_:
{
lean_object* v_toParserModuleContext_4711_; lean_object* v_toInputContext_4712_; lean_object* v_toCacheableParserContext_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4727_; 
v_toParserModuleContext_4711_ = lean_ctor_get(v___y_4710_, 1);
v_toInputContext_4712_ = lean_ctor_get(v___y_4710_, 0);
v_toCacheableParserContext_4713_ = lean_ctor_get(v___y_4710_, 2);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___y_4710_);
if (v_isSharedCheck_4727_ == 0)
{
lean_object* v_unused_4728_; 
v_unused_4728_ = lean_ctor_get(v___y_4710_, 3);
lean_dec(v_unused_4728_);
v___x_4715_ = v___y_4710_;
v_isShared_4716_ = v_isSharedCheck_4727_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_toCacheableParserContext_4713_);
lean_inc(v_toParserModuleContext_4711_);
lean_inc(v_toInputContext_4712_);
lean_dec(v___y_4710_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4727_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v_env_4717_; lean_object* v___x_4718_; lean_object* v_ext_4719_; lean_object* v_toEnvExtension_4720_; lean_object* v_asyncMode_4721_; lean_object* v___x_4722_; lean_object* v_tokens_4723_; lean_object* v___x_4725_; 
v_env_4717_ = lean_ctor_get(v_toParserModuleContext_4711_, 0);
v___x_4718_ = l_Lean_Parser_parserExtension;
v_ext_4719_ = lean_ctor_get(v___x_4718_, 1);
v_toEnvExtension_4720_ = lean_ctor_get(v_ext_4719_, 0);
v_asyncMode_4721_ = lean_ctor_get(v_toEnvExtension_4720_, 2);
lean_inc_ref(v_env_4717_);
v___x_4722_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4705_, v___x_4718_, v_env_4717_, v_asyncMode_4721_);
v_tokens_4723_ = lean_ctor_get(v___x_4722_, 0);
lean_inc_ref(v_tokens_4723_);
lean_dec(v___x_4722_);
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 3, v_tokens_4723_);
v___x_4725_ = v___x_4715_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_toInputContext_4712_);
lean_ctor_set(v_reuseFailAlloc_4726_, 1, v_toParserModuleContext_4711_);
lean_ctor_set(v_reuseFailAlloc_4726_, 2, v_toCacheableParserContext_4713_);
lean_ctor_set(v_reuseFailAlloc_4726_, 3, v_tokens_4723_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object* v___x_4739_, lean_object* v_ids_4740_, lean_object* v_addOpenSimple_4741_, lean_object* v_c_4742_){
_start:
{
uint8_t v_addOpenSimple_boxed_4743_; lean_object* v_res_4744_; 
v_addOpenSimple_boxed_4743_ = lean_unbox(v_addOpenSimple_4741_);
v_res_4744_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_4739_, v_ids_4740_, v_addOpenSimple_boxed_4743_, v_c_4742_);
lean_dec_ref(v_ids_4740_);
lean_dec_ref(v___x_4739_);
return v_res_4744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* v_ids_4745_, uint8_t v_addOpenSimple_4746_, lean_object* v_p_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___f_4752_; lean_object* v___x_4753_; 
v___x_4750_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4751_ = lean_box(v_addOpenSimple_4746_);
v___f_4752_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4752_, 0, v___x_4750_);
lean_closure_set(v___f_4752_, 1, v_ids_4745_);
lean_closure_set(v___f_4752_, 2, v___x_4751_);
v___x_4753_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_4752_, v_p_4747_, v_a_4748_, v_a_4749_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* v_ids_4754_, lean_object* v_addOpenSimple_4755_, lean_object* v_p_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_){
_start:
{
uint8_t v_addOpenSimple_boxed_4759_; lean_object* v_res_4760_; 
v_addOpenSimple_boxed_4759_ = lean_unbox(v_addOpenSimple_4755_);
v_res_4760_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_4754_, v_addOpenSimple_boxed_4759_, v_p_4756_, v_a_4757_, v_a_4758_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t v_sz_4761_, size_t v_i_4762_, lean_object* v_bs_4763_){
_start:
{
uint8_t v___x_4764_; 
v___x_4764_ = lean_usize_dec_lt(v_i_4762_, v_sz_4761_);
if (v___x_4764_ == 0)
{
return v_bs_4763_;
}
else
{
lean_object* v_v_4765_; lean_object* v___x_4766_; lean_object* v_bs_x27_4767_; lean_object* v___x_4768_; size_t v___x_4769_; size_t v___x_4770_; lean_object* v___x_4771_; 
v_v_4765_ = lean_array_uget(v_bs_4763_, v_i_4762_);
v___x_4766_ = lean_unsigned_to_nat(0u);
v_bs_x27_4767_ = lean_array_uset(v_bs_4763_, v_i_4762_, v___x_4766_);
v___x_4768_ = l_Lean_Syntax_getId(v_v_4765_);
lean_dec(v_v_4765_);
v___x_4769_ = ((size_t)1ULL);
v___x_4770_ = lean_usize_add(v_i_4762_, v___x_4769_);
v___x_4771_ = lean_array_uset(v_bs_x27_4767_, v_i_4762_, v___x_4768_);
v_i_4762_ = v___x_4770_;
v_bs_4763_ = v___x_4771_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object* v_sz_4773_, lean_object* v_i_4774_, lean_object* v_bs_4775_){
_start:
{
size_t v_sz_boxed_4776_; size_t v_i_boxed_4777_; lean_object* v_res_4778_; 
v_sz_boxed_4776_ = lean_unbox_usize(v_sz_4773_);
lean_dec(v_sz_4773_);
v_i_boxed_4777_ = lean_unbox_usize(v_i_4774_);
lean_dec(v_i_4774_);
v_res_4778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_boxed_4776_, v_i_boxed_4777_, v_bs_4775_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* v_openDeclStx_4792_, lean_object* v_p_4793_, lean_object* v_c_4794_, lean_object* v_s_4795_){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; uint8_t v___x_4798_; 
lean_inc(v_openDeclStx_4792_);
v___x_4796_ = l_Lean_Syntax_getKind(v_openDeclStx_4792_);
v___x_4797_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__2));
v___x_4798_ = lean_name_eq(v___x_4796_, v___x_4797_);
if (v___x_4798_ == 0)
{
lean_object* v___x_4799_; uint8_t v___x_4800_; 
v___x_4799_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__4));
v___x_4800_ = lean_name_eq(v___x_4796_, v___x_4799_);
lean_dec(v___x_4796_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; 
lean_dec(v_openDeclStx_4792_);
v___x_4801_ = lean_apply_2(v_p_4793_, v_c_4794_, v_s_4795_);
return v___x_4801_;
}
else
{
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; size_t v_sz_4805_; size_t v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4802_ = lean_unsigned_to_nat(1u);
v___x_4803_ = l_Lean_Syntax_getArg(v_openDeclStx_4792_, v___x_4802_);
lean_dec(v_openDeclStx_4792_);
v___x_4804_ = l_Lean_Syntax_getArgs(v___x_4803_);
lean_dec(v___x_4803_);
v_sz_4805_ = lean_array_size(v___x_4804_);
v___x_4806_ = ((size_t)0ULL);
v___x_4807_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4805_, v___x_4806_, v___x_4804_);
v___x_4808_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4807_, v___x_4798_, v_p_4793_, v_c_4794_, v_s_4795_);
return v___x_4808_;
}
}
else
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; size_t v_sz_4812_; size_t v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
lean_dec(v___x_4796_);
v___x_4809_ = lean_unsigned_to_nat(0u);
v___x_4810_ = l_Lean_Syntax_getArg(v_openDeclStx_4792_, v___x_4809_);
lean_dec(v_openDeclStx_4792_);
v___x_4811_ = l_Lean_Syntax_getArgs(v___x_4810_);
lean_dec(v___x_4810_);
v_sz_4812_ = lean_array_size(v___x_4811_);
v___x_4813_ = ((size_t)0ULL);
v___x_4814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4812_, v___x_4813_, v___x_4811_);
v___x_4815_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4814_, v___x_4798_, v_p_4793_, v_c_4794_, v_s_4795_);
return v___x_4815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* v_p_4822_, lean_object* v_c_4823_, lean_object* v_s_4824_){
_start:
{
lean_object* v_stxStack_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; uint8_t v___x_4828_; 
v_stxStack_4825_ = lean_ctor_get(v_s_4824_, 0);
v___x_4826_ = lean_unsigned_to_nat(0u);
v___x_4827_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4825_);
v___x_4828_ = lean_nat_dec_lt(v___x_4826_, v___x_4827_);
lean_dec(v___x_4827_);
if (v___x_4828_ == 0)
{
lean_object* v___x_4829_; 
v___x_4829_ = lean_apply_2(v_p_4822_, v_c_4823_, v_s_4824_);
return v___x_4829_;
}
else
{
lean_object* v_stx_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; uint8_t v___x_4833_; 
v_stx_4830_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4825_);
lean_inc(v_stx_4830_);
v___x_4831_ = l_Lean_Syntax_getKind(v_stx_4830_);
v___x_4832_ = ((lean_object*)(l_Lean_Parser_withOpenFn___closed__1));
v___x_4833_ = lean_name_eq(v___x_4831_, v___x_4832_);
lean_dec(v___x_4831_);
if (v___x_4833_ == 0)
{
lean_object* v___x_4834_; 
lean_dec(v_stx_4830_);
v___x_4834_ = lean_apply_2(v_p_4822_, v_c_4823_, v_s_4824_);
return v___x_4834_;
}
else
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4835_ = lean_unsigned_to_nat(1u);
v___x_4836_ = l_Lean_Syntax_getArg(v_stx_4830_, v___x_4835_);
lean_dec(v_stx_4830_);
v___x_4837_ = l_Lean_Parser_withOpenDeclFnCore(v___x_4836_, v_p_4822_, v_c_4823_, v_s_4824_);
return v___x_4837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* v_p_4838_){
_start:
{
lean_object* v_info_4839_; lean_object* v_fn_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4848_; 
v_info_4839_ = lean_ctor_get(v_p_4838_, 0);
v_fn_4840_ = lean_ctor_get(v_p_4838_, 1);
v_isSharedCheck_4848_ = !lean_is_exclusive(v_p_4838_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4842_ = v_p_4838_;
v_isShared_4843_ = v_isSharedCheck_4848_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_fn_4840_);
lean_inc(v_info_4839_);
lean_dec(v_p_4838_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4848_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4844_; lean_object* v___x_4846_; 
v___x_4844_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(v___x_4844_, 0, v_fn_4840_);
if (v_isShared_4843_ == 0)
{
lean_ctor_set(v___x_4842_, 1, v___x_4844_);
v___x_4846_ = v___x_4842_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_info_4839_);
lean_ctor_set(v_reuseFailAlloc_4847_, 1, v___x_4844_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* v_p_4849_, lean_object* v_c_4850_, lean_object* v_s_4851_){
_start:
{
lean_object* v_stxStack_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; uint8_t v___x_4855_; 
v_stxStack_4852_ = lean_ctor_get(v_s_4851_, 0);
v___x_4853_ = lean_unsigned_to_nat(0u);
v___x_4854_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4852_);
v___x_4855_ = lean_nat_dec_lt(v___x_4853_, v___x_4854_);
lean_dec(v___x_4854_);
if (v___x_4855_ == 0)
{
lean_object* v___x_4856_; 
v___x_4856_ = lean_apply_2(v_p_4849_, v_c_4850_, v_s_4851_);
return v___x_4856_;
}
else
{
lean_object* v_stx_4857_; lean_object* v___x_4858_; 
v_stx_4857_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4852_);
v___x_4858_ = l_Lean_Parser_withOpenDeclFnCore(v_stx_4857_, v_p_4849_, v_c_4850_, v_s_4851_);
return v___x_4858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* v_p_4859_){
_start:
{
lean_object* v_info_4860_; lean_object* v_fn_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4869_; 
v_info_4860_ = lean_ctor_get(v_p_4859_, 0);
v_fn_4861_ = lean_ctor_get(v_p_4859_, 1);
v_isSharedCheck_4869_ = !lean_is_exclusive(v_p_4859_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4863_ = v_p_4859_;
v_isShared_4864_ = v_isSharedCheck_4869_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_fn_4861_);
lean_inc(v_info_4860_);
lean_dec(v_p_4859_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4869_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4865_; lean_object* v___x_4867_; 
v___x_4865_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(v___x_4865_, 0, v_fn_4861_);
if (v_isShared_4864_ == 0)
{
lean_ctor_set(v___x_4863_, 1, v___x_4865_);
v___x_4867_ = v___x_4863_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_info_4860_);
lean_ctor_set(v_reuseFailAlloc_4868_, 1, v___x_4865_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object* v_val_4876_){
_start:
{
lean_object* v___x_4884_; 
v___x_4884_ = l_Lean_Syntax_isStrLit_x3f(v_val_4876_);
if (lean_obj_tag(v___x_4884_) == 1)
{
lean_object* v_val_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4893_; 
v_val_4885_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4887_ = v___x_4884_;
v_isShared_4888_ = v_isSharedCheck_4893_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_val_4885_);
lean_dec(v___x_4884_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4893_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4889_; lean_object* v___x_4891_; 
v___x_4889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4889_, 0, v_val_4885_);
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 0, v___x_4889_);
v___x_4891_ = v___x_4887_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
else
{
lean_object* v___x_4894_; 
lean_dec(v___x_4884_);
v___x_4894_ = l_Lean_Syntax_isNatLit_x3f(v_val_4876_);
if (lean_obj_tag(v___x_4894_) == 1)
{
lean_object* v_val_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4903_; 
v_val_4895_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4897_ = v___x_4894_;
v_isShared_4898_ = v_isSharedCheck_4903_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_val_4895_);
lean_dec(v___x_4894_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4903_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4899_; lean_object* v___x_4901_; 
v___x_4899_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4899_, 0, v_val_4895_);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 0, v___x_4899_);
v___x_4901_ = v___x_4897_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4899_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
else
{
lean_dec(v___x_4894_);
if (lean_obj_tag(v_val_4876_) == 2)
{
lean_object* v_val_4904_; lean_object* v___x_4905_; uint8_t v___x_4906_; 
v_val_4904_ = lean_ctor_get(v_val_4876_, 1);
v___x_4905_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3));
v___x_4906_ = lean_string_dec_eq(v_val_4904_, v___x_4905_);
if (v___x_4906_ == 0)
{
goto v___jp_4877_;
}
else
{
lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4907_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4907_, 0, v___x_4906_);
v___x_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4907_);
return v___x_4908_;
}
}
else
{
goto v___jp_4877_;
}
}
}
v___jp_4877_:
{
if (lean_obj_tag(v_val_4876_) == 2)
{
lean_object* v_val_4878_; lean_object* v___x_4879_; uint8_t v___x_4880_; 
v_val_4878_ = lean_ctor_get(v_val_4876_, 1);
v___x_4879_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0));
v___x_4880_ = lean_string_dec_eq(v_val_4878_, v___x_4879_);
if (v___x_4880_ == 0)
{
lean_object* v___x_4881_; 
v___x_4881_ = lean_box(0);
return v___x_4881_;
}
else
{
lean_object* v___x_4882_; 
v___x_4882_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2));
return v___x_4882_;
}
}
else
{
lean_object* v___x_4883_; 
v___x_4883_ = lean_box(0);
return v___x_4883_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object* v_val_4909_){
_start:
{
lean_object* v_res_4910_; 
v_res_4910_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_val_4909_);
lean_dec(v_val_4909_);
return v_res_4910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object* v_nameStx_4911_, lean_object* v_v_4912_, lean_object* v_c_4913_){
_start:
{
lean_object* v_toParserModuleContext_4914_; lean_object* v_toInputContext_4915_; lean_object* v_toCacheableParserContext_4916_; lean_object* v_tokens_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4954_; 
v_toParserModuleContext_4914_ = lean_ctor_get(v_c_4913_, 1);
v_toInputContext_4915_ = lean_ctor_get(v_c_4913_, 0);
v_toCacheableParserContext_4916_ = lean_ctor_get(v_c_4913_, 2);
v_tokens_4917_ = lean_ctor_get(v_c_4913_, 3);
v_isSharedCheck_4954_ = !lean_is_exclusive(v_c_4913_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4919_ = v_c_4913_;
v_isShared_4920_ = v_isSharedCheck_4954_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_tokens_4917_);
lean_inc(v_toCacheableParserContext_4916_);
lean_inc(v_toParserModuleContext_4914_);
lean_inc(v_toInputContext_4915_);
lean_dec(v_c_4913_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4954_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v_env_4921_; lean_object* v_options_4922_; lean_object* v_currNamespace_4923_; lean_object* v_openDecls_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4953_; 
v_env_4921_ = lean_ctor_get(v_toParserModuleContext_4914_, 0);
v_options_4922_ = lean_ctor_get(v_toParserModuleContext_4914_, 1);
v_currNamespace_4923_ = lean_ctor_get(v_toParserModuleContext_4914_, 2);
v_openDecls_4924_ = lean_ctor_get(v_toParserModuleContext_4914_, 3);
v_isSharedCheck_4953_ = !lean_is_exclusive(v_toParserModuleContext_4914_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4926_ = v_toParserModuleContext_4914_;
v_isShared_4927_ = v_isSharedCheck_4953_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_openDecls_4924_);
lean_inc(v_currNamespace_4923_);
lean_inc(v_options_4922_);
lean_inc(v_env_4921_);
lean_dec(v_toParserModuleContext_4914_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4953_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___y_4929_; lean_object* v_map_4936_; uint8_t v_hasTrace_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4952_; 
v_map_4936_ = lean_ctor_get(v_options_4922_, 0);
v_hasTrace_4937_ = lean_ctor_get_uint8(v_options_4922_, sizeof(void*)*1);
v_isSharedCheck_4952_ = !lean_is_exclusive(v_options_4922_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4939_ = v_options_4922_;
v_isShared_4940_ = v_isSharedCheck_4952_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_map_4936_);
lean_dec(v_options_4922_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4952_;
goto v_resetjp_4938_;
}
v___jp_4928_:
{
lean_object* v___x_4931_; 
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 1, v___y_4929_);
v___x_4931_ = v___x_4926_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_env_4921_);
lean_ctor_set(v_reuseFailAlloc_4935_, 1, v___y_4929_);
lean_ctor_set(v_reuseFailAlloc_4935_, 2, v_currNamespace_4923_);
lean_ctor_set(v_reuseFailAlloc_4935_, 3, v_openDecls_4924_);
v___x_4931_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
lean_object* v___x_4933_; 
if (v_isShared_4920_ == 0)
{
lean_ctor_set(v___x_4919_, 1, v___x_4931_);
v___x_4933_ = v___x_4919_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_toInputContext_4915_);
lean_ctor_set(v_reuseFailAlloc_4934_, 1, v___x_4931_);
lean_ctor_set(v_reuseFailAlloc_4934_, 2, v_toCacheableParserContext_4916_);
lean_ctor_set(v_reuseFailAlloc_4934_, 3, v_tokens_4917_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
v_resetjp_4938_:
{
lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4941_ = l_Lean_Syntax_getId(v_nameStx_4911_);
v___x_4942_ = l_Lean_Name_eraseMacroScopes(v___x_4941_);
lean_dec(v___x_4941_);
lean_inc(v___x_4942_);
v___x_4943_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_4942_, v_v_4912_, v_map_4936_);
if (v_hasTrace_4937_ == 0)
{
lean_object* v___x_4944_; uint8_t v___x_4945_; lean_object* v___x_4947_; 
v___x_4944_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_4945_ = l_Lean_Name_isPrefixOf(v___x_4944_, v___x_4942_);
lean_dec(v___x_4942_);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 0, v___x_4943_);
v___x_4947_ = v___x_4939_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v___x_4943_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
lean_ctor_set_uint8(v___x_4947_, sizeof(void*)*1, v___x_4945_);
v___y_4929_ = v___x_4947_;
goto v___jp_4928_;
}
}
else
{
lean_object* v___x_4950_; 
lean_dec(v___x_4942_);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 0, v___x_4943_);
v___x_4950_ = v___x_4939_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4943_);
lean_ctor_set_uint8(v_reuseFailAlloc_4951_, sizeof(void*)*1, v_hasTrace_4937_);
v___x_4950_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
v___y_4929_ = v___x_4950_;
goto v___jp_4928_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object* v_nameStx_4955_, lean_object* v_v_4956_, lean_object* v_c_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(v_nameStx_4955_, v_v_4956_, v_c_4957_);
lean_dec(v_nameStx_4955_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object* v_nameStx_4959_, lean_object* v_valStx_4960_, lean_object* v_p_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_valStx_4960_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v___x_4965_; 
lean_dec(v_nameStx_4959_);
v___x_4965_ = lean_apply_2(v_p_4961_, v_a_4962_, v_a_4963_);
return v___x_4965_;
}
else
{
lean_object* v_val_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v_val_4966_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_val_4966_);
lean_dec_ref_known(v___x_4964_, 1);
v___x_4967_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed), 3, 2);
lean_closure_set(v___x_4967_, 0, v_nameStx_4959_);
lean_closure_set(v___x_4967_, 1, v_val_4966_);
v___x_4968_ = l_Lean_Parser_adaptUncacheableContextFn(v___x_4967_, v_p_4961_, v_a_4962_, v_a_4963_);
return v___x_4968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object* v_nameStx_4969_, lean_object* v_valStx_4970_, lean_object* v_p_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v_nameStx_4969_, v_valStx_4970_, v_p_4971_, v_a_4972_, v_a_4973_);
lean_dec(v_valStx_4970_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object* v_p_4981_, lean_object* v_c_4982_, lean_object* v_s_4983_){
_start:
{
lean_object* v_stxStack_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; uint8_t v___x_4987_; 
v_stxStack_4984_ = lean_ctor_get(v_s_4983_, 0);
v___x_4985_ = lean_unsigned_to_nat(0u);
v___x_4986_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4984_);
v___x_4987_ = lean_nat_dec_lt(v___x_4985_, v___x_4986_);
lean_dec(v___x_4986_);
if (v___x_4987_ == 0)
{
lean_object* v___x_4988_; 
v___x_4988_ = lean_apply_2(v_p_4981_, v_c_4982_, v_s_4983_);
return v___x_4988_;
}
else
{
lean_object* v_stx_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; uint8_t v___x_4992_; 
v_stx_4989_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4984_);
lean_inc(v_stx_4989_);
v___x_4990_ = l_Lean_Syntax_getKind(v_stx_4989_);
v___x_4991_ = ((lean_object*)(l_Lean_Parser_withSetOptionFn___closed__1));
v___x_4992_ = lean_name_eq(v___x_4990_, v___x_4991_);
lean_dec(v___x_4990_);
if (v___x_4992_ == 0)
{
lean_object* v___x_4993_; 
lean_dec(v_stx_4989_);
v___x_4993_ = lean_apply_2(v_p_4981_, v_c_4982_, v_s_4983_);
return v___x_4993_;
}
else
{
lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v___x_4994_ = lean_unsigned_to_nat(1u);
v___x_4995_ = l_Lean_Syntax_getArg(v_stx_4989_, v___x_4994_);
v___x_4996_ = lean_unsigned_to_nat(3u);
v___x_4997_ = l_Lean_Syntax_getArg(v_stx_4989_, v___x_4996_);
lean_dec(v_stx_4989_);
v___x_4998_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_4995_, v___x_4997_, v_p_4981_, v_c_4982_, v_s_4983_);
lean_dec(v___x_4997_);
return v___x_4998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object* v_p_4999_){
_start:
{
lean_object* v_info_5000_; lean_object* v_fn_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5009_; 
v_info_5000_ = lean_ctor_get(v_p_4999_, 0);
v_fn_5001_ = lean_ctor_get(v_p_4999_, 1);
v_isSharedCheck_5009_ = !lean_is_exclusive(v_p_4999_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5003_ = v_p_4999_;
v_isShared_5004_ = v_isSharedCheck_5009_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_fn_5001_);
lean_inc(v_info_5000_);
lean_dec(v_p_4999_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5009_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5005_; lean_object* v___x_5007_; 
v___x_5005_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionFn), 3, 1);
lean_closure_set(v___x_5005_, 0, v_fn_5001_);
if (v_isShared_5004_ == 0)
{
lean_ctor_set(v___x_5003_, 1, v___x_5005_);
v___x_5007_ = v___x_5003_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_info_5000_);
lean_ctor_set(v_reuseFailAlloc_5008_, 1, v___x_5005_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object* v_p_5010_, lean_object* v_c_5011_, lean_object* v_s_5012_){
_start:
{
lean_object* v_stxStack_5013_; lean_object* v_sz_5014_; lean_object* v___x_5015_; uint8_t v___x_5016_; 
v_stxStack_5013_ = lean_ctor_get(v_s_5012_, 0);
v_sz_5014_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5013_);
v___x_5015_ = lean_unsigned_to_nat(3u);
v___x_5016_ = lean_nat_dec_le(v___x_5015_, v_sz_5014_);
if (v___x_5016_ == 0)
{
lean_object* v___x_5017_; 
lean_dec(v_sz_5014_);
v___x_5017_ = lean_apply_2(v_p_5010_, v_c_5011_, v_s_5012_);
return v___x_5017_;
}
else
{
lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5018_ = lean_nat_sub(v_sz_5014_, v___x_5015_);
lean_dec(v_sz_5014_);
v___x_5019_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5013_, v___x_5018_);
lean_dec(v___x_5018_);
v___x_5020_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5013_);
v___x_5021_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5019_, v___x_5020_, v_p_5010_, v_c_5011_, v_s_5012_);
lean_dec(v___x_5020_);
return v___x_5021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object* v_p_5022_){
_start:
{
lean_object* v_info_5023_; lean_object* v_fn_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5032_; 
v_info_5023_ = lean_ctor_get(v_p_5022_, 0);
v_fn_5024_ = lean_ctor_get(v_p_5022_, 1);
v_isSharedCheck_5032_ = !lean_is_exclusive(v_p_5022_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5026_ = v_p_5022_;
v_isShared_5027_ = v_isSharedCheck_5032_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_fn_5024_);
lean_inc(v_info_5023_);
lean_dec(v_p_5022_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5032_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5028_; lean_object* v___x_5030_; 
v___x_5028_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionValueFn), 3, 1);
lean_closure_set(v___x_5028_, 0, v_fn_5024_);
if (v_isShared_5027_ == 0)
{
lean_ctor_set(v___x_5026_, 1, v___x_5028_);
v___x_5030_ = v___x_5026_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_info_5023_);
lean_ctor_set(v_reuseFailAlloc_5031_, 1, v___x_5028_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object* v___x_5033_){
_start:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5035_ = lean_st_ref_get(v___x_5033_);
v___x_5036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5035_);
return v___x_5036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v___x_5037_, lean_object* v___y_5038_){
_start:
{
lean_object* v_res_5039_; 
v_res_5039_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_5037_);
lean_dec(v___x_5037_);
return v_res_5039_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5040_; lean_object* v___f_5041_; 
v___x_5040_ = l_Lean_Parser_parserAliasesRef;
v___f_5041_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5041_, 0, v___x_5040_);
return v___f_5041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
v___f_5043_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_);
v___x_5044_ = lean_box(0);
v___x_5045_ = lean_box(2);
v___x_5046_ = l_Lean_registerEnvExtension___redArg(v___f_5043_, v___x_5044_, v___x_5045_);
return v___x_5046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v_a_5047_){
_start:
{
lean_object* v_res_5048_; 
v_res_5048_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
return v_res_5048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx(lean_object* v_x_5049_){
_start:
{
switch(lean_obj_tag(v_x_5049_))
{
case 0:
{
lean_object* v___x_5050_; 
v___x_5050_ = lean_unsigned_to_nat(0u);
return v___x_5050_;
}
case 1:
{
lean_object* v___x_5051_; 
v___x_5051_ = lean_unsigned_to_nat(1u);
return v___x_5051_;
}
default: 
{
lean_object* v___x_5052_; 
v___x_5052_ = lean_unsigned_to_nat(2u);
return v___x_5052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___boxed(lean_object* v_x_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l_Lean_Parser_ParserResolution_ctorIdx(v_x_5053_);
lean_dec_ref(v_x_5053_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object* v_t_5055_, lean_object* v_k_5056_){
_start:
{
switch(lean_obj_tag(v_t_5055_))
{
case 0:
{
lean_object* v_cat_5057_; lean_object* v___x_5058_; 
v_cat_5057_ = lean_ctor_get(v_t_5055_, 0);
lean_inc(v_cat_5057_);
lean_dec_ref_known(v_t_5055_, 1);
v___x_5058_ = lean_apply_1(v_k_5056_, v_cat_5057_);
return v___x_5058_;
}
case 1:
{
lean_object* v_decl_5059_; uint8_t v_isDescr_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
v_decl_5059_ = lean_ctor_get(v_t_5055_, 0);
lean_inc(v_decl_5059_);
v_isDescr_5060_ = lean_ctor_get_uint8(v_t_5055_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5055_, 1);
v___x_5061_ = lean_box(v_isDescr_5060_);
v___x_5062_ = lean_apply_2(v_k_5056_, v_decl_5059_, v___x_5061_);
return v___x_5062_;
}
default: 
{
lean_object* v_p_5063_; lean_object* v___x_5064_; 
v_p_5063_ = lean_ctor_get(v_t_5055_, 0);
lean_inc_ref(v_p_5063_);
lean_dec_ref_known(v_t_5055_, 1);
v___x_5064_ = lean_apply_1(v_k_5056_, v_p_5063_);
return v___x_5064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object* v_motive_5065_, lean_object* v_ctorIdx_5066_, lean_object* v_t_5067_, lean_object* v_h_5068_, lean_object* v_k_5069_){
_start:
{
lean_object* v___x_5070_; 
v___x_5070_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5067_, v_k_5069_);
return v___x_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object* v_motive_5071_, lean_object* v_ctorIdx_5072_, lean_object* v_t_5073_, lean_object* v_h_5074_, lean_object* v_k_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l_Lean_Parser_ParserResolution_ctorElim(v_motive_5071_, v_ctorIdx_5072_, v_t_5073_, v_h_5074_, v_k_5075_);
lean_dec(v_ctorIdx_5072_);
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object* v_t_5077_, lean_object* v_category_5078_){
_start:
{
lean_object* v___x_5079_; 
v___x_5079_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5077_, v_category_5078_);
return v___x_5079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object* v_motive_5080_, lean_object* v_t_5081_, lean_object* v_h_5082_, lean_object* v_category_5083_){
_start:
{
lean_object* v___x_5084_; 
v___x_5084_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5081_, v_category_5083_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object* v_t_5085_, lean_object* v_parser_5086_){
_start:
{
lean_object* v___x_5087_; 
v___x_5087_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5085_, v_parser_5086_);
return v___x_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object* v_motive_5088_, lean_object* v_t_5089_, lean_object* v_h_5090_, lean_object* v_parser_5091_){
_start:
{
lean_object* v___x_5092_; 
v___x_5092_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5089_, v_parser_5091_);
return v___x_5092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object* v_t_5093_, lean_object* v_alias_5094_){
_start:
{
lean_object* v___x_5095_; 
v___x_5095_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5093_, v_alias_5094_);
return v___x_5095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object* v_motive_5096_, lean_object* v_t_5097_, lean_object* v_h_5098_, lean_object* v_alias_5099_){
_start:
{
lean_object* v___x_5100_; 
v___x_5100_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5097_, v_alias_5099_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object* v_env_5104_, lean_object* v_name_5105_){
_start:
{
uint8_t v___x_5106_; lean_object* v___x_5107_; 
v___x_5106_ = 0;
v___x_5107_ = l_Lean_Environment_find_x3f(v_env_5104_, v_name_5105_, v___x_5106_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v___x_5108_; 
v___x_5108_ = lean_box(0);
return v___x_5108_;
}
else
{
lean_object* v_val_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5156_; 
v_val_5109_ = lean_ctor_get(v___x_5107_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5111_ = v___x_5107_;
v_isShared_5112_ = v_isSharedCheck_5156_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_val_5109_);
lean_dec(v___x_5107_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5156_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5113_; 
v___x_5113_ = l_Lean_ConstantInfo_type(v_val_5109_);
lean_dec(v_val_5109_);
if (lean_obj_tag(v___x_5113_) == 4)
{
lean_object* v_declName_5114_; 
v_declName_5114_ = lean_ctor_get(v___x_5113_, 0);
lean_inc(v_declName_5114_);
lean_dec_ref_known(v___x_5113_, 2);
if (lean_obj_tag(v_declName_5114_) == 1)
{
lean_object* v_pre_5115_; 
v_pre_5115_ = lean_ctor_get(v_declName_5114_, 0);
lean_inc(v_pre_5115_);
if (lean_obj_tag(v_pre_5115_) == 1)
{
lean_object* v_pre_5116_; 
v_pre_5116_ = lean_ctor_get(v_pre_5115_, 0);
switch(lean_obj_tag(v_pre_5116_))
{
case 1:
{
lean_object* v_pre_5117_; 
lean_inc_ref(v_pre_5116_);
lean_del_object(v___x_5111_);
v_pre_5117_ = lean_ctor_get(v_pre_5116_, 0);
if (lean_obj_tag(v_pre_5117_) == 0)
{
lean_object* v_str_5118_; lean_object* v_str_5119_; lean_object* v_str_5120_; lean_object* v___x_5121_; uint8_t v___x_5122_; 
v_str_5118_ = lean_ctor_get(v_declName_5114_, 1);
lean_inc_ref(v_str_5118_);
lean_dec_ref_known(v_declName_5114_, 2);
v_str_5119_ = lean_ctor_get(v_pre_5115_, 1);
lean_inc_ref(v_str_5119_);
lean_dec_ref_known(v_pre_5115_, 2);
v_str_5120_ = lean_ctor_get(v_pre_5116_, 1);
lean_inc_ref(v_str_5120_);
lean_dec_ref_known(v_pre_5116_, 2);
v___x_5121_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5122_ = lean_string_dec_eq(v_str_5120_, v___x_5121_);
lean_dec_ref(v_str_5120_);
if (v___x_5122_ == 0)
{
lean_object* v___x_5123_; 
lean_dec_ref(v_str_5119_);
lean_dec_ref(v_str_5118_);
v___x_5123_ = lean_box(0);
return v___x_5123_;
}
else
{
lean_object* v___x_5124_; uint8_t v___x_5125_; 
v___x_5124_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_5125_ = lean_string_dec_eq(v_str_5119_, v___x_5124_);
lean_dec_ref(v_str_5119_);
if (v___x_5125_ == 0)
{
lean_object* v___x_5126_; 
lean_dec_ref(v_str_5118_);
v___x_5126_ = lean_box(0);
return v___x_5126_;
}
else
{
uint8_t v___x_5127_; 
v___x_5127_ = lean_string_dec_eq(v_str_5118_, v___x_5124_);
if (v___x_5127_ == 0)
{
lean_object* v___x_5128_; uint8_t v___x_5129_; 
v___x_5128_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_5129_ = lean_string_dec_eq(v_str_5118_, v___x_5128_);
lean_dec_ref(v_str_5118_);
if (v___x_5129_ == 0)
{
lean_object* v___x_5130_; 
v___x_5130_ = lean_box(0);
return v___x_5130_;
}
else
{
lean_object* v___x_5131_; 
v___x_5131_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5131_;
}
}
else
{
lean_object* v___x_5132_; 
lean_dec_ref(v_str_5118_);
v___x_5132_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5132_;
}
}
}
}
else
{
lean_object* v___x_5133_; 
lean_dec_ref_known(v_pre_5116_, 2);
lean_dec_ref_known(v_pre_5115_, 2);
lean_dec_ref_known(v_declName_5114_, 2);
v___x_5133_ = lean_box(0);
return v___x_5133_;
}
}
case 0:
{
lean_object* v_str_5134_; lean_object* v_str_5135_; lean_object* v___x_5136_; uint8_t v___x_5137_; 
v_str_5134_ = lean_ctor_get(v_declName_5114_, 1);
lean_inc_ref(v_str_5134_);
lean_dec_ref_known(v_declName_5114_, 2);
v_str_5135_ = lean_ctor_get(v_pre_5115_, 1);
lean_inc_ref(v_str_5135_);
lean_dec_ref_known(v_pre_5115_, 2);
v___x_5136_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5137_ = lean_string_dec_eq(v_str_5135_, v___x_5136_);
lean_dec_ref(v_str_5135_);
if (v___x_5137_ == 0)
{
lean_object* v___x_5138_; 
lean_dec_ref(v_str_5134_);
lean_del_object(v___x_5111_);
v___x_5138_ = lean_box(0);
return v___x_5138_;
}
else
{
lean_object* v___x_5139_; uint8_t v___x_5140_; 
v___x_5139_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_5140_ = lean_string_dec_eq(v_str_5134_, v___x_5139_);
if (v___x_5140_ == 0)
{
lean_object* v___x_5141_; uint8_t v___x_5142_; 
v___x_5141_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_5142_ = lean_string_dec_eq(v_str_5134_, v___x_5141_);
lean_dec_ref(v_str_5134_);
if (v___x_5142_ == 0)
{
lean_object* v___x_5143_; 
lean_del_object(v___x_5111_);
v___x_5143_ = lean_box(0);
return v___x_5143_;
}
else
{
lean_object* v___x_5144_; lean_object* v___x_5146_; 
v___x_5144_ = lean_box(v___x_5137_);
if (v_isShared_5112_ == 0)
{
lean_ctor_set(v___x_5111_, 0, v___x_5144_);
v___x_5146_ = v___x_5111_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v___x_5144_);
v___x_5146_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
return v___x_5146_;
}
}
}
else
{
lean_object* v___x_5148_; lean_object* v___x_5150_; 
lean_dec_ref(v_str_5134_);
v___x_5148_ = lean_box(v___x_5137_);
if (v_isShared_5112_ == 0)
{
lean_ctor_set(v___x_5111_, 0, v___x_5148_);
v___x_5150_ = v___x_5111_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v___x_5148_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
}
default: 
{
lean_object* v___x_5152_; 
lean_dec_ref_known(v_pre_5115_, 2);
lean_dec_ref_known(v_declName_5114_, 2);
lean_del_object(v___x_5111_);
v___x_5152_ = lean_box(0);
return v___x_5152_;
}
}
}
else
{
lean_object* v___x_5153_; 
lean_dec_ref_known(v_declName_5114_, 2);
lean_dec(v_pre_5115_);
lean_del_object(v___x_5111_);
v___x_5153_ = lean_box(0);
return v___x_5153_;
}
}
else
{
lean_object* v___x_5154_; 
lean_dec(v_declName_5114_);
lean_del_object(v___x_5111_);
v___x_5154_ = lean_box(0);
return v___x_5154_;
}
}
else
{
lean_object* v___x_5155_; 
lean_dec_ref(v___x_5113_);
lean_del_object(v___x_5111_);
v___x_5155_ = lean_box(0);
return v___x_5155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object* v_env_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_){
_start:
{
if (lean_obj_tag(v_a_5158_) == 0)
{
lean_object* v___x_5160_; 
lean_dec_ref(v_env_5157_);
v___x_5160_ = lean_array_to_list(v_a_5159_);
return v___x_5160_;
}
else
{
lean_object* v_head_5161_; lean_object* v_snd_5162_; 
v_head_5161_ = lean_ctor_get(v_a_5158_, 0);
v_snd_5162_ = lean_ctor_get(v_head_5161_, 1);
if (lean_obj_tag(v_snd_5162_) == 0)
{
lean_object* v_tail_5163_; lean_object* v_fst_5164_; lean_object* v___x_5165_; 
lean_inc(v_head_5161_);
v_tail_5163_ = lean_ctor_get(v_a_5158_, 1);
lean_inc(v_tail_5163_);
lean_dec_ref_known(v_a_5158_, 2);
v_fst_5164_ = lean_ctor_get(v_head_5161_, 0);
lean_inc_n(v_fst_5164_, 2);
lean_dec(v_head_5161_);
lean_inc_ref(v_env_5157_);
v___x_5165_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5157_, v_fst_5164_);
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_dec(v_fst_5164_);
v_a_5158_ = v_tail_5163_;
goto _start;
}
else
{
lean_object* v_val_5167_; lean_object* v___x_5168_; uint8_t v___x_5169_; lean_object* v___x_5170_; 
v_val_5167_ = lean_ctor_get(v___x_5165_, 0);
lean_inc(v_val_5167_);
lean_dec_ref_known(v___x_5165_, 1);
v___x_5168_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5168_, 0, v_fst_5164_);
v___x_5169_ = lean_unbox(v_val_5167_);
lean_dec(v_val_5167_);
lean_ctor_set_uint8(v___x_5168_, sizeof(void*)*1, v___x_5169_);
v___x_5170_ = lean_array_push(v_a_5159_, v___x_5168_);
v_a_5158_ = v_tail_5163_;
v_a_5159_ = v___x_5170_;
goto _start;
}
}
else
{
lean_object* v_tail_5172_; 
v_tail_5172_ = lean_ctor_get(v_a_5158_, 1);
lean_inc(v_tail_5172_);
lean_dec_ref_known(v_a_5158_, 2);
v_a_5158_ = v_tail_5172_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object* v_env_5177_, lean_object* v_as_x27_5178_, lean_object* v_b_5179_){
_start:
{
if (lean_obj_tag(v_as_x27_5178_) == 0)
{
lean_dec_ref(v_env_5177_);
lean_inc_ref(v_b_5179_);
return v_b_5179_;
}
else
{
lean_object* v_head_5180_; lean_object* v_tail_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; 
v_head_5180_ = lean_ctor_get(v_as_x27_5178_, 0);
v_tail_5181_ = lean_ctor_get(v_as_x27_5178_, 1);
v___x_5182_ = lean_box(0);
v___x_5183_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_5180_) == 1)
{
lean_object* v_fields_5184_; 
v_fields_5184_ = lean_ctor_get(v_head_5180_, 1);
if (lean_obj_tag(v_fields_5184_) == 0)
{
lean_object* v_n_5185_; lean_object* v___x_5186_; 
v_n_5185_ = lean_ctor_get(v_head_5180_, 0);
lean_inc(v_n_5185_);
lean_inc_ref(v_env_5177_);
v___x_5186_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5177_, v_n_5185_);
if (lean_obj_tag(v___x_5186_) == 1)
{
lean_object* v_val_5187_; lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5199_; 
lean_dec_ref(v_env_5177_);
v_val_5187_ = lean_ctor_get(v___x_5186_, 0);
v_isSharedCheck_5199_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5199_ == 0)
{
v___x_5189_ = v___x_5186_;
v_isShared_5190_ = v_isSharedCheck_5199_;
goto v_resetjp_5188_;
}
else
{
lean_inc(v_val_5187_);
lean_dec(v___x_5186_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5199_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v___x_5191_; uint8_t v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5196_; 
lean_inc(v_n_5185_);
v___x_5191_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5191_, 0, v_n_5185_);
v___x_5192_ = lean_unbox(v_val_5187_);
lean_dec(v_val_5187_);
lean_ctor_set_uint8(v___x_5191_, sizeof(void*)*1, v___x_5192_);
v___x_5193_ = lean_box(0);
v___x_5194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5194_, 0, v___x_5191_);
lean_ctor_set(v___x_5194_, 1, v___x_5193_);
if (v_isShared_5190_ == 0)
{
lean_ctor_set(v___x_5189_, 0, v___x_5194_);
v___x_5196_ = v___x_5189_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5198_; 
v_reuseFailAlloc_5198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5198_, 0, v___x_5194_);
v___x_5196_ = v_reuseFailAlloc_5198_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
lean_object* v___x_5197_; 
v___x_5197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5197_, 0, v___x_5196_);
lean_ctor_set(v___x_5197_, 1, v___x_5182_);
return v___x_5197_;
}
}
}
else
{
lean_dec(v___x_5186_);
v_as_x27_5178_ = v_tail_5181_;
v_b_5179_ = v___x_5183_;
goto _start;
}
}
else
{
v_as_x27_5178_ = v_tail_5181_;
v_b_5179_ = v___x_5183_;
goto _start;
}
}
else
{
v_as_x27_5178_ = v_tail_5181_;
v_b_5179_ = v___x_5183_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object* v_env_5203_, lean_object* v_as_x27_5204_, lean_object* v_b_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5203_, v_as_x27_5204_, v_b_5205_);
lean_dec_ref(v_b_5205_);
lean_dec(v_as_x27_5204_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object* v_env_5209_, lean_object* v_opts_5210_, lean_object* v_currNamespace_5211_, lean_object* v_openDecls_5212_, lean_object* v_ident_5213_){
_start:
{
if (lean_obj_tag(v_ident_5213_) == 3)
{
lean_object* v_val_5214_; lean_object* v_preresolved_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v_fst_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5253_; 
v_val_5214_ = lean_ctor_get(v_ident_5213_, 2);
lean_inc(v_val_5214_);
v_preresolved_5215_ = lean_ctor_get(v_ident_5213_, 3);
lean_inc(v_preresolved_5215_);
lean_dec_ref_known(v_ident_5213_, 4);
v___x_5216_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
lean_inc_ref(v_env_5209_);
v___x_5217_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5209_, v_preresolved_5215_, v___x_5216_);
lean_dec(v_preresolved_5215_);
v_fst_5218_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5253_ == 0)
{
lean_object* v_unused_5254_; 
v_unused_5254_ = lean_ctor_get(v___x_5217_, 1);
lean_dec(v_unused_5254_);
v___x_5220_ = v___x_5217_;
v_isShared_5221_ = v_isSharedCheck_5253_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_fst_5218_);
lean_dec(v___x_5217_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5253_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
if (lean_obj_tag(v_fst_5218_) == 0)
{
lean_object* v___x_5222_; uint8_t v___x_5223_; 
v___x_5222_ = l_Lean_Name_eraseMacroScopes(v_val_5214_);
lean_inc_ref(v_env_5209_);
v___x_5223_ = l_Lean_Parser_isParserCategory(v_env_5209_, v___x_5222_);
if (v___x_5223_ == 0)
{
lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; uint8_t v___x_5227_; 
lean_inc_ref_n(v_env_5209_, 2);
v___x_5224_ = l_Lean_ResolveName_resolveGlobalName(v_env_5209_, v_opts_5210_, v_currNamespace_5211_, v_openDecls_5212_, v_val_5214_);
v___x_5225_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0));
v___x_5226_ = l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(v_env_5209_, v___x_5224_, v___x_5225_);
v___x_5227_ = l_List_isEmpty___redArg(v___x_5226_);
if (v___x_5227_ == 0)
{
lean_dec(v___x_5222_);
lean_del_object(v___x_5220_);
lean_dec_ref(v_env_5209_);
return v___x_5226_;
}
else
{
lean_object* v___x_5228_; lean_object* v_asyncMode_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; 
lean_dec(v___x_5226_);
v___x_5228_ = l_Lean_Parser_aliasExtension;
v_asyncMode_5229_ = lean_ctor_get(v___x_5228_, 2);
v___x_5230_ = lean_box(1);
v___x_5231_ = lean_box(0);
v___x_5232_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5230_, v___x_5228_, v_env_5209_, v_asyncMode_5229_, v___x_5231_);
v___x_5233_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5232_, v___x_5222_);
lean_dec(v___x_5222_);
lean_dec(v___x_5232_);
if (lean_obj_tag(v___x_5233_) == 1)
{
lean_object* v_val_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5245_; 
v_val_5234_ = lean_ctor_get(v___x_5233_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5236_ = v___x_5233_;
v_isShared_5237_ = v_isSharedCheck_5245_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_val_5234_);
lean_dec(v___x_5233_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5245_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5239_; 
if (v_isShared_5237_ == 0)
{
lean_ctor_set_tag(v___x_5236_, 2);
v___x_5239_ = v___x_5236_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_val_5234_);
v___x_5239_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
lean_object* v___x_5240_; lean_object* v___x_5242_; 
v___x_5240_ = lean_box(0);
if (v_isShared_5221_ == 0)
{
lean_ctor_set_tag(v___x_5220_, 1);
lean_ctor_set(v___x_5220_, 1, v___x_5240_);
lean_ctor_set(v___x_5220_, 0, v___x_5239_);
v___x_5242_ = v___x_5220_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v___x_5239_);
lean_ctor_set(v_reuseFailAlloc_5243_, 1, v___x_5240_);
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
else
{
lean_object* v___x_5246_; 
lean_dec(v___x_5233_);
lean_del_object(v___x_5220_);
v___x_5246_ = lean_box(0);
return v___x_5246_;
}
}
}
else
{
lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5250_; 
lean_dec(v_val_5214_);
lean_dec(v_openDecls_5212_);
lean_dec(v_currNamespace_5211_);
lean_dec_ref(v_env_5209_);
v___x_5247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5247_, 0, v___x_5222_);
v___x_5248_ = lean_box(0);
if (v_isShared_5221_ == 0)
{
lean_ctor_set_tag(v___x_5220_, 1);
lean_ctor_set(v___x_5220_, 1, v___x_5248_);
lean_ctor_set(v___x_5220_, 0, v___x_5247_);
v___x_5250_ = v___x_5220_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v___x_5247_);
lean_ctor_set(v_reuseFailAlloc_5251_, 1, v___x_5248_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
return v___x_5250_;
}
}
}
else
{
lean_object* v_val_5252_; 
lean_del_object(v___x_5220_);
lean_dec(v_val_5214_);
lean_dec(v_openDecls_5212_);
lean_dec(v_currNamespace_5211_);
lean_dec_ref(v_env_5209_);
v_val_5252_ = lean_ctor_get(v_fst_5218_, 0);
lean_inc(v_val_5252_);
lean_dec_ref_known(v_fst_5218_, 1);
return v_val_5252_;
}
}
}
else
{
lean_object* v___x_5255_; 
lean_dec(v_ident_5213_);
lean_dec(v_openDecls_5212_);
lean_dec(v_currNamespace_5211_);
lean_dec_ref(v_env_5209_);
v___x_5255_ = lean_box(0);
return v___x_5255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object* v_env_5256_, lean_object* v_opts_5257_, lean_object* v_currNamespace_5258_, lean_object* v_openDecls_5259_, lean_object* v_ident_5260_){
_start:
{
lean_object* v_res_5261_; 
v_res_5261_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5256_, v_opts_5257_, v_currNamespace_5258_, v_openDecls_5259_, v_ident_5260_);
lean_dec_ref(v_opts_5257_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object* v_env_5262_, lean_object* v_as_5263_, lean_object* v_as_x27_5264_, lean_object* v_b_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v___x_5267_; 
v___x_5267_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5262_, v_as_x27_5264_, v_b_5265_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object* v_env_5268_, lean_object* v_as_5269_, lean_object* v_as_x27_5270_, lean_object* v_b_5271_, lean_object* v_a_5272_){
_start:
{
lean_object* v_res_5273_; 
v_res_5273_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(v_env_5268_, v_as_5269_, v_as_x27_5270_, v_b_5271_, v_a_5272_);
lean_dec_ref(v_b_5271_);
lean_dec(v_as_x27_5270_);
lean_dec(v_as_5269_);
return v_res_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object* v_ctx_5274_, lean_object* v_id_5275_, uint8_t v_unsetExporting_5276_){
_start:
{
lean_object* v___y_5278_; 
if (v_unsetExporting_5276_ == 0)
{
lean_object* v_toParserModuleContext_5284_; lean_object* v_env_5285_; 
v_toParserModuleContext_5284_ = lean_ctor_get(v_ctx_5274_, 1);
v_env_5285_ = lean_ctor_get(v_toParserModuleContext_5284_, 0);
lean_inc_ref(v_env_5285_);
v___y_5278_ = v_env_5285_;
goto v___jp_5277_;
}
else
{
lean_object* v_toParserModuleContext_5286_; lean_object* v_env_5287_; uint8_t v___x_5288_; lean_object* v___x_5289_; 
v_toParserModuleContext_5286_ = lean_ctor_get(v_ctx_5274_, 1);
v_env_5287_ = lean_ctor_get(v_toParserModuleContext_5286_, 0);
v___x_5288_ = 0;
lean_inc_ref(v_env_5287_);
v___x_5289_ = l_Lean_Environment_setExporting(v_env_5287_, v___x_5288_);
v___y_5278_ = v___x_5289_;
goto v___jp_5277_;
}
v___jp_5277_:
{
lean_object* v_toParserModuleContext_5279_; lean_object* v_options_5280_; lean_object* v_currNamespace_5281_; lean_object* v_openDecls_5282_; lean_object* v___x_5283_; 
v_toParserModuleContext_5279_ = lean_ctor_get(v_ctx_5274_, 1);
lean_inc_ref(v_toParserModuleContext_5279_);
lean_dec_ref(v_ctx_5274_);
v_options_5280_ = lean_ctor_get(v_toParserModuleContext_5279_, 1);
lean_inc_ref(v_options_5280_);
v_currNamespace_5281_ = lean_ctor_get(v_toParserModuleContext_5279_, 2);
lean_inc(v_currNamespace_5281_);
v_openDecls_5282_ = lean_ctor_get(v_toParserModuleContext_5279_, 3);
lean_inc(v_openDecls_5282_);
lean_dec_ref(v_toParserModuleContext_5279_);
v___x_5283_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v___y_5278_, v_options_5280_, v_currNamespace_5281_, v_openDecls_5282_, v_id_5275_);
lean_dec_ref(v_options_5280_);
return v___x_5283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object* v_ctx_5290_, lean_object* v_id_5291_, lean_object* v_unsetExporting_5292_){
_start:
{
uint8_t v_unsetExporting_boxed_5293_; lean_object* v_res_5294_; 
v_unsetExporting_boxed_5293_ = lean_unbox(v_unsetExporting_5292_);
v_res_5294_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5290_, v_id_5291_, v_unsetExporting_boxed_5293_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object* v_id_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_){
_start:
{
lean_object* v___x_5299_; lean_object* v_toCold_5300_; lean_object* v_env_5301_; lean_object* v_options_5302_; lean_object* v_currNamespace_5303_; lean_object* v_openDecls_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; 
v___x_5299_ = lean_st_ref_get(v_a_5297_);
v_toCold_5300_ = lean_ctor_get(v_a_5296_, 0);
v_env_5301_ = lean_ctor_get(v___x_5299_, 0);
lean_inc_ref(v_env_5301_);
lean_dec(v___x_5299_);
v_options_5302_ = lean_ctor_get(v_toCold_5300_, 2);
v_currNamespace_5303_ = lean_ctor_get(v_toCold_5300_, 4);
v_openDecls_5304_ = lean_ctor_get(v_toCold_5300_, 5);
lean_inc(v_openDecls_5304_);
lean_inc(v_currNamespace_5303_);
v___x_5305_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5301_, v_options_5302_, v_currNamespace_5303_, v_openDecls_5304_, v_id_5295_);
v___x_5306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5305_);
return v___x_5306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object* v_id_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_){
_start:
{
lean_object* v_res_5311_; 
v_res_5311_ = l_Lean_Parser_resolveParserName(v_id_5307_, v_a_5308_, v_a_5309_);
lean_dec(v_a_5309_);
lean_dec_ref(v_a_5308_);
return v_res_5311_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object* v_x_5312_, lean_object* v_x_5313_){
_start:
{
if (lean_obj_tag(v_x_5312_) == 0)
{
if (lean_obj_tag(v_x_5313_) == 0)
{
uint8_t v___x_5314_; 
v___x_5314_ = 1;
return v___x_5314_;
}
else
{
uint8_t v___x_5315_; 
v___x_5315_ = 0;
return v___x_5315_;
}
}
else
{
if (lean_obj_tag(v_x_5313_) == 0)
{
uint8_t v___x_5316_; 
v___x_5316_ = 0;
return v___x_5316_;
}
else
{
lean_object* v_val_5317_; lean_object* v_val_5318_; uint8_t v___x_5319_; 
v_val_5317_ = lean_ctor_get(v_x_5312_, 0);
v_val_5318_ = lean_ctor_get(v_x_5313_, 0);
v___x_5319_ = l_Lean_Parser_instBEqError_beq(v_val_5317_, v_val_5318_);
return v___x_5319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object* v_x_5320_, lean_object* v_x_5321_){
_start:
{
uint8_t v_res_5322_; lean_object* v_r_5323_; 
v_res_5322_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5320_, v_x_5321_);
lean_dec(v_x_5321_);
lean_dec(v_x_5320_);
v_r_5323_ = lean_box(v_res_5322_);
return v_r_5323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t v___x_5324_, lean_object* v_ctx_5325_){
_start:
{
lean_object* v_toParserModuleContext_5326_; lean_object* v_toInputContext_5327_; lean_object* v_toCacheableParserContext_5328_; lean_object* v_tokens_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5354_; 
v_toParserModuleContext_5326_ = lean_ctor_get(v_ctx_5325_, 1);
v_toInputContext_5327_ = lean_ctor_get(v_ctx_5325_, 0);
v_toCacheableParserContext_5328_ = lean_ctor_get(v_ctx_5325_, 2);
v_tokens_5329_ = lean_ctor_get(v_ctx_5325_, 3);
v_isSharedCheck_5354_ = !lean_is_exclusive(v_ctx_5325_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5331_ = v_ctx_5325_;
v_isShared_5332_ = v_isSharedCheck_5354_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_tokens_5329_);
lean_inc(v_toCacheableParserContext_5328_);
lean_inc(v_toParserModuleContext_5326_);
lean_inc(v_toInputContext_5327_);
lean_dec(v_ctx_5325_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5354_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v_env_5333_; lean_object* v_options_5334_; lean_object* v_currNamespace_5335_; lean_object* v_openDecls_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5353_; 
v_env_5333_ = lean_ctor_get(v_toParserModuleContext_5326_, 0);
v_options_5334_ = lean_ctor_get(v_toParserModuleContext_5326_, 1);
v_currNamespace_5335_ = lean_ctor_get(v_toParserModuleContext_5326_, 2);
v_openDecls_5336_ = lean_ctor_get(v_toParserModuleContext_5326_, 3);
v_isSharedCheck_5353_ = !lean_is_exclusive(v_toParserModuleContext_5326_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5338_ = v_toParserModuleContext_5326_;
v_isShared_5339_ = v_isSharedCheck_5353_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_openDecls_5336_);
lean_inc(v_currNamespace_5335_);
lean_inc(v_options_5334_);
lean_inc(v_env_5333_);
lean_dec(v_toParserModuleContext_5326_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5353_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5340_; uint8_t v___y_5342_; lean_object* v___x_5350_; uint8_t v___x_5351_; 
v___x_5340_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_5350_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_5351_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_5334_, v___x_5350_);
if (v___x_5351_ == 0)
{
uint8_t v___x_5352_; 
v___x_5352_ = 1;
v___y_5342_ = v___x_5352_;
goto v___jp_5341_;
}
else
{
v___y_5342_ = v___x_5324_;
goto v___jp_5341_;
}
v___jp_5341_:
{
lean_object* v___x_5343_; lean_object* v___x_5345_; 
v___x_5343_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_5334_, v___x_5340_, v___y_5342_);
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 1, v___x_5343_);
v___x_5345_ = v___x_5338_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_env_5333_);
lean_ctor_set(v_reuseFailAlloc_5349_, 1, v___x_5343_);
lean_ctor_set(v_reuseFailAlloc_5349_, 2, v_currNamespace_5335_);
lean_ctor_set(v_reuseFailAlloc_5349_, 3, v_openDecls_5336_);
v___x_5345_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
lean_object* v___x_5347_; 
if (v_isShared_5332_ == 0)
{
lean_ctor_set(v___x_5331_, 1, v___x_5345_);
v___x_5347_ = v___x_5331_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_toInputContext_5327_);
lean_ctor_set(v_reuseFailAlloc_5348_, 1, v___x_5345_);
lean_ctor_set(v_reuseFailAlloc_5348_, 2, v_toCacheableParserContext_5328_);
lean_ctor_set(v_reuseFailAlloc_5348_, 3, v_tokens_5329_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object* v___x_5355_, lean_object* v_ctx_5356_){
_start:
{
uint8_t v___x_1069__boxed_5357_; lean_object* v_res_5358_; 
v___x_1069__boxed_5357_ = lean_unbox(v___x_5355_);
v_res_5358_ = l_Lean_Parser_parserOfStackFn___lam__0(v___x_1069__boxed_5357_, v_ctx_5356_);
return v_res_5358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* v_offset_5366_, lean_object* v_ctx_5367_, lean_object* v_s_5368_){
_start:
{
lean_object* v_stxStack_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; uint8_t v___x_5373_; 
v_stxStack_5369_ = lean_ctor_get(v_s_5368_, 0);
v___x_5370_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5369_);
v___x_5371_ = lean_unsigned_to_nat(1u);
v___x_5372_ = lean_nat_add(v_offset_5366_, v___x_5371_);
v___x_5373_ = lean_nat_dec_lt(v___x_5370_, v___x_5372_);
lean_dec(v___x_5372_);
if (v___x_5373_ == 0)
{
lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; 
v___x_5374_ = lean_nat_sub(v___x_5370_, v_offset_5366_);
lean_dec(v___x_5370_);
v___x_5375_ = lean_nat_sub(v___x_5374_, v___x_5371_);
lean_dec(v___x_5374_);
v___x_5376_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5369_, v___x_5375_);
lean_dec(v___x_5375_);
if (lean_obj_tag(v___x_5376_) == 3)
{
uint8_t v___x_5388_; lean_object* v___x_5389_; 
v___x_5388_ = 1;
lean_inc_ref(v___x_5376_);
lean_inc_ref(v_ctx_5367_);
v___x_5389_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5367_, v___x_5376_, v___x_5388_);
if (lean_obj_tag(v___x_5389_) == 0)
{
lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; 
lean_dec_ref(v_ctx_5367_);
v___x_5390_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__1));
v___x_5391_ = lean_box(0);
v___x_5392_ = l_Lean_Syntax_formatStx(v___x_5376_, v___x_5391_, v___x_5373_);
v___x_5393_ = l_Std_Format_defWidth;
v___x_5394_ = lean_unsigned_to_nat(0u);
v___x_5395_ = l_Std_Format_pretty(v___x_5392_, v___x_5393_, v___x_5394_, v___x_5394_);
v___x_5396_ = lean_string_append(v___x_5390_, v___x_5395_);
lean_dec_ref(v___x_5395_);
v___x_5397_ = lean_box(0);
v___x_5398_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5368_, v___x_5396_, v___x_5397_, v___x_5388_);
return v___x_5398_;
}
else
{
lean_object* v_head_5399_; lean_object* v_tail_5400_; lean_object* v_iniSz_5401_; lean_object* v_s_5403_; 
v_head_5399_ = lean_ctor_get(v___x_5389_, 0);
lean_inc(v_head_5399_);
v_tail_5400_ = lean_ctor_get(v___x_5389_, 1);
lean_inc(v_tail_5400_);
lean_dec_ref_known(v___x_5389_, 2);
v_iniSz_5401_ = l_Lean_Parser_ParserState_stackSize(v_s_5368_);
switch(lean_obj_tag(v_head_5399_))
{
case 0:
{
if (lean_obj_tag(v_tail_5400_) == 0)
{
lean_object* v_cat_5413_; lean_object* v___x_5414_; 
lean_dec_ref_known(v___x_5376_, 4);
v_cat_5413_ = lean_ctor_get(v_head_5399_, 0);
lean_inc(v_cat_5413_);
lean_dec_ref_known(v_head_5399_, 1);
v___x_5414_ = l_Lean_Parser_categoryParserFn(v_cat_5413_, v_ctx_5367_, v_s_5368_);
v_s_5403_ = v___x_5414_;
goto v___jp_5402_;
}
else
{
lean_dec_ref_known(v_tail_5400_, 2);
lean_dec_ref_known(v_head_5399_, 1);
lean_dec(v_iniSz_5401_);
lean_dec_ref(v_ctx_5367_);
goto v___jp_5377_;
}
}
case 1:
{
if (lean_obj_tag(v_tail_5400_) == 0)
{
lean_object* v_decl_5415_; lean_object* v___x_5416_; lean_object* v___f_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; 
lean_dec_ref_known(v___x_5376_, 4);
v_decl_5415_ = lean_ctor_get(v_head_5399_, 0);
lean_inc(v_decl_5415_);
lean_dec_ref_known(v_head_5399_, 1);
v___x_5416_ = lean_box(v___x_5373_);
v___f_5417_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5417_, 0, v___x_5416_);
v___x_5418_ = lean_box(0);
v___x_5419_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_5419_, 0, v_decl_5415_);
lean_closure_set(v___x_5419_, 1, v___x_5418_);
v___x_5420_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5417_, v___x_5419_, v_ctx_5367_, v_s_5368_);
v_s_5403_ = v___x_5420_;
goto v___jp_5402_;
}
else
{
lean_dec_ref_known(v_tail_5400_, 2);
lean_dec_ref_known(v_head_5399_, 1);
lean_dec(v_iniSz_5401_);
lean_dec_ref(v_ctx_5367_);
goto v___jp_5377_;
}
}
default: 
{
if (lean_obj_tag(v_tail_5400_) == 0)
{
lean_object* v_p_5421_; 
v_p_5421_ = lean_ctor_get(v_head_5399_, 0);
lean_inc_ref(v_p_5421_);
lean_dec_ref_known(v_head_5399_, 1);
if (lean_obj_tag(v_p_5421_) == 0)
{
lean_object* v_p_5422_; lean_object* v_fn_5423_; lean_object* v___x_5424_; 
lean_dec_ref_known(v___x_5376_, 4);
v_p_5422_ = lean_ctor_get(v_p_5421_, 0);
lean_inc(v_p_5422_);
lean_dec_ref_known(v_p_5421_, 1);
v_fn_5423_ = lean_ctor_get(v_p_5422_, 1);
lean_inc_ref(v_fn_5423_);
lean_dec(v_p_5422_);
v___x_5424_ = lean_apply_2(v_fn_5423_, v_ctx_5367_, v_s_5368_);
v_s_5403_ = v___x_5424_;
goto v___jp_5402_;
}
else
{
lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; 
lean_dec_ref(v_p_5421_);
lean_dec(v_iniSz_5401_);
lean_dec_ref(v_ctx_5367_);
v___x_5425_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__3));
v___x_5426_ = lean_box(0);
v___x_5427_ = l_Lean_Syntax_formatStx(v___x_5376_, v___x_5426_, v___x_5373_);
v___x_5428_ = l_Std_Format_defWidth;
v___x_5429_ = lean_unsigned_to_nat(0u);
v___x_5430_ = l_Std_Format_pretty(v___x_5427_, v___x_5428_, v___x_5429_, v___x_5429_);
v___x_5431_ = lean_string_append(v___x_5425_, v___x_5430_);
lean_dec_ref(v___x_5430_);
v___x_5432_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__4));
v___x_5433_ = lean_string_append(v___x_5431_, v___x_5432_);
v___x_5434_ = lean_box(0);
v___x_5435_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5368_, v___x_5433_, v___x_5434_, v___x_5388_);
return v___x_5435_;
}
}
else
{
lean_dec_ref_known(v_tail_5400_, 2);
lean_dec_ref_known(v_head_5399_, 1);
lean_dec(v_iniSz_5401_);
lean_dec_ref(v_ctx_5367_);
goto v___jp_5377_;
}
}
}
v___jp_5402_:
{
lean_object* v_errorMsg_5404_; lean_object* v___x_5405_; uint8_t v___x_5406_; 
v_errorMsg_5404_ = lean_ctor_get(v_s_5403_, 4);
v___x_5405_ = lean_box(0);
v___x_5406_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_errorMsg_5404_, v___x_5405_);
if (v___x_5406_ == 0)
{
lean_dec(v_iniSz_5401_);
return v_s_5403_;
}
else
{
lean_object* v___x_5407_; lean_object* v___x_5408_; uint8_t v___x_5409_; 
v___x_5407_ = l_Lean_Parser_ParserState_stackSize(v_s_5403_);
v___x_5408_ = lean_nat_add(v_iniSz_5401_, v___x_5371_);
lean_dec(v_iniSz_5401_);
v___x_5409_ = lean_nat_dec_eq(v___x_5407_, v___x_5408_);
lean_dec(v___x_5408_);
lean_dec(v___x_5407_);
if (v___x_5409_ == 0)
{
lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; 
v___x_5410_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__2));
v___x_5411_ = lean_box(0);
v___x_5412_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5403_, v___x_5410_, v___x_5411_, v___x_5406_);
return v___x_5412_;
}
else
{
return v_s_5403_;
}
}
}
}
}
else
{
lean_object* v___x_5436_; lean_object* v___x_5437_; uint8_t v___x_5438_; lean_object* v___x_5439_; 
lean_dec(v___x_5376_);
lean_dec_ref(v_ctx_5367_);
v___x_5436_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__5));
v___x_5437_ = lean_box(0);
v___x_5438_ = 1;
v___x_5439_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5368_, v___x_5436_, v___x_5437_, v___x_5438_);
return v___x_5439_;
}
v___jp_5377_:
{
lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; uint8_t v___x_5386_; lean_object* v___x_5387_; 
v___x_5378_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__0));
v___x_5379_ = lean_box(0);
v___x_5380_ = l_Lean_Syntax_formatStx(v___x_5376_, v___x_5379_, v___x_5373_);
v___x_5381_ = l_Std_Format_defWidth;
v___x_5382_ = lean_unsigned_to_nat(0u);
v___x_5383_ = l_Std_Format_pretty(v___x_5380_, v___x_5381_, v___x_5382_, v___x_5382_);
v___x_5384_ = lean_string_append(v___x_5378_, v___x_5383_);
lean_dec_ref(v___x_5383_);
v___x_5385_ = lean_box(0);
v___x_5386_ = 1;
v___x_5387_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5368_, v___x_5384_, v___x_5385_, v___x_5386_);
return v___x_5387_;
}
}
else
{
lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; 
lean_dec(v___x_5370_);
lean_dec_ref(v_ctx_5367_);
v___x_5440_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__6));
v___x_5441_ = lean_box(0);
v___x_5442_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5368_, v___x_5440_, v___x_5441_, v___x_5373_);
return v___x_5442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* v_offset_5443_, lean_object* v_ctx_5444_, lean_object* v_s_5445_){
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l_Lean_Parser_parserOfStackFn(v_offset_5443_, v_ctx_5444_, v_s_5445_);
lean_dec(v_offset_5443_);
return v_res_5446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object* v_prec_5447_, lean_object* v_x_5448_){
_start:
{
lean_object* v_quotDepth_5449_; uint8_t v_suppressInsideQuot_5450_; lean_object* v_savedPos_x3f_5451_; lean_object* v_forbiddenTks_5452_; lean_object* v___x_5454_; uint8_t v_isShared_5455_; uint8_t v_isSharedCheck_5459_; 
v_quotDepth_5449_ = lean_ctor_get(v_x_5448_, 1);
v_suppressInsideQuot_5450_ = lean_ctor_get_uint8(v_x_5448_, sizeof(void*)*4);
v_savedPos_x3f_5451_ = lean_ctor_get(v_x_5448_, 2);
v_forbiddenTks_5452_ = lean_ctor_get(v_x_5448_, 3);
v_isSharedCheck_5459_ = !lean_is_exclusive(v_x_5448_);
if (v_isSharedCheck_5459_ == 0)
{
lean_object* v_unused_5460_; 
v_unused_5460_ = lean_ctor_get(v_x_5448_, 0);
lean_dec(v_unused_5460_);
v___x_5454_ = v_x_5448_;
v_isShared_5455_ = v_isSharedCheck_5459_;
goto v_resetjp_5453_;
}
else
{
lean_inc(v_forbiddenTks_5452_);
lean_inc(v_savedPos_x3f_5451_);
lean_inc(v_quotDepth_5449_);
lean_dec(v_x_5448_);
v___x_5454_ = lean_box(0);
v_isShared_5455_ = v_isSharedCheck_5459_;
goto v_resetjp_5453_;
}
v_resetjp_5453_:
{
lean_object* v___x_5457_; 
if (v_isShared_5455_ == 0)
{
lean_ctor_set(v___x_5454_, 0, v_prec_5447_);
v___x_5457_ = v___x_5454_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v_prec_5447_);
lean_ctor_set(v_reuseFailAlloc_5458_, 1, v_quotDepth_5449_);
lean_ctor_set(v_reuseFailAlloc_5458_, 2, v_savedPos_x3f_5451_);
lean_ctor_set(v_reuseFailAlloc_5458_, 3, v_forbiddenTks_5452_);
lean_ctor_set_uint8(v_reuseFailAlloc_5458_, sizeof(void*)*4, v_suppressInsideQuot_5450_);
v___x_5457_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
return v___x_5457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object* v___y_5461_){
_start:
{
lean_inc(v___y_5461_);
return v___y_5461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object* v___y_5462_){
_start:
{
lean_object* v_res_5463_; 
v_res_5463_ = l_Lean_Parser_parserOfStack___lam__1(v___y_5462_);
lean_dec(v___y_5462_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object* v___y_5464_){
_start:
{
lean_inc_ref(v___y_5464_);
return v___y_5464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object* v___y_5465_){
_start:
{
lean_object* v_res_5466_; 
v_res_5466_ = l_Lean_Parser_parserOfStack___lam__2(v___y_5465_);
lean_dec_ref(v___y_5465_);
return v_res_5466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* v_offset_5473_, lean_object* v_prec_5474_){
_start:
{
lean_object* v___f_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; 
v___f_5475_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___lam__0), 2, 1);
lean_closure_set(v___f_5475_, 0, v_prec_5474_);
v___x_5476_ = ((lean_object*)(l_Lean_Parser_parserOfStack___closed__2));
v___x_5477_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___boxed), 3, 1);
lean_closure_set(v___x_5477_, 0, v_offset_5473_);
v___x_5478_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5478_, 0, v___f_5475_);
lean_closure_set(v___x_5478_, 1, v___x_5477_);
v___x_5479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5479_, 0, v___x_5476_);
lean_ctor_set(v___x_5479_, 1, v___x_5478_);
return v___x_5479_;
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
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_();
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
