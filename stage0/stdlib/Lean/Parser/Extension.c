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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Data_Trie_empty___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
static const lean_closure_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__value)} };
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
v___x_1_ = l_Lean_Data_Trie_empty___redArg();
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
v___x_8_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_);
v___x_84_ = lean_st_mk_ref(v___x_83_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2____boxed(lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(lean_object* v_catName_90_){
_start:
{
lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_91_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0));
v___x_92_ = 1;
v___x_93_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_90_, v___x_92_);
v___x_94_ = lean_string_append(v___x_91_, v___x_93_);
lean_dec_ref(v___x_93_);
v___x_95_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1));
v___x_96_ = lean_string_append(v___x_94_, v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined(lean_object* v_00_u03b1_98_, lean_object* v_catName_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_101_, lean_object* v_x_102_, lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
lean_object* v_ks_105_; lean_object* v_vs_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_130_; 
v_ks_105_ = lean_ctor_get(v_x_101_, 0);
v_vs_106_ = lean_ctor_get(v_x_101_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_x_101_);
if (v_isSharedCheck_130_ == 0)
{
v___x_108_ = v_x_101_;
v_isShared_109_ = v_isSharedCheck_130_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_vs_106_);
lean_inc(v_ks_105_);
lean_dec(v_x_101_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_130_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_array_get_size(v_ks_105_);
v___x_111_ = lean_nat_dec_lt(v_x_102_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
lean_dec(v_x_102_);
v___x_112_ = lean_array_push(v_ks_105_, v_x_103_);
v___x_113_ = lean_array_push(v_vs_106_, v_x_104_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v___x_113_);
lean_ctor_set(v___x_108_, 0, v___x_112_);
v___x_115_ = v___x_108_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
else
{
lean_object* v_k_x27_117_; uint8_t v___x_118_; 
v_k_x27_117_ = lean_array_fget_borrowed(v_ks_105_, v_x_102_);
v___x_118_ = lean_name_eq(v_x_103_, v_k_x27_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_120_; 
if (v_isShared_109_ == 0)
{
v___x_120_ = v___x_108_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_ks_105_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_vs_106_);
v___x_120_ = v_reuseFailAlloc_124_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_add(v_x_102_, v___x_121_);
lean_dec(v_x_102_);
v_x_101_ = v___x_120_;
v_x_102_ = v___x_122_;
goto _start;
}
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_125_ = lean_array_fset(v_ks_105_, v_x_102_, v_x_103_);
v___x_126_ = lean_array_fset(v_vs_106_, v_x_102_, v_x_104_);
lean_dec(v_x_102_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v___x_126_);
lean_ctor_set(v___x_108_, 0, v___x_125_);
v___x_128_ = v___x_108_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(lean_object* v_n_131_, lean_object* v_k_132_, lean_object* v_v_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_n_131_, v___x_134_, v_k_132_, v_v_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(lean_object* v_x_137_, size_t v_x_138_, size_t v_x_139_, lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v_es_142_; size_t v___x_143_; size_t v___x_144_; lean_object* v_j_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v_es_142_ = lean_ctor_get(v_x_137_, 0);
v___x_143_ = ((size_t)31ULL);
v___x_144_ = lean_usize_land(v_x_138_, v___x_143_);
v_j_145_ = lean_usize_to_nat(v___x_144_);
v___x_146_ = lean_array_get_size(v_es_142_);
v___x_147_ = lean_nat_dec_lt(v_j_145_, v___x_146_);
if (v___x_147_ == 0)
{
lean_dec(v_j_145_);
lean_dec(v_x_141_);
lean_dec(v_x_140_);
return v_x_137_;
}
else
{
lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_186_; 
lean_inc_ref(v_es_142_);
v_isSharedCheck_186_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_186_ == 0)
{
lean_object* v_unused_187_; 
v_unused_187_ = lean_ctor_get(v_x_137_, 0);
lean_dec(v_unused_187_);
v___x_149_ = v_x_137_;
v_isShared_150_ = v_isSharedCheck_186_;
goto v_resetjp_148_;
}
else
{
lean_dec(v_x_137_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_186_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v_v_151_; lean_object* v___x_152_; lean_object* v_xs_x27_153_; lean_object* v___y_155_; 
v_v_151_ = lean_array_fget(v_es_142_, v_j_145_);
v___x_152_ = lean_box(0);
v_xs_x27_153_ = lean_array_fset(v_es_142_, v_j_145_, v___x_152_);
switch(lean_obj_tag(v_v_151_))
{
case 0:
{
lean_object* v_key_160_; lean_object* v_val_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_171_; 
v_key_160_ = lean_ctor_get(v_v_151_, 0);
v_val_161_ = lean_ctor_get(v_v_151_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_v_151_);
if (v_isSharedCheck_171_ == 0)
{
v___x_163_ = v_v_151_;
v_isShared_164_ = v_isSharedCheck_171_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_val_161_);
lean_inc(v_key_160_);
lean_dec(v_v_151_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_171_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
uint8_t v___x_165_; 
v___x_165_ = lean_name_eq(v_x_140_, v_key_160_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_del_object(v___x_163_);
v___x_166_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_160_, v_val_161_, v_x_140_, v_x_141_);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
v___y_155_ = v___x_167_;
goto v___jp_154_;
}
else
{
lean_object* v___x_169_; 
lean_dec(v_val_161_);
lean_dec(v_key_160_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v_x_141_);
lean_ctor_set(v___x_163_, 0, v_x_140_);
v___x_169_ = v___x_163_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_x_140_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_x_141_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
v___y_155_ = v___x_169_;
goto v___jp_154_;
}
}
}
}
case 1:
{
lean_object* v_node_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_184_; 
v_node_172_ = lean_ctor_get(v_v_151_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v_v_151_);
if (v_isSharedCheck_184_ == 0)
{
v___x_174_ = v_v_151_;
v_isShared_175_ = v_isSharedCheck_184_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_node_172_);
lean_dec(v_v_151_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_184_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_176_ = ((size_t)5ULL);
v___x_177_ = lean_usize_shift_right(v_x_138_, v___x_176_);
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_x_139_, v___x_178_);
v___x_180_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_node_172_, v___x_177_, v___x_179_, v_x_140_, v_x_141_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_180_);
v___x_182_ = v___x_174_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
v___y_155_ = v___x_182_;
goto v___jp_154_;
}
}
}
default: 
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_x_140_);
lean_ctor_set(v___x_185_, 1, v_x_141_);
v___y_155_ = v___x_185_;
goto v___jp_154_;
}
}
v___jp_154_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_array_fset(v_xs_x27_153_, v_j_145_, v___y_155_);
lean_dec(v_j_145_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_156_);
v___x_158_ = v___x_149_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
else
{
lean_object* v_ks_188_; lean_object* v_vs_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_207_; 
v_ks_188_ = lean_ctor_get(v_x_137_, 0);
v_vs_189_ = lean_ctor_get(v_x_137_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_207_ == 0)
{
v___x_191_ = v_x_137_;
v_isShared_192_ = v_isSharedCheck_207_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_vs_189_);
lean_inc(v_ks_188_);
lean_dec(v_x_137_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_207_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_ks_188_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_vs_189_);
v___x_194_ = v_reuseFailAlloc_206_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v_newNode_195_; size_t v___x_196_; uint8_t v___x_197_; 
v_newNode_195_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v___x_194_, v_x_140_, v_x_141_);
v___x_196_ = ((size_t)7ULL);
v___x_197_ = lean_usize_dec_le(v___x_196_, v_x_139_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_198_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_195_);
v___x_199_ = lean_unsigned_to_nat(4u);
v___x_200_ = lean_nat_dec_lt(v___x_198_, v___x_199_);
lean_dec(v___x_198_);
if (v___x_200_ == 0)
{
lean_object* v_ks_201_; lean_object* v_vs_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_ks_201_ = lean_ctor_get(v_newNode_195_, 0);
lean_inc_ref(v_ks_201_);
v_vs_202_ = lean_ctor_get(v_newNode_195_, 1);
lean_inc_ref(v_vs_202_);
lean_dec_ref(v_newNode_195_);
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0);
v___x_205_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_x_139_, v_ks_201_, v_vs_202_, v___x_203_, v___x_204_);
lean_dec_ref(v_vs_202_);
lean_dec_ref(v_ks_201_);
return v___x_205_;
}
else
{
return v_newNode_195_;
}
}
else
{
return v_newNode_195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(size_t v_depth_208_, lean_object* v_keys_209_, lean_object* v_vals_210_, lean_object* v_i_211_, lean_object* v_entries_212_){
_start:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_array_get_size(v_keys_209_);
v___x_214_ = lean_nat_dec_lt(v_i_211_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec(v_i_211_);
return v_entries_212_;
}
else
{
lean_object* v_k_215_; lean_object* v_v_216_; uint64_t v___y_218_; 
v_k_215_ = lean_array_fget_borrowed(v_keys_209_, v_i_211_);
v_v_216_ = lean_array_fget_borrowed(v_vals_210_, v_i_211_);
if (lean_obj_tag(v_k_215_) == 0)
{
uint64_t v___x_229_; 
v___x_229_ = 1723ULL;
v___y_218_ = v___x_229_;
goto v___jp_217_;
}
else
{
uint64_t v_hash_230_; 
v_hash_230_ = lean_ctor_get_uint64(v_k_215_, sizeof(void*)*2);
v___y_218_ = v_hash_230_;
goto v___jp_217_;
}
v___jp_217_:
{
size_t v_h_219_; size_t v___x_220_; lean_object* v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; size_t v_h_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_h_219_ = lean_uint64_to_usize(v___y_218_);
v___x_220_ = ((size_t)5ULL);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_sub(v_depth_208_, v___x_222_);
v___x_224_ = lean_usize_mul(v___x_220_, v___x_223_);
v_h_225_ = lean_usize_shift_right(v_h_219_, v___x_224_);
v___x_226_ = lean_nat_add(v_i_211_, v___x_221_);
lean_dec(v_i_211_);
lean_inc(v_v_216_);
lean_inc(v_k_215_);
v___x_227_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_entries_212_, v_h_225_, v_depth_208_, v_k_215_, v_v_216_);
v_i_211_ = v___x_226_;
v_entries_212_ = v___x_227_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_231_, lean_object* v_keys_232_, lean_object* v_vals_233_, lean_object* v_i_234_, lean_object* v_entries_235_){
_start:
{
size_t v_depth_boxed_236_; lean_object* v_res_237_; 
v_depth_boxed_236_ = lean_unbox_usize(v_depth_231_);
lean_dec(v_depth_231_);
v_res_237_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_boxed_236_, v_keys_232_, v_vals_233_, v_i_234_, v_entries_235_);
lean_dec_ref(v_vals_233_);
lean_dec_ref(v_keys_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
size_t v_x_527__boxed_243_; size_t v_x_528__boxed_244_; lean_object* v_res_245_; 
v_x_527__boxed_243_ = lean_unbox_usize(v_x_239_);
lean_dec(v_x_239_);
v_x_528__boxed_244_ = lean_unbox_usize(v_x_240_);
lean_dec(v_x_240_);
v_res_245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_238_, v_x_527__boxed_243_, v_x_528__boxed_244_, v_x_241_, v_x_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
uint64_t v___y_250_; 
if (lean_obj_tag(v_x_247_) == 0)
{
uint64_t v___x_254_; 
v___x_254_ = 1723ULL;
v___y_250_ = v___x_254_;
goto v___jp_249_;
}
else
{
uint64_t v_hash_255_; 
v_hash_255_ = lean_ctor_get_uint64(v_x_247_, sizeof(void*)*2);
v___y_250_ = v_hash_255_;
goto v___jp_249_;
}
v___jp_249_:
{
size_t v___x_251_; size_t v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_uint64_to_usize(v___y_250_);
v___x_252_ = ((size_t)1ULL);
v___x_253_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_246_, v___x_251_, v___x_252_, v_x_247_, v_x_248_);
return v___x_253_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_256_, lean_object* v_i_257_, lean_object* v_k_258_){
_start:
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_array_get_size(v_keys_256_);
v___x_260_ = lean_nat_dec_lt(v_i_257_, v___x_259_);
if (v___x_260_ == 0)
{
lean_dec(v_i_257_);
return v___x_260_;
}
else
{
lean_object* v_k_x27_261_; uint8_t v___x_262_; 
v_k_x27_261_ = lean_array_fget_borrowed(v_keys_256_, v_i_257_);
v___x_262_ = lean_name_eq(v_k_258_, v_k_x27_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = lean_nat_add(v_i_257_, v___x_263_);
lean_dec(v_i_257_);
v_i_257_ = v___x_264_;
goto _start;
}
else
{
lean_dec(v_i_257_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_266_, lean_object* v_i_267_, lean_object* v_k_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_266_, v_i_267_, v_k_268_);
lean_dec(v_k_268_);
lean_dec_ref(v_keys_266_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(lean_object* v_x_271_, size_t v_x_272_, lean_object* v_x_273_){
_start:
{
if (lean_obj_tag(v_x_271_) == 0)
{
lean_object* v_es_274_; lean_object* v___x_275_; size_t v___x_276_; size_t v___x_277_; lean_object* v_j_278_; lean_object* v___x_279_; 
v_es_274_ = lean_ctor_get(v_x_271_, 0);
v___x_275_ = lean_box(2);
v___x_276_ = ((size_t)31ULL);
v___x_277_ = lean_usize_land(v_x_272_, v___x_276_);
v_j_278_ = lean_usize_to_nat(v___x_277_);
v___x_279_ = lean_array_get_borrowed(v___x_275_, v_es_274_, v_j_278_);
lean_dec(v_j_278_);
switch(lean_obj_tag(v___x_279_))
{
case 0:
{
lean_object* v_key_280_; uint8_t v___x_281_; 
v_key_280_ = lean_ctor_get(v___x_279_, 0);
v___x_281_ = lean_name_eq(v_x_273_, v_key_280_);
return v___x_281_;
}
case 1:
{
lean_object* v_node_282_; size_t v___x_283_; size_t v___x_284_; 
v_node_282_ = lean_ctor_get(v___x_279_, 0);
v___x_283_ = ((size_t)5ULL);
v___x_284_ = lean_usize_shift_right(v_x_272_, v___x_283_);
v_x_271_ = v_node_282_;
v_x_272_ = v___x_284_;
goto _start;
}
default: 
{
uint8_t v___x_286_; 
v___x_286_ = 0;
return v___x_286_;
}
}
}
else
{
lean_object* v_ks_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_ks_287_ = lean_ctor_get(v_x_271_, 0);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_ks_287_, v___x_288_, v_x_273_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
size_t v_x_711__boxed_293_; uint8_t v_res_294_; lean_object* v_r_295_; 
v_x_711__boxed_293_ = lean_unbox_usize(v_x_291_);
lean_dec(v_x_291_);
v_res_294_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_290_, v_x_711__boxed_293_, v_x_292_);
lean_dec(v_x_292_);
lean_dec_ref(v_x_290_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(lean_object* v_x_296_, lean_object* v_x_297_){
_start:
{
uint64_t v___y_299_; 
if (lean_obj_tag(v_x_297_) == 0)
{
uint64_t v___x_302_; 
v___x_302_ = 1723ULL;
v___y_299_ = v___x_302_;
goto v___jp_298_;
}
else
{
uint64_t v_hash_303_; 
v_hash_303_ = lean_ctor_get_uint64(v_x_297_, sizeof(void*)*2);
v___y_299_ = v_hash_303_;
goto v___jp_298_;
}
v___jp_298_:
{
size_t v___x_300_; uint8_t v___x_301_; 
v___x_300_ = lean_uint64_to_usize(v___y_299_);
v___x_301_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_296_, v___x_300_, v_x_297_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg___boxed(lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_304_, v_x_305_);
lean_dec(v_x_305_);
lean_dec_ref(v_x_304_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object* v_categories_308_, lean_object* v_catName_309_, lean_object* v_initial_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_308_, v_catName_309_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_308_, v_catName_309_, v_initial_310_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; 
lean_dec_ref(v_initial_310_);
lean_dec_ref(v_categories_308_);
v___x_314_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_309_);
return v___x_314_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(lean_object* v_00_u03b2_315_, lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_316_, v_x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___boxed(lean_object* v_00_u03b2_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(v_00_u03b2_319_, v_x_320_, v_x_321_);
lean_dec(v_x_321_);
lean_dec_ref(v_x_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1(lean_object* v_00_u03b2_324_, lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_x_325_, v_x_326_, v_x_327_);
return v___x_328_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(lean_object* v_00_u03b2_329_, lean_object* v_x_330_, size_t v_x_331_, lean_object* v_x_332_){
_start:
{
uint8_t v___x_333_; 
v___x_333_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_330_, v_x_331_, v_x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_334_, lean_object* v_x_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
size_t v_x_792__boxed_338_; uint8_t v_res_339_; lean_object* v_r_340_; 
v_x_792__boxed_338_ = lean_unbox_usize(v_x_336_);
lean_dec(v_x_336_);
v_res_339_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(v_00_u03b2_334_, v_x_335_, v_x_792__boxed_338_, v_x_337_);
lean_dec(v_x_337_);
lean_dec_ref(v_x_335_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(lean_object* v_00_u03b2_341_, lean_object* v_x_342_, size_t v_x_343_, size_t v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_342_, v_x_343_, v_x_344_, v_x_345_, v_x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_348_, lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
size_t v_x_803__boxed_354_; size_t v_x_804__boxed_355_; lean_object* v_res_356_; 
v_x_803__boxed_354_ = lean_unbox_usize(v_x_350_);
lean_dec(v_x_350_);
v_x_804__boxed_355_ = lean_unbox_usize(v_x_351_);
lean_dec(v_x_351_);
v_res_356_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(v_00_u03b2_348_, v_x_349_, v_x_803__boxed_354_, v_x_804__boxed_355_, v_x_352_, v_x_353_);
return v_res_356_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_357_, lean_object* v_keys_358_, lean_object* v_vals_359_, lean_object* v_heq_360_, lean_object* v_i_361_, lean_object* v_k_362_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_358_, v_i_361_, v_k_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_364_, lean_object* v_keys_365_, lean_object* v_vals_366_, lean_object* v_heq_367_, lean_object* v_i_368_, lean_object* v_k_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(v_00_u03b2_364_, v_keys_365_, v_vals_366_, v_heq_367_, v_i_368_, v_k_369_);
lean_dec(v_k_369_);
lean_dec_ref(v_vals_366_);
lean_dec_ref(v_keys_365_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_372_, lean_object* v_n_373_, lean_object* v_k_374_, lean_object* v_v_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v_n_373_, v_k_374_, v_v_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_377_, size_t v_depth_378_, lean_object* v_keys_379_, lean_object* v_vals_380_, lean_object* v_heq_381_, lean_object* v_i_382_, lean_object* v_entries_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_378_, v_keys_379_, v_vals_380_, v_i_382_, v_entries_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_385_, lean_object* v_depth_386_, lean_object* v_keys_387_, lean_object* v_vals_388_, lean_object* v_heq_389_, lean_object* v_i_390_, lean_object* v_entries_391_){
_start:
{
size_t v_depth_boxed_392_; lean_object* v_res_393_; 
v_depth_boxed_392_ = lean_unbox_usize(v_depth_386_);
lean_dec(v_depth_386_);
v_res_393_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(v_00_u03b2_385_, v_depth_boxed_392_, v_keys_387_, v_vals_388_, v_heq_389_, v_i_390_, v_entries_391_);
lean_dec_ref(v_vals_388_);
lean_dec_ref(v_keys_387_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_394_, lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_x_395_, v_x_396_, v_x_397_, v_x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(lean_object* v_e_400_){
_start:
{
if (lean_obj_tag(v_e_400_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_410_; 
v_a_402_ = lean_ctor_get(v_e_400_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v_e_400_);
if (v_isSharedCheck_410_ == 0)
{
v___x_404_ = v_e_400_;
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v_e_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_mk_io_user_error(v_a_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 1);
lean_ctor_set(v___x_404_, 0, v___x_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
v_a_411_ = lean_ctor_get(v_e_400_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v_e_400_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v_e_400_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v_e_400_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set_tag(v___x_413_, 0);
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg___boxed(lean_object* v_e_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(lean_object* v_00_u03b1_422_, lean_object* v_e_423_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___boxed(lean_object* v_00_u03b1_426_, lean_object* v_e_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(v_00_u03b1_426_, v_e_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object* v_catName_433_, lean_object* v_declName_434_, uint8_t v_behavior_435_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_437_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_438_ = lean_st_ref_get(v___x_437_);
v___x_439_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_440_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_441_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_441_, 0, v_declName_434_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
lean_ctor_set(v___x_441_, 2, v___x_440_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*3, v_behavior_435_);
v___x_442_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(v___x_438_, v_catName_433_, v___x_441_);
v___x_443_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_453_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_453_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_453_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_453_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_448_ = lean_box(0);
v___x_449_ = lean_st_ref_swap(v___x_437_, v_a_444_);
lean_dec(v___x_449_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_448_);
v___x_451_ = v___x_446_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_448_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
v_a_454_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_443_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_443_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object* v_catName_462_, lean_object* v_declName_463_, lean_object* v_behavior_464_, lean_object* v_a_465_){
_start:
{
uint8_t v_behavior_boxed_466_; lean_object* v_res_467_; 
v_behavior_boxed_466_ = lean_unbox(v_behavior_464_);
v_res_467_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_462_, v_declName_463_, v_behavior_boxed_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(lean_object* v_x_468_){
_start:
{
switch(lean_obj_tag(v_x_468_))
{
case 0:
{
lean_object* v___x_469_; 
v___x_469_ = lean_unsigned_to_nat(0u);
return v___x_469_;
}
case 1:
{
lean_object* v___x_470_; 
v___x_470_ = lean_unsigned_to_nat(1u);
return v___x_470_;
}
case 2:
{
lean_object* v___x_471_; 
v___x_471_ = lean_unsigned_to_nat(2u);
return v___x_471_;
}
default: 
{
lean_object* v___x_472_; 
v___x_472_ = lean_unsigned_to_nat(3u);
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___boxed(lean_object* v_x_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(v_x_473_);
lean_dec_ref(v_x_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(lean_object* v_t_475_, lean_object* v_k_476_){
_start:
{
switch(lean_obj_tag(v_t_475_))
{
case 0:
{
lean_object* v_val_477_; lean_object* v___x_478_; 
v_val_477_ = lean_ctor_get(v_t_475_, 0);
lean_inc_ref(v_val_477_);
lean_dec_ref_known(v_t_475_, 1);
v___x_478_ = lean_apply_1(v_k_476_, v_val_477_);
return v___x_478_;
}
case 1:
{
lean_object* v_val_479_; lean_object* v___x_480_; 
v_val_479_ = lean_ctor_get(v_t_475_, 0);
lean_inc(v_val_479_);
lean_dec_ref_known(v_t_475_, 1);
v___x_480_ = lean_apply_1(v_k_476_, v_val_479_);
return v___x_480_;
}
case 2:
{
lean_object* v_catName_481_; lean_object* v_declName_482_; uint8_t v_behavior_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_catName_481_ = lean_ctor_get(v_t_475_, 0);
lean_inc(v_catName_481_);
v_declName_482_ = lean_ctor_get(v_t_475_, 1);
lean_inc(v_declName_482_);
v_behavior_483_ = lean_ctor_get_uint8(v_t_475_, sizeof(void*)*2);
lean_dec_ref_known(v_t_475_, 2);
v___x_484_ = lean_box(v_behavior_483_);
v___x_485_ = lean_apply_3(v_k_476_, v_catName_481_, v_declName_482_, v___x_484_);
return v___x_485_;
}
default: 
{
lean_object* v_catName_486_; lean_object* v_declName_487_; lean_object* v_prio_488_; lean_object* v___x_489_; 
v_catName_486_ = lean_ctor_get(v_t_475_, 0);
lean_inc(v_catName_486_);
v_declName_487_ = lean_ctor_get(v_t_475_, 1);
lean_inc(v_declName_487_);
v_prio_488_ = lean_ctor_get(v_t_475_, 2);
lean_inc(v_prio_488_);
lean_dec_ref_known(v_t_475_, 3);
v___x_489_ = lean_apply_3(v_k_476_, v_catName_486_, v_declName_487_, v_prio_488_);
return v___x_489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(lean_object* v_motive_490_, lean_object* v_ctorIdx_491_, lean_object* v_t_492_, lean_object* v_h_493_, lean_object* v_k_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_492_, v_k_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___boxed(lean_object* v_motive_496_, lean_object* v_ctorIdx_497_, lean_object* v_t_498_, lean_object* v_h_499_, lean_object* v_k_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(v_motive_496_, v_ctorIdx_497_, v_t_498_, v_h_499_, v_k_500_);
lean_dec(v_ctorIdx_497_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim___redArg(lean_object* v_t_502_, lean_object* v_token_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_502_, v_token_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim(lean_object* v_motive_505_, lean_object* v_t_506_, lean_object* v_h_507_, lean_object* v_token_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_506_, v_token_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim___redArg(lean_object* v_t_510_, lean_object* v_kind_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_510_, v_kind_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim(lean_object* v_motive_513_, lean_object* v_t_514_, lean_object* v_h_515_, lean_object* v_kind_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_514_, v_kind_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim___redArg(lean_object* v_t_518_, lean_object* v_category_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_518_, v_category_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim(lean_object* v_motive_521_, lean_object* v_t_522_, lean_object* v_h_523_, lean_object* v_category_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_522_, v_category_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim___redArg(lean_object* v_t_526_, lean_object* v_parser_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_526_, v_parser_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim(lean_object* v_motive_529_, lean_object* v_t_530_, lean_object* v_h_531_, lean_object* v_parser_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_530_, v_parser_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx(lean_object* v_x_539_){
_start:
{
switch(lean_obj_tag(v_x_539_))
{
case 0:
{
lean_object* v___x_540_; 
v___x_540_ = lean_unsigned_to_nat(0u);
return v___x_540_;
}
case 1:
{
lean_object* v___x_541_; 
v___x_541_ = lean_unsigned_to_nat(1u);
return v___x_541_;
}
case 2:
{
lean_object* v___x_542_; 
v___x_542_ = lean_unsigned_to_nat(2u);
return v___x_542_;
}
default: 
{
lean_object* v___x_543_; 
v___x_543_ = lean_unsigned_to_nat(3u);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___boxed(lean_object* v_x_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Parser_ParserExtension_Entry_ctorIdx(v_x_544_);
lean_dec_ref(v_x_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(lean_object* v_t_546_, lean_object* v_k_547_){
_start:
{
switch(lean_obj_tag(v_t_546_))
{
case 0:
{
lean_object* v_val_548_; lean_object* v___x_549_; 
v_val_548_ = lean_ctor_get(v_t_546_, 0);
lean_inc_ref(v_val_548_);
lean_dec_ref_known(v_t_546_, 1);
v___x_549_ = lean_apply_1(v_k_547_, v_val_548_);
return v___x_549_;
}
case 1:
{
lean_object* v_val_550_; lean_object* v___x_551_; 
v_val_550_ = lean_ctor_get(v_t_546_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v_t_546_, 1);
v___x_551_ = lean_apply_1(v_k_547_, v_val_550_);
return v___x_551_;
}
case 2:
{
lean_object* v_catName_552_; lean_object* v_declName_553_; uint8_t v_behavior_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_catName_552_ = lean_ctor_get(v_t_546_, 0);
lean_inc(v_catName_552_);
v_declName_553_ = lean_ctor_get(v_t_546_, 1);
lean_inc(v_declName_553_);
v_behavior_554_ = lean_ctor_get_uint8(v_t_546_, sizeof(void*)*2);
lean_dec_ref_known(v_t_546_, 2);
v___x_555_ = lean_box(v_behavior_554_);
v___x_556_ = lean_apply_3(v_k_547_, v_catName_552_, v_declName_553_, v___x_555_);
return v___x_556_;
}
default: 
{
lean_object* v_catName_557_; lean_object* v_declName_558_; uint8_t v_leading_559_; lean_object* v_p_560_; lean_object* v_prio_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_catName_557_ = lean_ctor_get(v_t_546_, 0);
lean_inc(v_catName_557_);
v_declName_558_ = lean_ctor_get(v_t_546_, 1);
lean_inc(v_declName_558_);
v_leading_559_ = lean_ctor_get_uint8(v_t_546_, sizeof(void*)*4);
v_p_560_ = lean_ctor_get(v_t_546_, 2);
lean_inc_ref(v_p_560_);
v_prio_561_ = lean_ctor_get(v_t_546_, 3);
lean_inc(v_prio_561_);
lean_dec_ref_known(v_t_546_, 4);
v___x_562_ = lean_box(v_leading_559_);
v___x_563_ = lean_apply_5(v_k_547_, v_catName_557_, v_declName_558_, v___x_562_, v_p_560_, v_prio_561_);
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim(lean_object* v_motive_564_, lean_object* v_ctorIdx_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_k_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_566_, v_k_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___boxed(lean_object* v_motive_570_, lean_object* v_ctorIdx_571_, lean_object* v_t_572_, lean_object* v_h_573_, lean_object* v_k_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Parser_ParserExtension_Entry_ctorElim(v_motive_570_, v_ctorIdx_571_, v_t_572_, v_h_573_, v_k_574_);
lean_dec(v_ctorIdx_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim___redArg(lean_object* v_t_576_, lean_object* v_token_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_576_, v_token_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim(lean_object* v_motive_579_, lean_object* v_t_580_, lean_object* v_h_581_, lean_object* v_token_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_580_, v_token_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim___redArg(lean_object* v_t_584_, lean_object* v_kind_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_584_, v_kind_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim(lean_object* v_motive_587_, lean_object* v_t_588_, lean_object* v_h_589_, lean_object* v_kind_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_588_, v_kind_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim___redArg(lean_object* v_t_592_, lean_object* v_category_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_592_, v_category_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim(lean_object* v_motive_595_, lean_object* v_t_596_, lean_object* v_h_597_, lean_object* v_category_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_596_, v_category_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim___redArg(lean_object* v_t_600_, lean_object* v_parser_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_600_, v_parser_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim(lean_object* v_motive_603_, lean_object* v_t_604_, lean_object* v_h_605_, lean_object* v_parser_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_604_, v_parser_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object* v_x_612_){
_start:
{
switch(lean_obj_tag(v_x_612_))
{
case 0:
{
lean_object* v_val_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
v_val_613_ = lean_ctor_get(v_x_612_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_x_612_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v_x_612_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_val_613_);
lean_dec(v_x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_val_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
case 1:
{
lean_object* v_val_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
v_val_621_ = lean_ctor_get(v_x_612_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x_612_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v_x_612_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_val_621_);
lean_dec(v_x_612_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_val_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
case 2:
{
lean_object* v_catName_629_; lean_object* v_declName_630_; uint8_t v_behavior_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
v_catName_629_ = lean_ctor_get(v_x_612_, 0);
v_declName_630_ = lean_ctor_get(v_x_612_, 1);
v_behavior_631_ = lean_ctor_get_uint8(v_x_612_, sizeof(void*)*2);
v_isSharedCheck_638_ = !lean_is_exclusive(v_x_612_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v_x_612_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_declName_630_);
lean_inc(v_catName_629_);
lean_dec(v_x_612_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_catName_629_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_declName_630_);
lean_ctor_set_uint8(v_reuseFailAlloc_637_, sizeof(void*)*2, v_behavior_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
default: 
{
lean_object* v_catName_639_; lean_object* v_declName_640_; lean_object* v_prio_641_; lean_object* v___x_642_; 
v_catName_639_ = lean_ctor_get(v_x_612_, 0);
lean_inc(v_catName_639_);
v_declName_640_ = lean_ctor_get(v_x_612_, 1);
lean_inc(v_declName_640_);
v_prio_641_ = lean_ctor_get(v_x_612_, 3);
lean_inc(v_prio_641_);
lean_dec_ref_known(v_x_612_, 4);
v___x_642_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_642_, 0, v_catName_639_);
lean_ctor_set(v___x_642_, 1, v_declName_640_);
lean_ctor_set(v___x_642_, 2, v_prio_641_);
return v___x_642_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_644_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___x_643_);
lean_ctor_set(v___x_645_, 2, v___x_643_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lean_obj_once(&l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0, &l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0_once, _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState(void){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_649_ = l_Lean_Parser_builtinTokenTable;
v___x_650_ = lean_st_ref_get(v___x_649_);
v___x_651_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_652_ = lean_st_ref_get(v___x_651_);
v___x_653_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_654_ = lean_st_ref_get(v___x_653_);
v___x_655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_655_, 0, v___x_650_);
lean_ctor_set(v___x_655_, 1, v___x_652_);
lean_ctor_set(v___x_655_, 2, v___x_654_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object* v_tokens_662_, lean_object* v_tk_663_){
_start:
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = ((lean_object*)(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0));
v___x_665_ = lean_string_dec_eq(v_tk_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Data_Trie_find_x3f___redArg(v_tokens_662_, v_tk_663_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_inc_ref(v_tk_663_);
v___x_667_ = l_Lean_Data_Trie_insert___redArg(v_tokens_662_, v_tk_663_, v_tk_663_);
lean_dec_ref(v_tk_663_);
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
else
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec_ref(v_tk_663_);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; 
v_unused_676_ = lean_ctor_get(v___x_666_, 0);
lean_dec(v_unused_676_);
v___x_670_ = v___x_666_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_dec(v___x_666_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v_tokens_662_);
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_tokens_662_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v___x_677_; 
lean_dec_ref(v_tk_663_);
lean_dec_ref(v_tokens_662_);
v___x_677_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1));
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg(lean_object* v_catName_680_){
_start:
{
lean_object* v___x_681_; uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_681_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0));
v___x_682_ = 1;
v___x_683_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_680_, v___x_682_);
v___x_684_ = lean_string_append(v___x_681_, v___x_683_);
lean_dec_ref(v___x_683_);
v___x_685_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_686_ = lean_string_append(v___x_684_, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object* v_00_u03b1_688_, lean_object* v_catName_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object* v_categories_693_, lean_object* v_catName_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__0));
v___x_696_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__1));
v___x_697_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_695_, v___x_696_, v_categories_693_, v_catName_694_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory___boxed(lean_object* v_categories_698_, lean_object* v_catName_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Parser_getCategory(v_categories_698_, v_catName_699_);
lean_dec_ref(v_categories_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(lean_object* v_as_702_){
_start:
{
lean_object* v___f_703_; lean_object* v___x_704_; 
v___f_703_ = ((lean_object*)(l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0));
v___x_704_ = l_List_eraseDupsBy___redArg(v___f_703_, v_as_702_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(lean_object* v_p_705_, lean_object* v_prio_706_, lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
if (lean_obj_tag(v_x_708_) == 0)
{
lean_dec(v_prio_706_);
lean_dec_ref(v_p_705_);
return v_x_707_;
}
else
{
lean_object* v_head_709_; lean_object* v_tail_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_730_; 
v_head_709_ = lean_ctor_get(v_x_708_, 0);
v_tail_710_ = lean_ctor_get(v_x_708_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_708_);
if (v_isSharedCheck_730_ == 0)
{
v___x_712_ = v_x_708_;
v_isShared_713_ = v_isSharedCheck_730_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_tail_710_);
lean_inc(v_head_709_);
lean_dec(v_x_708_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_730_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_leadingTable_714_; lean_object* v_leadingParsers_715_; lean_object* v_trailingTable_716_; lean_object* v_trailingParsers_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_729_; 
v_leadingTable_714_ = lean_ctor_get(v_x_707_, 0);
v_leadingParsers_715_ = lean_ctor_get(v_x_707_, 1);
v_trailingTable_716_ = lean_ctor_get(v_x_707_, 2);
v_trailingParsers_717_ = lean_ctor_get(v_x_707_, 3);
v_isSharedCheck_729_ = !lean_is_exclusive(v_x_707_);
if (v_isSharedCheck_729_ == 0)
{
v___x_719_ = v_x_707_;
v_isShared_720_ = v_isSharedCheck_729_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_trailingParsers_717_);
lean_inc(v_trailingTable_716_);
lean_inc(v_leadingParsers_715_);
lean_inc(v_leadingTable_714_);
lean_dec(v_x_707_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_729_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
lean_inc(v_prio_706_);
lean_inc_ref(v_p_705_);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 0);
lean_ctor_set(v___x_712_, 1, v_prio_706_);
lean_ctor_set(v___x_712_, 0, v_p_705_);
v___x_722_ = v___x_712_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_p_705_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_prio_706_);
v___x_722_ = v_reuseFailAlloc_728_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = l_Lean_Parser_TokenMap_insert___redArg(v_leadingTable_714_, v_head_709_, v___x_722_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_723_);
v___x_725_ = v___x_719_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_leadingParsers_715_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_trailingTable_716_);
lean_ctor_set(v_reuseFailAlloc_727_, 3, v_trailingParsers_717_);
v___x_725_ = v_reuseFailAlloc_727_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
v_x_707_ = v___x_725_;
v_x_708_ = v_tail_710_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_731_, lean_object* v_vals_732_, lean_object* v_i_733_, lean_object* v_k_734_){
_start:
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = lean_array_get_size(v_keys_731_);
v___x_736_ = lean_nat_dec_lt(v_i_733_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_dec(v_i_733_);
v___x_737_ = lean_box(0);
return v___x_737_;
}
else
{
lean_object* v_k_x27_738_; uint8_t v___x_739_; 
v_k_x27_738_ = lean_array_fget_borrowed(v_keys_731_, v_i_733_);
v___x_739_ = lean_name_eq(v_k_734_, v_k_x27_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_i_733_, v___x_740_);
lean_dec(v_i_733_);
v_i_733_ = v___x_741_;
goto _start;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_array_fget_borrowed(v_vals_732_, v_i_733_);
lean_dec(v_i_733_);
lean_inc(v___x_743_);
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_745_, lean_object* v_vals_746_, lean_object* v_i_747_, lean_object* v_k_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_745_, v_vals_746_, v_i_747_, v_k_748_);
lean_dec(v_k_748_);
lean_dec_ref(v_vals_746_);
lean_dec_ref(v_keys_745_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(lean_object* v_x_750_, size_t v_x_751_, lean_object* v_x_752_){
_start:
{
if (lean_obj_tag(v_x_750_) == 0)
{
lean_object* v_es_753_; lean_object* v___x_754_; size_t v___x_755_; size_t v___x_756_; lean_object* v_j_757_; lean_object* v___x_758_; 
v_es_753_ = lean_ctor_get(v_x_750_, 0);
v___x_754_ = lean_box(2);
v___x_755_ = ((size_t)31ULL);
v___x_756_ = lean_usize_land(v_x_751_, v___x_755_);
v_j_757_ = lean_usize_to_nat(v___x_756_);
v___x_758_ = lean_array_get_borrowed(v___x_754_, v_es_753_, v_j_757_);
lean_dec(v_j_757_);
switch(lean_obj_tag(v___x_758_))
{
case 0:
{
lean_object* v_key_759_; lean_object* v_val_760_; uint8_t v___x_761_; 
v_key_759_ = lean_ctor_get(v___x_758_, 0);
v_val_760_ = lean_ctor_get(v___x_758_, 1);
v___x_761_ = lean_name_eq(v_x_752_, v_key_759_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; 
v___x_762_ = lean_box(0);
return v___x_762_;
}
else
{
lean_object* v___x_763_; 
lean_inc(v_val_760_);
v___x_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_763_, 0, v_val_760_);
return v___x_763_;
}
}
case 1:
{
lean_object* v_node_764_; size_t v___x_765_; size_t v___x_766_; 
v_node_764_ = lean_ctor_get(v___x_758_, 0);
v___x_765_ = ((size_t)5ULL);
v___x_766_ = lean_usize_shift_right(v_x_751_, v___x_765_);
v_x_750_ = v_node_764_;
v_x_751_ = v___x_766_;
goto _start;
}
default: 
{
lean_object* v___x_768_; 
v___x_768_ = lean_box(0);
return v___x_768_;
}
}
}
else
{
lean_object* v_ks_769_; lean_object* v_vs_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_ks_769_ = lean_ctor_get(v_x_750_, 0);
v_vs_770_ = lean_ctor_get(v_x_750_, 1);
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_ks_769_, v_vs_770_, v___x_771_, v_x_752_);
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg___boxed(lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
size_t v_x_496__boxed_776_; lean_object* v_res_777_; 
v_x_496__boxed_776_ = lean_unbox_usize(v_x_774_);
lean_dec(v_x_774_);
v_res_777_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_773_, v_x_496__boxed_776_, v_x_775_);
lean_dec(v_x_775_);
lean_dec_ref(v_x_773_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
uint64_t v___y_781_; 
if (lean_obj_tag(v_x_779_) == 0)
{
uint64_t v___x_784_; 
v___x_784_ = 1723ULL;
v___y_781_ = v___x_784_;
goto v___jp_780_;
}
else
{
uint64_t v_hash_785_; 
v_hash_785_ = lean_ctor_get_uint64(v_x_779_, sizeof(void*)*2);
v___y_781_ = v_hash_785_;
goto v___jp_780_;
}
v___jp_780_:
{
size_t v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_uint64_to_usize(v___y_781_);
v___x_783_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_778_, v___x_782_, v_x_779_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg___boxed(lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_786_, v_x_787_);
lean_dec(v_x_787_);
lean_dec_ref(v_x_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
if (lean_obj_tag(v_a_789_) == 0)
{
lean_object* v___x_791_; 
v___x_791_ = l_List_reverse___redArg(v_a_790_);
return v___x_791_;
}
else
{
lean_object* v_head_792_; lean_object* v_tail_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_803_; 
v_head_792_ = lean_ctor_get(v_a_789_, 0);
v_tail_793_ = lean_ctor_get(v_a_789_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v_a_789_);
if (v_isSharedCheck_803_ == 0)
{
v___x_795_ = v_a_789_;
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_tail_793_);
lean_inc(v_head_792_);
lean_dec(v_a_789_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_797_ = lean_box(0);
v___x_798_ = l_Lean_Name_str___override(v___x_797_, v_head_792_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v_a_790_);
lean_ctor_set(v___x_795_, 0, v___x_798_);
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_a_790_);
v___x_800_ = v_reuseFailAlloc_802_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
v_a_789_ = v_tail_793_;
v_a_790_ = v___x_800_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object* v_categories_804_, lean_object* v_catName_805_, lean_object* v_declName_806_, lean_object* v_p_807_, lean_object* v_prio_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_804_, v_catName_805_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v___x_810_; 
lean_dec(v_prio_808_);
lean_dec_ref(v_p_807_);
lean_dec(v_declName_806_);
lean_dec_ref(v_categories_804_);
v___x_810_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_805_);
return v___x_810_;
}
else
{
lean_object* v_val_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_857_; 
v_val_811_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_857_ == 0)
{
v___x_813_ = v___x_809_;
v_isShared_814_ = v_isSharedCheck_857_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_val_811_);
lean_dec(v___x_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_857_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_info_815_; lean_object* v_declName_816_; lean_object* v_kinds_817_; lean_object* v_tables_818_; uint8_t v_behavior_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_856_; 
v_info_815_ = lean_ctor_get(v_p_807_, 0);
v_declName_816_ = lean_ctor_get(v_val_811_, 0);
v_kinds_817_ = lean_ctor_get(v_val_811_, 1);
v_tables_818_ = lean_ctor_get(v_val_811_, 2);
v_behavior_819_ = lean_ctor_get_uint8(v_val_811_, sizeof(void*)*3);
v_isSharedCheck_856_ = !lean_is_exclusive(v_val_811_);
if (v_isSharedCheck_856_ == 0)
{
v___x_821_ = v_val_811_;
v_isShared_822_ = v_isSharedCheck_856_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_tables_818_);
lean_inc(v_kinds_817_);
lean_inc(v_declName_816_);
lean_dec(v_val_811_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_856_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_firstTokens_823_; lean_object* v_kinds_824_; lean_object* v_tks_826_; 
v_firstTokens_823_ = lean_ctor_get(v_info_815_, 2);
v_kinds_824_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_817_, v_declName_806_);
switch(lean_obj_tag(v_firstTokens_823_))
{
case 2:
{
lean_object* v_a_838_; 
v_a_838_ = lean_ctor_get(v_firstTokens_823_, 0);
lean_inc(v_a_838_);
v_tks_826_ = v_a_838_;
goto v___jp_825_;
}
case 3:
{
lean_object* v_a_839_; 
v_a_839_ = lean_ctor_get(v_firstTokens_823_, 0);
lean_inc(v_a_839_);
v_tks_826_ = v_a_839_;
goto v___jp_825_;
}
default: 
{
lean_object* v_leadingTable_840_; lean_object* v_leadingParsers_841_; lean_object* v_trailingTable_842_; lean_object* v_trailingParsers_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_855_; 
lean_del_object(v___x_821_);
lean_del_object(v___x_813_);
v_leadingTable_840_ = lean_ctor_get(v_tables_818_, 0);
v_leadingParsers_841_ = lean_ctor_get(v_tables_818_, 1);
v_trailingTable_842_ = lean_ctor_get(v_tables_818_, 2);
v_trailingParsers_843_ = lean_ctor_get(v_tables_818_, 3);
v_isSharedCheck_855_ = !lean_is_exclusive(v_tables_818_);
if (v_isSharedCheck_855_ == 0)
{
v___x_845_ = v_tables_818_;
v_isShared_846_ = v_isSharedCheck_855_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_trailingParsers_843_);
lean_inc(v_trailingTable_842_);
lean_inc(v_leadingParsers_841_);
lean_inc(v_leadingTable_840_);
lean_dec(v_tables_818_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_855_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_tables_850_; 
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_p_807_);
lean_ctor_set(v___x_847_, 1, v_prio_808_);
v___x_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v_leadingParsers_841_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v___x_848_);
v_tables_850_ = v___x_845_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_leadingTable_840_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_854_, 2, v_trailingTable_842_);
lean_ctor_set(v_reuseFailAlloc_854_, 3, v_trailingParsers_843_);
v_tables_850_ = v_reuseFailAlloc_854_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_851_, 0, v_declName_816_);
lean_ctor_set(v___x_851_, 1, v_kinds_824_);
lean_ctor_set(v___x_851_, 2, v_tables_850_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*3, v_behavior_819_);
v___x_852_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_804_, v_catName_805_, v___x_851_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
}
}
v___jp_825_:
{
lean_object* v___x_827_; lean_object* v_tks_828_; lean_object* v___x_829_; lean_object* v_tables_830_; lean_object* v___x_832_; 
v___x_827_ = lean_box(0);
v_tks_828_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_826_, v___x_827_);
v___x_829_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_828_);
v_tables_830_ = l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(v_p_807_, v_prio_808_, v_tables_818_, v___x_829_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 2, v_tables_830_);
lean_ctor_set(v___x_821_, 1, v_kinds_824_);
v___x_832_ = v___x_821_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_declName_816_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_kinds_824_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v_tables_830_);
lean_ctor_set_uint8(v_reuseFailAlloc_837_, sizeof(void*)*3, v_behavior_819_);
v___x_832_ = v_reuseFailAlloc_837_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_804_, v_catName_805_, v___x_832_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_833_);
v___x_835_ = v___x_813_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(lean_object* v_00_u03b2_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___boxed(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(v_00_u03b2_862_, v_x_863_, v_x_864_);
lean_dec(v_x_864_);
lean_dec_ref(v_x_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_object* v_00_u03b2_866_, lean_object* v_x_867_, size_t v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_867_, v_x_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___boxed(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
size_t v_x_665__boxed_875_; lean_object* v_res_876_; 
v_x_665__boxed_875_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_res_876_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(v_00_u03b2_871_, v_x_872_, v_x_665__boxed_875_, v_x_874_);
lean_dec(v_x_874_);
lean_dec_ref(v_x_872_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_877_, lean_object* v_keys_878_, lean_object* v_vals_879_, lean_object* v_heq_880_, lean_object* v_i_881_, lean_object* v_k_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_878_, v_vals_879_, v_i_881_, v_k_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_884_, lean_object* v_keys_885_, lean_object* v_vals_886_, lean_object* v_heq_887_, lean_object* v_i_888_, lean_object* v_k_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(v_00_u03b2_884_, v_keys_885_, v_vals_886_, v_heq_887_, v_i_888_, v_k_889_);
lean_dec(v_k_889_);
lean_dec_ref(v_vals_886_);
lean_dec_ref(v_keys_885_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(lean_object* v_p_891_, lean_object* v_prio_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
lean_dec(v_prio_892_);
lean_dec_ref(v_p_891_);
return v_x_893_;
}
else
{
lean_object* v_head_895_; lean_object* v_tail_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_916_; 
v_head_895_ = lean_ctor_get(v_x_894_, 0);
v_tail_896_ = lean_ctor_get(v_x_894_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_x_894_);
if (v_isSharedCheck_916_ == 0)
{
v___x_898_ = v_x_894_;
v_isShared_899_ = v_isSharedCheck_916_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_tail_896_);
lean_inc(v_head_895_);
lean_dec(v_x_894_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_916_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_leadingTable_900_; lean_object* v_leadingParsers_901_; lean_object* v_trailingTable_902_; lean_object* v_trailingParsers_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_915_; 
v_leadingTable_900_ = lean_ctor_get(v_x_893_, 0);
v_leadingParsers_901_ = lean_ctor_get(v_x_893_, 1);
v_trailingTable_902_ = lean_ctor_get(v_x_893_, 2);
v_trailingParsers_903_ = lean_ctor_get(v_x_893_, 3);
v_isSharedCheck_915_ = !lean_is_exclusive(v_x_893_);
if (v_isSharedCheck_915_ == 0)
{
v___x_905_ = v_x_893_;
v_isShared_906_ = v_isSharedCheck_915_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_trailingParsers_903_);
lean_inc(v_trailingTable_902_);
lean_inc(v_leadingParsers_901_);
lean_inc(v_leadingTable_900_);
lean_dec(v_x_893_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_915_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
lean_inc(v_prio_892_);
lean_inc_ref(v_p_891_);
if (v_isShared_899_ == 0)
{
lean_ctor_set_tag(v___x_898_, 0);
lean_ctor_set(v___x_898_, 1, v_prio_892_);
lean_ctor_set(v___x_898_, 0, v_p_891_);
v___x_908_ = v___x_898_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_p_891_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_prio_892_);
v___x_908_ = v_reuseFailAlloc_914_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_909_ = l_Lean_Parser_TokenMap_insert___redArg(v_trailingTable_902_, v_head_895_, v___x_908_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 2, v___x_909_);
v___x_911_ = v___x_905_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_leadingTable_900_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_leadingParsers_901_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_trailingParsers_903_);
v___x_911_ = v_reuseFailAlloc_913_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
v_x_893_ = v___x_911_;
v_x_894_ = v_tail_896_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object* v_tables_917_, lean_object* v_p_918_, lean_object* v_prio_919_){
_start:
{
lean_object* v_tks_921_; lean_object* v_info_926_; lean_object* v_firstTokens_927_; 
v_info_926_ = lean_ctor_get(v_p_918_, 0);
v_firstTokens_927_ = lean_ctor_get(v_info_926_, 2);
switch(lean_obj_tag(v_firstTokens_927_))
{
case 2:
{
lean_object* v_a_928_; 
v_a_928_ = lean_ctor_get(v_firstTokens_927_, 0);
lean_inc(v_a_928_);
v_tks_921_ = v_a_928_;
goto v___jp_920_;
}
case 3:
{
lean_object* v_a_929_; 
v_a_929_ = lean_ctor_get(v_firstTokens_927_, 0);
lean_inc(v_a_929_);
v_tks_921_ = v_a_929_;
goto v___jp_920_;
}
default: 
{
lean_object* v_leadingTable_930_; lean_object* v_leadingParsers_931_; lean_object* v_trailingTable_932_; lean_object* v_trailingParsers_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_942_; 
v_leadingTable_930_ = lean_ctor_get(v_tables_917_, 0);
v_leadingParsers_931_ = lean_ctor_get(v_tables_917_, 1);
v_trailingTable_932_ = lean_ctor_get(v_tables_917_, 2);
v_trailingParsers_933_ = lean_ctor_get(v_tables_917_, 3);
v_isSharedCheck_942_ = !lean_is_exclusive(v_tables_917_);
if (v_isSharedCheck_942_ == 0)
{
v___x_935_ = v_tables_917_;
v_isShared_936_ = v_isSharedCheck_942_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_trailingParsers_933_);
lean_inc(v_trailingTable_932_);
lean_inc(v_leadingParsers_931_);
lean_inc(v_leadingTable_930_);
lean_dec(v_tables_917_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_942_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_p_918_);
lean_ctor_set(v___x_937_, 1, v_prio_919_);
v___x_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v_trailingParsers_933_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 3, v___x_938_);
v___x_940_ = v___x_935_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_leadingTable_930_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_leadingParsers_931_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_trailingTable_932_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
v___jp_920_:
{
lean_object* v___x_922_; lean_object* v_tks_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_922_ = lean_box(0);
v_tks_923_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_921_, v___x_922_);
v___x_924_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_923_);
v___x_925_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(v_p_918_, v_prio_919_, v_tables_917_, v___x_924_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object* v_categories_943_, lean_object* v_catName_944_, lean_object* v_declName_945_, lean_object* v_p_946_, lean_object* v_prio_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_943_, v_catName_944_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v___x_949_; 
lean_dec(v_prio_947_);
lean_dec_ref(v_p_946_);
lean_dec(v_declName_945_);
lean_dec_ref(v_categories_943_);
v___x_949_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_944_);
return v___x_949_;
}
else
{
lean_object* v_val_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_971_; 
v_val_950_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_971_ == 0)
{
v___x_952_ = v___x_948_;
v_isShared_953_ = v_isSharedCheck_971_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_val_950_);
lean_dec(v___x_948_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_971_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_declName_954_; lean_object* v_kinds_955_; lean_object* v_tables_956_; uint8_t v_behavior_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_970_; 
v_declName_954_ = lean_ctor_get(v_val_950_, 0);
v_kinds_955_ = lean_ctor_get(v_val_950_, 1);
v_tables_956_ = lean_ctor_get(v_val_950_, 2);
v_behavior_957_ = lean_ctor_get_uint8(v_val_950_, sizeof(void*)*3);
v_isSharedCheck_970_ = !lean_is_exclusive(v_val_950_);
if (v_isSharedCheck_970_ == 0)
{
v___x_959_ = v_val_950_;
v_isShared_960_ = v_isSharedCheck_970_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_tables_956_);
lean_inc(v_kinds_955_);
lean_inc(v_declName_954_);
lean_dec(v_val_950_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_970_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_kinds_961_; lean_object* v_tables_962_; lean_object* v___x_964_; 
v_kinds_961_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_955_, v_declName_945_);
v_tables_962_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(v_tables_956_, v_p_946_, v_prio_947_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 2, v_tables_962_);
lean_ctor_set(v___x_959_, 1, v_kinds_961_);
v___x_964_ = v___x_959_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_declName_954_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_kinds_961_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_tables_962_);
lean_ctor_set_uint8(v_reuseFailAlloc_969_, sizeof(void*)*3, v_behavior_957_);
v___x_964_ = v_reuseFailAlloc_969_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_965_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_943_, v_catName_944_, v___x_964_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_965_);
v___x_967_ = v___x_952_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object* v_categories_972_, lean_object* v_catName_973_, lean_object* v_declName_974_, uint8_t v_leading_975_, lean_object* v_p_976_, lean_object* v_prio_977_){
_start:
{
if (v_leading_975_ == 0)
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_Parser_addTrailingParser(v_categories_972_, v_catName_973_, v_declName_974_, v_p_976_, v_prio_977_);
return v___x_978_;
}
else
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_Parser_addLeadingParser(v_categories_972_, v_catName_973_, v_declName_974_, v_p_976_, v_prio_977_);
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object* v_categories_980_, lean_object* v_catName_981_, lean_object* v_declName_982_, lean_object* v_leading_983_, lean_object* v_p_984_, lean_object* v_prio_985_){
_start:
{
uint8_t v_leading_boxed_986_; lean_object* v_res_987_; 
v_leading_boxed_986_ = lean_unbox(v_leading_983_);
v_res_987_ = l_Lean_Parser_addParser(v_categories_980_, v_catName_981_, v_declName_982_, v_leading_boxed_986_, v_p_984_, v_prio_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(lean_object* v_x_988_, lean_object* v_x_989_){
_start:
{
if (lean_obj_tag(v_x_989_) == 0)
{
lean_object* v___x_990_; 
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v_x_988_);
return v___x_990_;
}
else
{
lean_object* v_head_991_; lean_object* v_tail_992_; lean_object* v___x_993_; 
v_head_991_ = lean_ctor_get(v_x_989_, 0);
lean_inc(v_head_991_);
v_tail_992_ = lean_ctor_get(v_x_989_, 1);
lean_inc(v_tail_992_);
lean_dec_ref_known(v_x_989_, 2);
v___x_993_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_x_988_, v_head_991_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_dec(v_tail_992_);
return v___x_993_;
}
else
{
lean_object* v_a_994_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
v_x_988_ = v_a_994_;
v_x_989_ = v_tail_992_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object* v_tokenTable_996_, lean_object* v_info_997_){
_start:
{
lean_object* v_collectTokens_998_; lean_object* v___x_999_; lean_object* v_newTokens_1000_; lean_object* v___x_1001_; 
v_collectTokens_998_ = lean_ctor_get(v_info_997_, 0);
lean_inc_ref(v_collectTokens_998_);
lean_dec_ref(v_info_997_);
v___x_999_ = lean_box(0);
v_newTokens_1000_ = lean_apply_1(v_collectTokens_998_, v___x_999_);
v___x_1001_ = l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(v_tokenTable_996_, v_newTokens_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object* v_info_1004_, lean_object* v_declName_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1007_ = l_Lean_Parser_builtinTokenTable;
v___x_1008_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_1009_ = lean_st_ref_swap(v___x_1007_, v___x_1008_);
v___x_1010_ = l_Lean_Parser_addParserTokens(v___x_1009_, v_info_1004_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1027_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1027_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1027_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1015_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0));
v___x_1016_ = l_Lean_privateToUserName(v_declName_1005_);
v___x_1017_ = 1;
v___x_1018_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1016_, v___x_1017_);
v___x_1019_ = lean_string_append(v___x_1015_, v___x_1018_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_1021_ = lean_string_append(v___x_1019_, v___x_1020_);
v___x_1022_ = lean_string_append(v___x_1021_, v_a_1011_);
lean_dec(v_a_1011_);
v___x_1023_ = lean_mk_io_user_error(v___x_1022_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set_tag(v___x_1013_, 1);
lean_ctor_set(v___x_1013_, 0, v___x_1023_);
v___x_1025_ = v___x_1013_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v_declName_1005_);
v_a_1028_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1030_ = v___x_1010_;
v_isShared_1031_ = v_isSharedCheck_1037_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1010_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1037_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_st_ref_swap(v___x_1007_, v_a_1028_);
lean_dec(v___x_1033_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1032_);
v___x_1035_ = v___x_1030_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1032_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___boxed(lean_object* v_info_1038_, lean_object* v_declName_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_1038_, v_declName_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(lean_object* v_msg_1042_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1044_ = lean_panic_fn_borrowed(v___x_1043_, v_msg_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object* v_s_1048_, lean_object* v_e_1049_){
_start:
{
switch(lean_obj_tag(v_e_1049_))
{
case 0:
{
lean_object* v_val_1050_; lean_object* v_tokens_1051_; lean_object* v_kinds_1052_; lean_object* v_categories_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1071_; 
v_val_1050_ = lean_ctor_get(v_e_1049_, 0);
lean_inc_ref(v_val_1050_);
lean_dec_ref_known(v_e_1049_, 1);
v_tokens_1051_ = lean_ctor_get(v_s_1048_, 0);
v_kinds_1052_ = lean_ctor_get(v_s_1048_, 1);
v_categories_1053_ = lean_ctor_get(v_s_1048_, 2);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_s_1048_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1055_ = v_s_1048_;
v_isShared_1056_ = v_isSharedCheck_1071_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_categories_1053_);
lean_inc(v_kinds_1052_);
lean_inc(v_tokens_1051_);
lean_dec(v_s_1048_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1071_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; 
v___x_1057_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_1051_, v_val_1050_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_del_object(v___x_1055_);
lean_dec_ref(v_categories_1053_);
lean_dec_ref(v_kinds_1052_);
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v___x_1059_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1060_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1061_ = lean_unsigned_to_nat(166u);
v___x_1062_ = lean_unsigned_to_nat(26u);
v___x_1063_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1064_ = lean_string_append(v___x_1063_, v_a_1058_);
lean_dec(v_a_1058_);
v___x_1065_ = l_mkPanicMessageWithDecl(v___x_1059_, v___x_1060_, v___x_1061_, v___x_1062_, v___x_1064_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1065_);
return v___x_1066_;
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; 
v_a_1067_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1057_, 1);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v_a_1067_);
v___x_1069_ = v___x_1055_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1067_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_kinds_1052_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_categories_1053_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
case 1:
{
lean_object* v_val_1072_; lean_object* v_tokens_1073_; lean_object* v_kinds_1074_; lean_object* v_categories_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_val_1072_ = lean_ctor_get(v_e_1049_, 0);
lean_inc(v_val_1072_);
lean_dec_ref_known(v_e_1049_, 1);
v_tokens_1073_ = lean_ctor_get(v_s_1048_, 0);
v_kinds_1074_ = lean_ctor_get(v_s_1048_, 1);
v_categories_1075_ = lean_ctor_get(v_s_1048_, 2);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_s_1048_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1077_ = v_s_1048_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_categories_1075_);
lean_inc(v_kinds_1074_);
lean_inc(v_tokens_1073_);
lean_dec(v_s_1048_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_1074_, v_val_1072_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_tokens_1073_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_categories_1075_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
case 2:
{
lean_object* v_catName_1084_; lean_object* v_declName_1085_; uint8_t v_behavior_1086_; lean_object* v_tokens_1087_; lean_object* v_kinds_1088_; lean_object* v_categories_1089_; uint8_t v___x_1090_; 
v_catName_1084_ = lean_ctor_get(v_e_1049_, 0);
lean_inc(v_catName_1084_);
v_declName_1085_ = lean_ctor_get(v_e_1049_, 1);
lean_inc(v_declName_1085_);
v_behavior_1086_ = lean_ctor_get_uint8(v_e_1049_, sizeof(void*)*2);
lean_dec_ref_known(v_e_1049_, 2);
v_tokens_1087_ = lean_ctor_get(v_s_1048_, 0);
v_kinds_1088_ = lean_ctor_get(v_s_1048_, 1);
v_categories_1089_ = lean_ctor_get(v_s_1048_, 2);
v___x_1090_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_1089_, v_catName_1084_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1101_; 
lean_inc_ref(v_categories_1089_);
lean_inc_ref(v_kinds_1088_);
lean_inc_ref(v_tokens_1087_);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_s_1048_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; lean_object* v_unused_1103_; lean_object* v_unused_1104_; 
v_unused_1102_ = lean_ctor_get(v_s_1048_, 2);
lean_dec(v_unused_1102_);
v_unused_1103_ = lean_ctor_get(v_s_1048_, 1);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_s_1048_, 0);
lean_dec(v_unused_1104_);
v___x_1092_ = v_s_1048_;
v_isShared_1093_ = v_isSharedCheck_1101_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v_s_1048_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1101_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1094_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_1095_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_1096_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1096_, 0, v_declName_1085_);
lean_ctor_set(v___x_1096_, 1, v___x_1094_);
lean_ctor_set(v___x_1096_, 2, v___x_1095_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*3, v_behavior_1086_);
v___x_1097_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_1089_, v_catName_1084_, v___x_1096_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 2, v___x_1097_);
v___x_1099_ = v___x_1092_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_tokens_1087_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_kinds_1088_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
else
{
lean_dec(v_declName_1085_);
lean_dec(v_catName_1084_);
return v_s_1048_;
}
}
default: 
{
lean_object* v_catName_1105_; lean_object* v_declName_1106_; uint8_t v_leading_1107_; lean_object* v_p_1108_; lean_object* v_prio_1109_; lean_object* v_tokens_1110_; lean_object* v_kinds_1111_; lean_object* v_categories_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1130_; 
v_catName_1105_ = lean_ctor_get(v_e_1049_, 0);
lean_inc(v_catName_1105_);
v_declName_1106_ = lean_ctor_get(v_e_1049_, 1);
lean_inc(v_declName_1106_);
v_leading_1107_ = lean_ctor_get_uint8(v_e_1049_, sizeof(void*)*4);
v_p_1108_ = lean_ctor_get(v_e_1049_, 2);
lean_inc_ref(v_p_1108_);
v_prio_1109_ = lean_ctor_get(v_e_1049_, 3);
lean_inc(v_prio_1109_);
lean_dec_ref_known(v_e_1049_, 4);
v_tokens_1110_ = lean_ctor_get(v_s_1048_, 0);
v_kinds_1111_ = lean_ctor_get(v_s_1048_, 1);
v_categories_1112_ = lean_ctor_get(v_s_1048_, 2);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_s_1048_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1114_ = v_s_1048_;
v_isShared_1115_ = v_isSharedCheck_1130_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_categories_1112_);
lean_inc(v_kinds_1111_);
lean_inc(v_tokens_1110_);
lean_dec(v_s_1048_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1130_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Parser_addParser(v_categories_1112_, v_catName_1105_, v_declName_1106_, v_leading_1107_, v_p_1108_, v_prio_1109_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_del_object(v___x_1114_);
lean_dec_ref(v_kinds_1111_);
lean_dec_ref(v_tokens_1110_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1119_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1120_ = lean_unsigned_to_nat(176u);
v___x_1121_ = lean_unsigned_to_nat(30u);
v___x_1122_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1123_ = lean_string_append(v___x_1122_, v_a_1117_);
lean_dec(v_a_1117_);
v___x_1124_ = l_mkPanicMessageWithDecl(v___x_1118_, v___x_1119_, v___x_1120_, v___x_1121_, v___x_1123_);
lean_dec_ref(v___x_1123_);
v___x_1125_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1124_);
return v___x_1125_;
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; 
v_a_1126_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1116_, 1);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 2, v_a_1126_);
v___x_1128_ = v___x_1114_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_tokens_1110_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_kinds_1111_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_a_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg(lean_object* v_x_1131_){
_start:
{
switch(lean_obj_tag(v_x_1131_))
{
case 0:
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
return v___x_1132_;
}
case 1:
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_unsigned_to_nat(1u);
return v___x_1133_;
}
default: 
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_unsigned_to_nat(2u);
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg___boxed(lean_object* v_x_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Parser_AliasValue_ctorIdx___redArg(v_x_1135_);
lean_dec_ref(v_x_1135_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx(lean_object* v_00_u03b1_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Parser_AliasValue_ctorIdx___redArg(v_x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___boxed(lean_object* v_00_u03b1_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_Parser_AliasValue_ctorIdx(v_00_u03b1_1140_, v_x_1141_);
lean_dec_ref(v_x_1141_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___redArg(lean_object* v_t_1143_, lean_object* v_k_1144_){
_start:
{
lean_object* v_p_1145_; lean_object* v___x_1146_; 
v_p_1145_ = lean_ctor_get(v_t_1143_, 0);
lean_inc(v_p_1145_);
lean_dec_ref(v_t_1143_);
v___x_1146_ = lean_apply_1(v_k_1144_, v_p_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim(lean_object* v_00_u03b1_1147_, lean_object* v_motive_1148_, lean_object* v_ctorIdx_1149_, lean_object* v_t_1150_, lean_object* v_h_1151_, lean_object* v_k_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1150_, v_k_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___boxed(lean_object* v_00_u03b1_1154_, lean_object* v_motive_1155_, lean_object* v_ctorIdx_1156_, lean_object* v_t_1157_, lean_object* v_h_1158_, lean_object* v_k_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_Parser_AliasValue_ctorElim(v_00_u03b1_1154_, v_motive_1155_, v_ctorIdx_1156_, v_t_1157_, v_h_1158_, v_k_1159_);
lean_dec(v_ctorIdx_1156_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim___redArg(lean_object* v_t_1161_, lean_object* v_const_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1161_, v_const_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim(lean_object* v_00_u03b1_1164_, lean_object* v_motive_1165_, lean_object* v_t_1166_, lean_object* v_h_1167_, lean_object* v_const_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1166_, v_const_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim___redArg(lean_object* v_t_1170_, lean_object* v_unary_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1170_, v_unary_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim(lean_object* v_00_u03b1_1173_, lean_object* v_motive_1174_, lean_object* v_t_1175_, lean_object* v_h_1176_, lean_object* v_unary_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1175_, v_unary_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim___redArg(lean_object* v_t_1179_, lean_object* v_binary_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1179_, v_binary_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim(lean_object* v_00_u03b1_1182_, lean_object* v_motive_1183_, lean_object* v_t_1184_, lean_object* v_h_1185_, lean_object* v_binary_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1184_, v_binary_1186_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_Parser_registerAliasCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__0));
v___x_1190_ = lean_mk_io_user_error(v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg(lean_object* v_mapRef_1193_, lean_object* v_aliasName_1194_, lean_object* v_value_1195_){
_start:
{
uint8_t v___x_1197_; 
v___x_1197_ = l_Lean_initializing();
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_dec_ref(v_value_1195_);
lean_dec(v_aliasName_1194_);
v___x_1198_ = lean_obj_once(&l_Lean_Parser_registerAliasCore___redArg___closed__1, &l_Lean_Parser_registerAliasCore___redArg___closed__1_once, _init_l_Lean_Parser_registerAliasCore___redArg___closed__1);
v___x_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = lean_st_ref_get(v_mapRef_1193_);
v___x_1201_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_aliasName_1194_, v___x_1200_);
lean_dec(v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1202_ = lean_st_ref_take(v_mapRef_1193_);
v___x_1203_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1194_, v_value_1195_, v___x_1202_);
v___x_1204_ = lean_st_ref_put(v_mapRef_1193_, v___x_1203_);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_dec_ref(v_value_1195_);
v___x_1206_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__2));
v___x_1207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1194_, v___x_1201_);
v___x_1208_ = lean_string_append(v___x_1206_, v___x_1207_);
lean_dec_ref(v___x_1207_);
v___x_1209_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__3));
v___x_1210_ = lean_string_append(v___x_1208_, v___x_1209_);
v___x_1211_ = lean_mk_io_user_error(v___x_1210_);
v___x_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg___boxed(lean_object* v_mapRef_1213_, lean_object* v_aliasName_1214_, lean_object* v_value_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1213_, v_aliasName_1214_, v_value_1215_);
lean_dec(v_mapRef_1213_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore(lean_object* v_00_u03b1_1218_, lean_object* v_mapRef_1219_, lean_object* v_aliasName_1220_, lean_object* v_value_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1219_, v_aliasName_1220_, v_value_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___boxed(lean_object* v_00_u03b1_1224_, lean_object* v_mapRef_1225_, lean_object* v_aliasName_1226_, lean_object* v_value_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Parser_registerAliasCore(v_00_u03b1_1224_, v_mapRef_1225_, v_aliasName_1226_, v_value_1227_);
lean_dec(v_mapRef_1225_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg(lean_object* v_mapRef_1230_, lean_object* v_aliasName_1231_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = lean_st_ref_get(v_mapRef_1230_);
v___x_1234_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1233_, v_aliasName_1231_);
lean_dec(v___x_1233_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg___boxed(lean_object* v_mapRef_1236_, lean_object* v_aliasName_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1236_, v_aliasName_1237_);
lean_dec(v_aliasName_1237_);
lean_dec(v_mapRef_1236_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias(lean_object* v_00_u03b1_1240_, lean_object* v_mapRef_1241_, lean_object* v_aliasName_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1241_, v_aliasName_1242_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___boxed(lean_object* v_00_u03b1_1245_, lean_object* v_mapRef_1246_, lean_object* v_aliasName_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Parser_getAlias(v_00_u03b1_1245_, v_mapRef_1246_, v_aliasName_1247_);
lean_dec(v_aliasName_1247_);
lean_dec(v_mapRef_1246_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object* v_mapRef_1254_, lean_object* v_aliasName_1255_){
_start:
{
lean_object* v___x_1257_; lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1297_; 
v___x_1257_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1254_, v_aliasName_1255_);
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1260_ = v___x_1257_;
v_isShared_1261_ = v_isSharedCheck_1297_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1297_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
if (lean_obj_tag(v_a_1258_) == 0)
{
lean_object* v___x_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1262_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1263_ = 1;
v___x_1264_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1255_, v___x_1263_);
v___x_1265_ = lean_string_append(v___x_1262_, v___x_1264_);
lean_dec_ref(v___x_1264_);
v___x_1266_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1267_ = lean_string_append(v___x_1265_, v___x_1266_);
v___x_1268_ = lean_mk_io_user_error(v___x_1267_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 1);
lean_ctor_set(v___x_1260_, 0, v___x_1268_);
v___x_1270_ = v___x_1260_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
else
{
lean_object* v_val_1272_; 
v_val_1272_ = lean_ctor_get(v_a_1258_, 0);
lean_inc(v_val_1272_);
lean_dec_ref_known(v_a_1258_, 1);
switch(lean_obj_tag(v_val_1272_))
{
case 0:
{
lean_object* v_p_1273_; lean_object* v___x_1275_; 
lean_dec(v_aliasName_1255_);
v_p_1273_ = lean_ctor_get(v_val_1272_, 0);
lean_inc(v_p_1273_);
lean_dec_ref_known(v_val_1272_, 1);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v_p_1273_);
v___x_1275_ = v___x_1260_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_p_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
case 1:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
lean_dec_ref_known(v_val_1272_, 1);
v___x_1277_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1278_ = 1;
v___x_1279_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1255_, v___x_1278_);
v___x_1280_ = lean_string_append(v___x_1277_, v___x_1279_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__2));
v___x_1282_ = lean_string_append(v___x_1280_, v___x_1281_);
v___x_1283_ = lean_mk_io_user_error(v___x_1282_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 1);
lean_ctor_set(v___x_1260_, 0, v___x_1283_);
v___x_1285_ = v___x_1260_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
default: 
{
lean_object* v___x_1287_; uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
lean_dec_ref_known(v_val_1272_, 1);
v___x_1287_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1288_ = 1;
v___x_1289_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1255_, v___x_1288_);
v___x_1290_ = lean_string_append(v___x_1287_, v___x_1289_);
lean_dec_ref(v___x_1289_);
v___x_1291_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__3));
v___x_1292_ = lean_string_append(v___x_1290_, v___x_1291_);
v___x_1293_ = lean_mk_io_user_error(v___x_1292_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 1);
lean_ctor_set(v___x_1260_, 0, v___x_1293_);
v___x_1295_ = v___x_1260_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object* v_mapRef_1298_, lean_object* v_aliasName_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1298_, v_aliasName_1299_);
lean_dec(v_mapRef_1298_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object* v_00_u03b1_1302_, lean_object* v_mapRef_1303_, lean_object* v_aliasName_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1303_, v_aliasName_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_mapRef_1308_, lean_object* v_aliasName_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_Parser_getConstAlias(v_00_u03b1_1307_, v_mapRef_1308_, v_aliasName_1309_);
lean_dec(v_mapRef_1308_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object* v_mapRef_1313_, lean_object* v_aliasName_1314_){
_start:
{
lean_object* v___x_1316_; lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1346_; 
v___x_1316_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1313_, v_aliasName_1314_);
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1346_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1346_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
if (lean_obj_tag(v_a_1317_) == 0)
{
lean_object* v___x_1321_; uint8_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1321_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1322_ = 1;
v___x_1323_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1314_, v___x_1322_);
v___x_1324_ = lean_string_append(v___x_1321_, v___x_1323_);
lean_dec_ref(v___x_1323_);
v___x_1325_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1326_ = lean_string_append(v___x_1324_, v___x_1325_);
v___x_1327_ = lean_mk_io_user_error(v___x_1326_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 1);
lean_ctor_set(v___x_1319_, 0, v___x_1327_);
v___x_1329_ = v___x_1319_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
else
{
lean_object* v_val_1331_; 
v_val_1331_ = lean_ctor_get(v_a_1317_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v_a_1317_, 1);
if (lean_obj_tag(v_val_1331_) == 1)
{
lean_object* v_p_1332_; lean_object* v___x_1334_; 
lean_dec(v_aliasName_1314_);
v_p_1332_ = lean_ctor_get(v_val_1331_, 0);
lean_inc(v_p_1332_);
lean_dec_ref_known(v_val_1331_, 1);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v_p_1332_);
v___x_1334_ = v___x_1319_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_p_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
lean_object* v___x_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
lean_dec(v_val_1331_);
v___x_1336_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1337_ = 1;
v___x_1338_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1314_, v___x_1337_);
v___x_1339_ = lean_string_append(v___x_1336_, v___x_1338_);
lean_dec_ref(v___x_1338_);
v___x_1340_ = ((lean_object*)(l_Lean_Parser_getUnaryAlias___redArg___closed__0));
v___x_1341_ = lean_string_append(v___x_1339_, v___x_1340_);
v___x_1342_ = lean_mk_io_user_error(v___x_1341_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 1);
lean_ctor_set(v___x_1319_, 0, v___x_1342_);
v___x_1344_ = v___x_1319_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object* v_mapRef_1347_, lean_object* v_aliasName_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1347_, v_aliasName_1348_);
lean_dec(v_mapRef_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object* v_00_u03b1_1351_, lean_object* v_mapRef_1352_, lean_object* v_aliasName_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1352_, v_aliasName_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_mapRef_1357_, lean_object* v_aliasName_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Parser_getUnaryAlias(v_00_u03b1_1356_, v_mapRef_1357_, v_aliasName_1358_);
lean_dec(v_mapRef_1357_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object* v_mapRef_1362_, lean_object* v_aliasName_1363_){
_start:
{
lean_object* v___x_1365_; lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1395_; 
v___x_1365_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1362_, v_aliasName_1363_);
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1395_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1395_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
if (lean_obj_tag(v_a_1366_) == 0)
{
lean_object* v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1370_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1371_ = 1;
v___x_1372_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1363_, v___x_1371_);
v___x_1373_ = lean_string_append(v___x_1370_, v___x_1372_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1375_ = lean_string_append(v___x_1373_, v___x_1374_);
v___x_1376_ = lean_mk_io_user_error(v___x_1375_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set_tag(v___x_1368_, 1);
lean_ctor_set(v___x_1368_, 0, v___x_1376_);
v___x_1378_ = v___x_1368_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
else
{
lean_object* v_val_1380_; 
v_val_1380_ = lean_ctor_get(v_a_1366_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v_a_1366_, 1);
if (lean_obj_tag(v_val_1380_) == 2)
{
lean_object* v_p_1381_; lean_object* v___x_1383_; 
lean_dec(v_aliasName_1363_);
v_p_1381_ = lean_ctor_get(v_val_1380_, 0);
lean_inc(v_p_1381_);
lean_dec_ref_known(v_val_1380_, 1);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v_p_1381_);
v___x_1383_ = v___x_1368_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_p_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
else
{
lean_object* v___x_1385_; uint8_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
lean_dec(v_val_1380_);
v___x_1385_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1386_ = 1;
v___x_1387_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1363_, v___x_1386_);
v___x_1388_ = lean_string_append(v___x_1385_, v___x_1387_);
lean_dec_ref(v___x_1387_);
v___x_1389_ = ((lean_object*)(l_Lean_Parser_getBinaryAlias___redArg___closed__0));
v___x_1390_ = lean_string_append(v___x_1388_, v___x_1389_);
v___x_1391_ = lean_mk_io_user_error(v___x_1390_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set_tag(v___x_1368_, 1);
lean_ctor_set(v___x_1368_, 0, v___x_1391_);
v___x_1393_ = v___x_1368_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg___boxed(lean_object* v_mapRef_1396_, lean_object* v_aliasName_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1396_, v_aliasName_1397_);
lean_dec(v_mapRef_1396_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object* v_00_u03b1_1400_, lean_object* v_mapRef_1401_, lean_object* v_aliasName_1402_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1401_, v_aliasName_1402_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___boxed(lean_object* v_00_u03b1_1405_, lean_object* v_mapRef_1406_, lean_object* v_aliasName_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Parser_getBinaryAlias(v_00_u03b1_1405_, v_mapRef_1406_, v_aliasName_1407_);
lean_dec(v_mapRef_1406_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = lean_box(1);
v___x_1418_ = lean_st_mk_ref(v___x_1417_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = lean_box(1);
v___x_1424_ = lean_st_mk_ref(v___x_1423_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(lean_object* v_t_1428_, lean_object* v_k_1429_, lean_object* v_fallback_1430_){
_start:
{
if (lean_obj_tag(v_t_1428_) == 0)
{
lean_object* v_k_1431_; lean_object* v_v_1432_; lean_object* v_l_1433_; lean_object* v_r_1434_; uint8_t v___x_1435_; 
v_k_1431_ = lean_ctor_get(v_t_1428_, 1);
v_v_1432_ = lean_ctor_get(v_t_1428_, 2);
v_l_1433_ = lean_ctor_get(v_t_1428_, 3);
v_r_1434_ = lean_ctor_get(v_t_1428_, 4);
v___x_1435_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1429_, v_k_1431_);
switch(v___x_1435_)
{
case 0:
{
v_t_1428_ = v_l_1433_;
goto _start;
}
case 1:
{
lean_inc(v_v_1432_);
return v_v_1432_;
}
default: 
{
v_t_1428_ = v_r_1434_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_1430_);
return v_fallback_1430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg___boxed(lean_object* v_t_1438_, lean_object* v_k_1439_, lean_object* v_fallback_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1438_, v_k_1439_, v_fallback_1440_);
lean_dec(v_fallback_1440_);
lean_dec(v_k_1439_);
lean_dec(v_t_1438_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo(lean_object* v_aliasName_1448_){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1450_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1451_ = lean_st_ref_get(v___x_1450_);
v___x_1452_ = ((lean_object*)(l_Lean_Parser_getParserAliasInfo___closed__1));
v___x_1453_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v___x_1451_, v_aliasName_1448_, v___x_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo___boxed(lean_object* v_aliasName_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_Parser_getParserAliasInfo(v_aliasName_1455_);
lean_dec(v_aliasName_1455_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(lean_object* v_00_u03b4_1458_, lean_object* v_t_1459_, lean_object* v_k_1460_, lean_object* v_fallback_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1459_, v_k_1460_, v_fallback_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___boxed(lean_object* v_00_u03b4_1463_, lean_object* v_t_1464_, lean_object* v_k_1465_, lean_object* v_fallback_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(v_00_u03b4_1463_, v_t_1464_, v_k_1465_, v_fallback_1466_);
lean_dec(v_fallback_1466_);
lean_dec(v_k_1465_);
lean_dec(v_t_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object* v_aliasName_1468_, lean_object* v_declName_1469_, lean_object* v_p_1470_, lean_object* v_kind_x3f_1471_, lean_object* v_info_1472_){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = l_Lean_Parser_parserAliasesRef;
lean_inc(v_aliasName_1468_);
v___x_1491_ = l_Lean_Parser_registerAliasCore___redArg(v___x_1490_, v_aliasName_1468_, v_p_1470_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_dec_ref_known(v___x_1491_, 1);
if (lean_obj_tag(v_kind_x3f_1471_) == 1)
{
lean_object* v_val_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_val_1492_ = lean_ctor_get(v_kind_x3f_1471_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v_kind_x3f_1471_, 1);
v___x_1493_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1494_ = lean_st_ref_take(v___x_1493_);
lean_inc(v_aliasName_1468_);
v___x_1495_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1468_, v_val_1492_, v___x_1494_);
v___x_1496_ = lean_st_ref_put(v___x_1493_, v___x_1495_);
goto v___jp_1474_;
}
else
{
lean_dec(v_kind_x3f_1471_);
goto v___jp_1474_;
}
}
else
{
lean_dec_ref(v_info_1472_);
lean_dec(v_kind_x3f_1471_);
lean_dec(v_declName_1469_);
lean_dec(v_aliasName_1468_);
return v___x_1491_;
}
v___jp_1474_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v_stackSz_x3f_1477_; uint8_t v_autoGroupArgs_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1488_; 
v___x_1475_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1476_ = lean_st_ref_take(v___x_1475_);
v_stackSz_x3f_1477_ = lean_ctor_get(v_info_1472_, 1);
v_autoGroupArgs_1478_ = lean_ctor_get_uint8(v_info_1472_, sizeof(void*)*2);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_info_1472_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v_info_1472_, 0);
lean_dec(v_unused_1489_);
v___x_1480_ = v_info_1472_;
v_isShared_1481_ = v_isSharedCheck_1488_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_stackSz_x3f_1477_);
lean_dec(v_info_1472_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1488_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v_declName_1469_);
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_declName_1469_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_stackSz_x3f_1477_);
lean_ctor_set_uint8(v_reuseFailAlloc_1487_, sizeof(void*)*2, v_autoGroupArgs_1478_);
v___x_1483_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1468_, v___x_1483_, v___x_1476_);
v___x_1485_ = lean_st_ref_put(v___x_1475_, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias___boxed(lean_object* v_aliasName_1497_, lean_object* v_declName_1498_, lean_object* v_p_1499_, lean_object* v_kind_x3f_1500_, lean_object* v_info_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Parser_registerAlias(v_aliasName_1497_, v_declName_1498_, v_p_1499_, v_kind_x3f_1500_, v_info_1501_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue___lam__0(lean_object* v_p_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_p_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0(lean_object* v_p_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v_p_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0(lean_object* v_p_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_p_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object* v_aliasName_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1534_; 
v___x_1518_ = l_Lean_Parser_parserAliasesRef;
v___x_1519_ = l_Lean_Parser_getAlias___redArg(v___x_1518_, v_aliasName_1516_);
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1534_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1534_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
if (lean_obj_tag(v_a_1520_) == 1)
{
uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
lean_dec_ref_known(v_a_1520_, 1);
v___x_1524_ = 1;
v___x_1525_ = lean_box(v___x_1524_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1525_);
v___x_1527_ = v___x_1522_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
else
{
uint8_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
lean_dec(v_a_1520_);
v___x_1529_ = 0;
v___x_1530_ = lean_box(v___x_1529_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1530_);
v___x_1532_ = v___x_1522_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object* v_aliasName_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_Parser_isParserAlias(v_aliasName_1535_);
lean_dec(v_aliasName_1535_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object* v_aliasName_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1540_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1541_ = lean_st_ref_get(v___x_1540_);
v___x_1542_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1541_, v_aliasName_1538_);
lean_dec(v___x_1541_);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f___boxed(lean_object* v_aliasName_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v_aliasName_1544_);
lean_dec(v_aliasName_1544_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object* v_aliasName_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = l_Lean_Parser_parserAliasesRef;
v___x_1550_ = lean_box(0);
v___x_1551_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1549_, v_aliasName_1547_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v___x_1551_, 0);
lean_dec(v_unused_1559_);
v___x_1553_ = v___x_1551_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v___x_1551_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1550_);
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1550_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
v_a_1560_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1551_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1551_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias___boxed(lean_object* v_aliasName_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_Parser_ensureUnaryParserAlias(v_aliasName_1568_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object* v_aliasName_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = l_Lean_Parser_parserAliasesRef;
v___x_1574_ = lean_box(0);
v___x_1575_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1573_, v_aliasName_1571_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v___x_1575_, 0);
lean_dec(v_unused_1583_);
v___x_1577_ = v___x_1575_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_dec(v___x_1575_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1574_);
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1574_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
v_a_1584_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1575_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1575_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias___boxed(lean_object* v_aliasName_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Parser_ensureBinaryParserAlias(v_aliasName_1592_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object* v_aliasName_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = l_Lean_Parser_parserAliasesRef;
v___x_1598_ = lean_box(0);
v___x_1599_ = l_Lean_Parser_getConstAlias___redArg(v___x_1597_, v_aliasName_1595_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v___x_1599_, 0);
lean_dec(v_unused_1607_);
v___x_1601_ = v___x_1599_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_dec(v___x_1599_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1598_);
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1598_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
v_a_1608_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1599_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1599_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias___boxed(lean_object* v_aliasName_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Parser_ensureConstantParserAlias(v_aliasName_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* v_constName_1627_, lean_object* v_compileParserDescr_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_env_1640_; lean_object* v_opts_1641_; uint8_t v___x_1642_; lean_object* v___x_1643_; 
v_env_1640_ = lean_ctor_get(v_a_1629_, 0);
v_opts_1641_ = lean_ctor_get(v_a_1629_, 1);
v___x_1642_ = 0;
lean_inc(v_constName_1627_);
lean_inc_ref(v_env_1640_);
v___x_1643_ = l_Lean_Environment_find_x3f(v_env_1640_, v_constName_1627_, v___x_1642_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1644_; uint8_t v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec_ref(v_compileParserDescr_1628_);
v___x_1644_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_1645_ = 1;
v___x_1646_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1627_, v___x_1645_);
v___x_1647_ = lean_string_append(v___x_1644_, v___x_1646_);
lean_dec_ref(v___x_1646_);
v___x_1648_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_1649_ = lean_string_append(v___x_1647_, v___x_1648_);
v___x_1650_ = lean_mk_io_user_error(v___x_1649_);
v___x_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
else
{
lean_object* v_val_1652_; lean_object* v___x_1653_; 
v_val_1652_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_val_1652_);
lean_dec_ref_known(v___x_1643_, 1);
v___x_1653_ = l_Lean_ConstantInfo_type(v_val_1652_);
lean_dec(v_val_1652_);
if (lean_obj_tag(v___x_1653_) == 4)
{
lean_object* v_declName_1654_; 
v_declName_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_declName_1654_);
lean_dec_ref_known(v___x_1653_, 2);
if (lean_obj_tag(v_declName_1654_) == 1)
{
lean_object* v_pre_1655_; 
v_pre_1655_ = lean_ctor_get(v_declName_1654_, 0);
lean_inc(v_pre_1655_);
if (lean_obj_tag(v_pre_1655_) == 1)
{
lean_object* v_pre_1656_; 
v_pre_1656_ = lean_ctor_get(v_pre_1655_, 0);
switch(lean_obj_tag(v_pre_1656_))
{
case 1:
{
lean_object* v_pre_1657_; 
lean_inc_ref(v_pre_1656_);
lean_dec_ref(v_compileParserDescr_1628_);
v_pre_1657_ = lean_ctor_get(v_pre_1656_, 0);
if (lean_obj_tag(v_pre_1657_) == 0)
{
lean_object* v_str_1658_; lean_object* v_str_1659_; lean_object* v_str_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v_str_1658_ = lean_ctor_get(v_declName_1654_, 1);
lean_inc_ref(v_str_1658_);
lean_dec_ref_known(v_declName_1654_, 2);
v_str_1659_ = lean_ctor_get(v_pre_1655_, 1);
lean_inc_ref(v_str_1659_);
lean_dec_ref_known(v_pre_1655_, 2);
v_str_1660_ = lean_ctor_get(v_pre_1656_, 1);
lean_inc_ref(v_str_1660_);
lean_dec_ref_known(v_pre_1656_, 2);
v___x_1661_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1662_ = lean_string_dec_eq(v_str_1660_, v___x_1661_);
lean_dec_ref(v_str_1660_);
if (v___x_1662_ == 0)
{
lean_dec_ref(v_str_1659_);
lean_dec_ref(v_str_1658_);
goto v___jp_1631_;
}
else
{
lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_1664_ = lean_string_dec_eq(v_str_1659_, v___x_1663_);
lean_dec_ref(v_str_1659_);
if (v___x_1664_ == 0)
{
lean_dec_ref(v_str_1658_);
goto v___jp_1631_;
}
else
{
lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1665_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_1666_ = lean_string_dec_eq(v_str_1658_, v___x_1665_);
if (v___x_1666_ == 0)
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_string_dec_eq(v_str_1658_, v___x_1663_);
lean_dec_ref(v_str_1658_);
if (v___x_1667_ == 0)
{
goto v___jp_1631_;
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = l_Lean_Environment_evalConst___redArg(v_env_1640_, v_opts_1641_, v_constName_1627_, v___x_1667_);
lean_dec(v_constName_1627_);
v___x_1669_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1668_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1679_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1679_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1679_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1674_ = lean_box(v___x_1667_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v_a_1670_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1675_);
v___x_1677_ = v___x_1672_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
v_a_1680_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1669_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1669_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_dec_ref(v_str_1658_);
v___x_1688_ = l_Lean_Environment_evalConst___redArg(v_env_1640_, v_opts_1641_, v_constName_1627_, v___x_1666_);
lean_dec(v_constName_1627_);
v___x_1689_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1688_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1699_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1699_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1699_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1694_ = lean_box(v___x_1642_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v_a_1690_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1695_);
v___x_1697_ = v___x_1692_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
v_a_1700_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1689_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1689_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1656_, 2);
lean_dec_ref_known(v_pre_1655_, 2);
lean_dec_ref_known(v_declName_1654_, 2);
goto v___jp_1631_;
}
}
case 0:
{
lean_object* v_str_1708_; lean_object* v_str_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v_str_1708_ = lean_ctor_get(v_declName_1654_, 1);
lean_inc_ref(v_str_1708_);
lean_dec_ref_known(v_declName_1654_, 2);
v_str_1709_ = lean_ctor_get(v_pre_1655_, 1);
lean_inc_ref(v_str_1709_);
lean_dec_ref_known(v_pre_1655_, 2);
v___x_1710_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1711_ = lean_string_dec_eq(v_str_1709_, v___x_1710_);
lean_dec_ref(v_str_1709_);
if (v___x_1711_ == 0)
{
lean_dec_ref(v_str_1708_);
lean_dec_ref(v_compileParserDescr_1628_);
goto v___jp_1631_;
}
else
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_1713_ = lean_string_dec_eq(v_str_1708_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_1715_ = lean_string_dec_eq(v_str_1708_, v___x_1714_);
lean_dec_ref(v_str_1708_);
if (v___x_1715_ == 0)
{
lean_dec_ref(v_compileParserDescr_1628_);
goto v___jp_1631_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = l_Lean_Environment_evalConst___redArg(v_env_1640_, v_opts_1641_, v_constName_1627_, v___x_1715_);
lean_dec(v_constName_1627_);
v___x_1717_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1716_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
lean_inc_ref(v_a_1629_);
v___x_1719_ = lean_apply_3(v_compileParserDescr_1628_, v_a_1718_, v_a_1629_, lean_box(0));
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1729_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1729_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1729_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1724_ = lean_box(v___x_1713_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
lean_ctor_set(v___x_1725_, 1, v_a_1720_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1725_);
v___x_1727_ = v___x_1722_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
v_a_1730_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1719_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1719_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec_ref(v_compileParserDescr_1628_);
v_a_1738_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1717_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1717_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec_ref(v_str_1708_);
v___x_1746_ = l_Lean_Environment_evalConst___redArg(v_env_1640_, v_opts_1641_, v_constName_1627_, v___x_1713_);
lean_dec(v_constName_1627_);
v___x_1747_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1746_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
lean_inc_ref(v_a_1629_);
v___x_1749_ = lean_apply_3(v_compileParserDescr_1628_, v_a_1748_, v_a_1629_, lean_box(0));
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1759_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1759_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1759_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1754_ = lean_box(v___x_1713_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v_a_1750_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1755_);
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
v_a_1760_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1749_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1749_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v_compileParserDescr_1628_);
v_a_1768_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1747_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1747_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_pre_1655_, 2);
lean_dec_ref_known(v_declName_1654_, 2);
lean_dec_ref(v_compileParserDescr_1628_);
goto v___jp_1631_;
}
}
}
else
{
lean_dec_ref_known(v_declName_1654_, 2);
lean_dec(v_pre_1655_);
lean_dec_ref(v_compileParserDescr_1628_);
goto v___jp_1631_;
}
}
else
{
lean_dec(v_declName_1654_);
lean_dec_ref(v_compileParserDescr_1628_);
goto v___jp_1631_;
}
}
else
{
lean_dec_ref(v___x_1653_);
lean_dec_ref(v_compileParserDescr_1628_);
goto v___jp_1631_;
}
}
v___jp_1631_:
{
lean_object* v___x_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1632_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__0));
v___x_1633_ = 1;
v___x_1634_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1627_, v___x_1633_);
v___x_1635_ = lean_string_append(v___x_1632_, v___x_1634_);
lean_dec_ref(v___x_1634_);
v___x_1636_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1));
v___x_1637_ = lean_string_append(v___x_1635_, v___x_1636_);
v___x_1638_ = lean_mk_io_user_error(v___x_1637_);
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object* v_constName_1776_, lean_object* v_compileParserDescr_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1776_, v_compileParserDescr_1777_, v_a_1778_);
lean_dec_ref(v_a_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed(lean_object* v_categories_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1781_, v_a_1782_, v_a_1783_);
lean_dec_ref(v_a_1783_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(lean_object* v_categories_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
switch(lean_obj_tag(v_a_1787_))
{
case 0:
{
lean_object* v_name_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_dec_ref(v_categories_1786_);
v_name_1790_ = lean_ctor_get(v_a_1787_, 0);
lean_inc(v_name_1790_);
lean_dec_ref_known(v_a_1787_, 1);
v___x_1791_ = l_Lean_Parser_parserAliasesRef;
v___x_1792_ = l_Lean_Parser_getConstAlias___redArg(v___x_1791_, v_name_1790_);
return v___x_1792_;
}
case 1:
{
lean_object* v_name_1793_; lean_object* v_p_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_name_1793_ = lean_ctor_get(v_a_1787_, 0);
lean_inc(v_name_1793_);
v_p_1794_ = lean_ctor_get(v_a_1787_, 1);
lean_inc_ref(v_p_1794_);
lean_dec_ref_known(v_a_1787_, 2);
v___x_1795_ = l_Lean_Parser_parserAliasesRef;
v___x_1796_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1795_, v_name_1793_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1786_, v_p_1794_, v_a_1788_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1807_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1807_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1807_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = lean_apply_1(v_a_1797_, v_a_1799_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1803_);
v___x_1805_ = v___x_1801_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
else
{
lean_dec(v_a_1797_);
return v___x_1798_;
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec_ref(v_p_1794_);
lean_dec_ref(v_categories_1786_);
v_a_1808_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1796_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1796_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
case 2:
{
lean_object* v_name_1816_; lean_object* v_p_u2081_1817_; lean_object* v_p_u2082_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v_name_1816_ = lean_ctor_get(v_a_1787_, 0);
lean_inc(v_name_1816_);
v_p_u2081_1817_ = lean_ctor_get(v_a_1787_, 1);
lean_inc_ref(v_p_u2081_1817_);
v_p_u2082_1818_ = lean_ctor_get(v_a_1787_, 2);
lean_inc_ref(v_p_u2082_1818_);
lean_dec_ref_known(v_a_1787_, 3);
v___x_1819_ = l_Lean_Parser_parserAliasesRef;
v___x_1820_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1819_, v_name_1816_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1822_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1820_, 1);
lean_inc_ref(v_categories_1786_);
v___x_1822_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1786_, v_p_u2081_1817_, v_a_1788_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1824_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v___x_1824_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1786_, v_p_u2082_1818_, v_a_1788_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1833_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1833_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1833_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1829_ = lean_apply_2(v_a_1821_, v_a_1823_, v_a_1825_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1829_);
v___x_1831_ = v___x_1827_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
else
{
lean_dec(v_a_1823_);
lean_dec(v_a_1821_);
return v___x_1824_;
}
}
else
{
lean_dec(v_a_1821_);
lean_dec_ref(v_p_u2082_1818_);
lean_dec_ref(v_categories_1786_);
return v___x_1822_;
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v_p_u2082_1818_);
lean_dec_ref(v_p_u2081_1817_);
lean_dec_ref(v_categories_1786_);
v_a_1834_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1820_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1820_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
case 3:
{
lean_object* v_kind_1842_; lean_object* v_prec_1843_; lean_object* v_p_1844_; lean_object* v___x_1845_; 
v_kind_1842_ = lean_ctor_get(v_a_1787_, 0);
lean_inc(v_kind_1842_);
v_prec_1843_ = lean_ctor_get(v_a_1787_, 1);
lean_inc(v_prec_1843_);
v_p_1844_ = lean_ctor_get(v_a_1787_, 2);
lean_inc_ref(v_p_1844_);
lean_dec_ref_known(v_a_1787_, 3);
v___x_1845_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1786_, v_p_1844_, v_a_1788_);
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
v___x_1850_ = l_Lean_Parser_leadingNode(v_kind_1842_, v_prec_1843_, v_a_1846_);
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
lean_dec(v_prec_1843_);
lean_dec(v_kind_1842_);
return v___x_1845_;
}
}
case 4:
{
lean_object* v_kind_1855_; lean_object* v_prec_1856_; lean_object* v_lhsPrec_1857_; lean_object* v_p_1858_; lean_object* v___x_1859_; 
v_kind_1855_ = lean_ctor_get(v_a_1787_, 0);
lean_inc(v_kind_1855_);
v_prec_1856_ = lean_ctor_get(v_a_1787_, 1);
lean_inc(v_prec_1856_);
v_lhsPrec_1857_ = lean_ctor_get(v_a_1787_, 2);
lean_inc(v_lhsPrec_1857_);
v_p_1858_ = lean_ctor_get(v_a_1787_, 3);
lean_inc_ref(v_p_1858_);
lean_dec_ref_known(v_a_1787_, 4);
v___x_1859_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1786_, v_p_1858_, v_a_1788_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1868_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1868_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1868_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1864_ = l_Lean_Parser_trailingNode(v_kind_1855_, v_prec_1856_, v_lhsPrec_1857_, v_a_1860_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1864_);
v___x_1866_ = v___x_1862_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
else
{
lean_dec(v_lhsPrec_1857_);
lean_dec(v_prec_1856_);
lean_dec(v_kind_1855_);
return v___x_1859_;
}
}
case 5:
{
lean_object* v_val_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v_categories_1786_);
v_val_1869_ = lean_ctor_get(v_a_1787_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_a_1787_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1871_ = v_a_1787_;
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_val_1869_);
lean_dec(v_a_1787_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = l_Lean_Parser_symbol(v_val_1869_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1873_);
v___x_1875_ = v___x_1871_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
case 6:
{
lean_object* v_val_1878_; uint8_t v_includeIdent_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_dec_ref(v_categories_1786_);
v_val_1878_ = lean_ctor_get(v_a_1787_, 0);
lean_inc_ref(v_val_1878_);
v_includeIdent_1879_ = lean_ctor_get_uint8(v_a_1787_, sizeof(void*)*1);
lean_dec_ref_known(v_a_1787_, 1);
v___x_1880_ = l_Lean_Parser_nonReservedSymbol(v_val_1878_, v_includeIdent_1879_);
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
return v___x_1881_;
}
case 7:
{
lean_object* v_catName_1882_; lean_object* v_rbp_1883_; lean_object* v___x_1884_; 
v_catName_1882_ = lean_ctor_get(v_a_1787_, 0);
lean_inc(v_catName_1882_);
v_rbp_1883_ = lean_ctor_get(v_a_1787_, 1);
lean_inc(v_rbp_1883_);
lean_dec_ref_known(v_a_1787_, 2);
v___x_1884_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_1786_, v_catName_1882_);
lean_dec_ref(v_categories_1786_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec(v_rbp_1883_);
v___x_1885_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_1882_);
v___x_1886_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1885_);
return v___x_1886_;
}
else
{
lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1894_; 
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; 
v_unused_1895_ = lean_ctor_get(v___x_1884_, 0);
lean_dec(v_unused_1895_);
v___x_1888_ = v___x_1884_;
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
else
{
lean_dec(v___x_1884_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = l_Lean_Parser_categoryParser(v_catName_1882_, v_rbp_1883_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1890_);
v___x_1892_ = v___x_1888_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
case 8:
{
lean_object* v_declName_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_declName_1896_ = lean_ctor_get(v_a_1787_, 0);
lean_inc(v_declName_1896_);
lean_dec_ref_known(v_a_1787_, 1);
v___x_1897_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed), 4, 1);
lean_closure_set(v___x_1897_, 0, v_categories_1786_);
v___x_1898_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_declName_1896_, v___x_1897_, v_a_1788_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1907_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1907_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1907_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v_snd_1903_; lean_object* v___x_1905_; 
v_snd_1903_ = lean_ctor_get(v_a_1899_, 1);
lean_inc(v_snd_1903_);
lean_dec(v_a_1899_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v_snd_1903_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_snd_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
v_a_1908_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1898_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1898_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
case 9:
{
lean_object* v_name_1916_; lean_object* v_kind_1917_; lean_object* v_p_1918_; lean_object* v___x_1919_; 
v_name_1916_ = lean_ctor_get(v_a_1787_, 0);
lean_inc_ref(v_name_1916_);
v_kind_1917_ = lean_ctor_get(v_a_1787_, 1);
lean_inc(v_kind_1917_);
v_p_1918_ = lean_ctor_get(v_a_1787_, 2);
lean_inc_ref(v_p_1918_);
lean_dec_ref_known(v_a_1787_, 3);
v___x_1919_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1786_, v_p_1918_, v_a_1788_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1930_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1930_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1930_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
uint8_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1924_ = 1;
lean_inc(v_kind_1917_);
v___x_1925_ = l_Lean_Parser_nodeWithAntiquot(v_name_1916_, v_kind_1917_, v_a_1920_, v___x_1924_);
v___x_1926_ = l_Lean_Parser_withCache(v_kind_1917_, v___x_1925_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1926_);
v___x_1928_ = v___x_1922_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
lean_dec(v_kind_1917_);
lean_dec_ref(v_name_1916_);
return v___x_1919_;
}
}
case 10:
{
lean_object* v_p_1931_; lean_object* v_sep_1932_; lean_object* v_psep_1933_; uint8_t v_allowTrailingSep_1934_; lean_object* v___x_1935_; 
v_p_1931_ = lean_ctor_get(v_a_1787_, 0);
lean_inc_ref(v_p_1931_);
v_sep_1932_ = lean_ctor_get(v_a_1787_, 1);
lean_inc_ref(v_sep_1932_);
v_psep_1933_ = lean_ctor_get(v_a_1787_, 2);
lean_inc_ref(v_psep_1933_);
v_allowTrailingSep_1934_ = lean_ctor_get_uint8(v_a_1787_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1787_, 3);
lean_inc_ref(v_categories_1786_);
v___x_1935_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1786_, v_p_1931_, v_a_1788_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1786_, v_psep_1933_, v_a_1788_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1946_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1946_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1946_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = l_Lean_Parser_sepBy(v_a_1936_, v_sep_1932_, v_a_1938_, v_allowTrailingSep_1934_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1942_);
v___x_1944_ = v___x_1940_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
else
{
lean_dec(v_a_1936_);
lean_dec_ref(v_sep_1932_);
return v___x_1937_;
}
}
else
{
lean_dec_ref(v_psep_1933_);
lean_dec_ref(v_sep_1932_);
lean_dec_ref(v_categories_1786_);
return v___x_1935_;
}
}
case 11:
{
lean_object* v_p_1947_; lean_object* v_sep_1948_; lean_object* v_psep_1949_; uint8_t v_allowTrailingSep_1950_; lean_object* v___x_1951_; 
v_p_1947_ = lean_ctor_get(v_a_1787_, 0);
lean_inc_ref(v_p_1947_);
v_sep_1948_ = lean_ctor_get(v_a_1787_, 1);
lean_inc_ref(v_sep_1948_);
v_psep_1949_ = lean_ctor_get(v_a_1787_, 2);
lean_inc_ref(v_psep_1949_);
v_allowTrailingSep_1950_ = lean_ctor_get_uint8(v_a_1787_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1787_, 3);
lean_inc_ref(v_categories_1786_);
v___x_1951_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1786_, v_p_1947_, v_a_1788_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1786_, v_psep_1949_, v_a_1788_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1962_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1956_ = v___x_1953_;
v_isShared_1957_ = v_isSharedCheck_1962_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1962_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1958_ = l_Lean_Parser_sepBy1(v_a_1952_, v_sep_1948_, v_a_1954_, v_allowTrailingSep_1950_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1958_);
v___x_1960_ = v___x_1956_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
else
{
lean_dec(v_a_1952_);
lean_dec_ref(v_sep_1948_);
return v___x_1953_;
}
}
else
{
lean_dec_ref(v_psep_1949_);
lean_dec_ref(v_sep_1948_);
lean_dec_ref(v_categories_1786_);
return v___x_1951_;
}
}
default: 
{
lean_object* v_val_1963_; lean_object* v_asciiVal_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_dec_ref(v_categories_1786_);
v_val_1963_ = lean_ctor_get(v_a_1787_, 0);
lean_inc_ref(v_val_1963_);
v_asciiVal_1964_ = lean_ctor_get(v_a_1787_, 1);
lean_inc_ref(v_asciiVal_1964_);
lean_dec_ref_known(v_a_1787_, 2);
v___x_1965_ = l_Lean_Parser_unicodeSymbol___redArg(v_val_1963_, v_asciiVal_1964_);
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object* v_categories_1967_, lean_object* v_d_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1967_, v_d_1968_, v_a_1969_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object* v_categories_1972_, lean_object* v_d_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_Parser_compileParserDescr(v_categories_1972_, v_d_1973_, v_a_1974_);
lean_dec_ref(v_a_1974_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0(lean_object* v_categories_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1977_, v___y_1978_, v___y_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0___boxed(lean_object* v_categories_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Parser_mkParserOfConstant___lam__0(v_categories_1982_, v___y_1983_, v___y_1984_);
lean_dec_ref(v___y_1984_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* v_categories_1987_, lean_object* v_constName_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v___f_1991_; lean_object* v___x_1992_; 
v___f_1991_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserOfConstant___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1991_, 0, v_categories_1987_);
v___x_1992_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1988_, v___f_1991_, v_a_1989_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___boxed(lean_object* v_categories_1993_, lean_object* v_constName_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_Parser_mkParserOfConstant(v_categories_1993_, v_constName_1994_, v_a_1995_);
lean_dec_ref(v_a_1995_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = lean_box(0);
v___x_2000_ = lean_st_mk_ref(v___x_1999_);
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object* v_a_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object* v_hook_2004_){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2006_ = l_Lean_Parser_parserAttributeHooks;
v___x_2007_ = lean_st_ref_take(v___x_2006_);
v___x_2008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2008_, 0, v_hook_2004_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = lean_st_ref_put(v___x_2006_, v___x_2008_);
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook___boxed(lean_object* v_hook_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_Parser_registerParserAttributeHook(v_hook_2011_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(lean_object* v_catName_2014_, lean_object* v_declName_2015_, uint8_t v_builtin_2016_, lean_object* v_as_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
if (lean_obj_tag(v_as_2017_) == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec(v_declName_2015_);
lean_dec(v_catName_2014_);
v___x_2021_ = lean_box(0);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
else
{
lean_object* v_head_2023_; lean_object* v_tail_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v_head_2023_ = lean_ctor_get(v_as_2017_, 0);
lean_inc(v_head_2023_);
v_tail_2024_ = lean_ctor_get(v_as_2017_, 1);
lean_inc(v_tail_2024_);
lean_dec_ref_known(v_as_2017_, 2);
v___x_2025_ = lean_box(v_builtin_2016_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
lean_inc(v_declName_2015_);
lean_inc(v_catName_2014_);
v___x_2026_ = lean_apply_6(v_head_2023_, v_catName_2014_, v_declName_2015_, v___x_2025_, v___y_2018_, v___y_2019_, lean_box(0));
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_dec_ref_known(v___x_2026_, 1);
v_as_2017_ = v_tail_2024_;
goto _start;
}
else
{
lean_dec(v_tail_2024_);
lean_dec(v_declName_2015_);
lean_dec(v_catName_2014_);
return v___x_2026_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0___boxed(lean_object* v_catName_2028_, lean_object* v_declName_2029_, lean_object* v_builtin_2030_, lean_object* v_as_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v_builtin_boxed_2035_; lean_object* v_res_2036_; 
v_builtin_boxed_2035_ = lean_unbox(v_builtin_2030_);
v_res_2036_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2028_, v_declName_2029_, v_builtin_boxed_2035_, v_as_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object* v_catName_2037_, lean_object* v_declName_2038_, uint8_t v_builtin_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2043_ = l_Lean_Parser_parserAttributeHooks;
v___x_2044_ = lean_st_ref_get(v___x_2043_);
v___x_2045_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2037_, v_declName_2038_, v_builtin_2039_, v___x_2044_, v_a_2040_, v_a_2041_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object* v_catName_2046_, lean_object* v_declName_2047_, lean_object* v_builtin_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
uint8_t v_builtin_boxed_2052_; lean_object* v_res_2053_; 
v_builtin_boxed_2052_ = lean_unbox(v_builtin_2048_);
v_res_2053_ = l_Lean_Parser_runParserAttributeHooks(v_catName_2046_, v_declName_2047_, v_builtin_boxed_2052_, v_a_2049_, v_a_2050_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2054_, lean_object* v_decl_2055_, lean_object* v_stx_2056_, uint8_t v_x_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2056_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2061_) == 0)
{
uint8_t v___x_2062_; lean_object* v___x_2063_; 
lean_dec_ref_known(v___x_2061_, 1);
v___x_2062_ = 1;
v___x_2063_ = l_Lean_Parser_runParserAttributeHooks(v___x_2054_, v_decl_2055_, v___x_2062_, v___y_2058_, v___y_2059_);
return v___x_2063_;
}
else
{
lean_dec(v_decl_2055_);
lean_dec(v___x_2054_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2064_, lean_object* v_decl_2065_, lean_object* v_stx_2066_, lean_object* v_x_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
uint8_t v_x_1092__boxed_2071_; lean_object* v_res_2072_; 
v_x_1092__boxed_2071_ = lean_unbox(v_x_2067_);
v_res_2072_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2064_, v_decl_2065_, v_stx_2066_, v_x_1092__boxed_2071_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
return v_res_2072_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
return v___x_2074_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2076_ = lean_unsigned_to_nat(0u);
v___x_2077_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
lean_ctor_set(v___x_2077_, 2, v___x_2076_);
lean_ctor_set(v___x_2077_, 3, v___x_2076_);
lean_ctor_set(v___x_2077_, 4, v___x_2075_);
lean_ctor_set(v___x_2077_, 5, v___x_2075_);
lean_ctor_set(v___x_2077_, 6, v___x_2075_);
lean_ctor_set(v___x_2077_, 7, v___x_2075_);
lean_ctor_set(v___x_2077_, 8, v___x_2075_);
lean_ctor_set(v___x_2077_, 9, v___x_2075_);
lean_ctor_set(v___x_2077_, 10, v___x_2075_);
return v___x_2077_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_unsigned_to_nat(32u);
v___x_2079_ = lean_mk_empty_array_with_capacity(v___x_2078_);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2081_ = ((size_t)5ULL);
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = lean_unsigned_to_nat(32u);
v___x_2084_ = lean_mk_empty_array_with_capacity(v___x_2083_);
v___x_2085_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_2086_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v___x_2084_);
lean_ctor_set(v___x_2086_, 2, v___x_2082_);
lean_ctor_set(v___x_2086_, 3, v___x_2082_);
lean_ctor_set_usize(v___x_2086_, 4, v___x_2081_);
return v___x_2086_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2087_ = lean_box(1);
v___x_2088_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2089_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___x_2088_);
lean_ctor_set(v___x_2090_, 2, v___x_2087_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___x_2095_; lean_object* v_toCold_2096_; lean_object* v_env_2097_; lean_object* v_options_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2095_ = lean_st_ref_get(v___y_2093_);
v_toCold_2096_ = lean_ctor_get(v___y_2092_, 0);
v_env_2097_ = lean_ctor_get(v___x_2095_, 0);
lean_inc_ref(v_env_2097_);
lean_dec(v___x_2095_);
v_options_2098_ = lean_ctor_get(v_toCold_2096_, 2);
v___x_2099_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_2098_);
v___x_2101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2101_, 0, v_env_2097_);
lean_ctor_set(v___x_2101_, 1, v___x_2099_);
lean_ctor_set(v___x_2101_, 2, v___x_2100_);
lean_ctor_set(v___x_2101_, 3, v_options_2098_);
v___x_2102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
lean_ctor_set(v___x_2102_, 1, v_msgData_2091_);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_ref_2113_; lean_object* v___x_2114_; lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2123_; 
v_ref_2113_ = lean_ctor_get(v___y_2110_, 2);
v___x_2114_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msg_2109_, v___y_2110_, v___y_2111_);
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
lean_inc(v_ref_2113_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v_ref_2113_);
lean_ctor_set(v___x_2119_, 1, v_a_2115_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set_tag(v___x_2117_, 1);
lean_ctor_set(v___x_2117_, 0, v___x_2119_);
v___x_2121_ = v___x_2117_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2128_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2131_ = l_Lean_stringToMessageData(v___x_2130_);
return v___x_2131_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2134_ = l_Lean_stringToMessageData(v___x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2135_, lean_object* v_decl_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2140_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2141_ = l_Lean_MessageData_ofName(v___x_2135_);
v___x_2142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2140_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2142_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2144_, v___y_2137_, v___y_2138_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2146_, lean_object* v_decl_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2146_, v_decl_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v_decl_2147_);
return v_res_2151_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = lean_unsigned_to_nat(3646333153u);
v___x_2195_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2196_ = l_Lean_Name_num___override(v___x_2195_, v___x_2194_);
return v___x_2196_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2199_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2200_ = l_Lean_Name_str___override(v___x_2199_, v___x_2198_);
return v___x_2200_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2203_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2204_ = l_Lean_Name_str___override(v___x_2203_, v___x_2202_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = lean_unsigned_to_nat(2u);
v___x_2206_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2207_ = l_Lean_Name_num___override(v___x_2206_, v___x_2205_);
return v___x_2207_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2214_ = 0;
v___x_2215_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2216_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2217_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2218_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v___x_2216_);
lean_ctor_set(v___x_2218_, 2, v___x_2215_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*3, v___x_2214_);
return v___x_2218_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2219_; lean_object* v___f_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___f_2219_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___f_2220_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2221_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___f_2220_);
lean_ctor_set(v___x_2222_, 2, v___f_2219_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2225_ = l_Lean_registerBuiltinAttribute(v___x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2228_, lean_object* v_msg_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2229_, v___y_2230_, v___y_2231_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2234_, lean_object* v_msg_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(v_00_u03b1_2234_, v_msg_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2240_, lean_object* v_decl_2241_, lean_object* v_stx_2242_, uint8_t v_x_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2242_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2247_) == 0)
{
uint8_t v___x_2248_; lean_object* v___x_2249_; 
lean_dec_ref_known(v___x_2247_, 1);
v___x_2248_ = 0;
v___x_2249_ = l_Lean_Parser_runParserAttributeHooks(v___x_2240_, v_decl_2241_, v___x_2248_, v___y_2244_, v___y_2245_);
return v___x_2249_;
}
else
{
lean_dec(v_decl_2241_);
lean_dec(v___x_2240_);
return v___x_2247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2250_, lean_object* v_decl_2251_, lean_object* v_stx_2252_, lean_object* v_x_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
uint8_t v_x_212__boxed_2257_; lean_object* v_res_2258_; 
v_x_212__boxed_2257_ = lean_unbox(v_x_2253_);
v_res_2258_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2250_, v_decl_2251_, v_stx_2252_, v_x_212__boxed_2257_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
return v_res_2258_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = lean_unsigned_to_nat(3789407938u);
v___x_2262_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2263_ = l_Lean_Name_num___override(v___x_2262_, v___x_2261_);
return v___x_2263_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2265_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2266_ = l_Lean_Name_str___override(v___x_2265_, v___x_2264_);
return v___x_2266_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2267_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2268_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2269_ = l_Lean_Name_str___override(v___x_2268_, v___x_2267_);
return v___x_2269_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = lean_unsigned_to_nat(2u);
v___x_2271_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2272_ = l_Lean_Name_num___override(v___x_2271_, v___x_2270_);
return v___x_2272_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2279_ = 0;
v___x_2280_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2281_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2282_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2283_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
lean_ctor_set(v___x_2283_, 1, v___x_2281_);
lean_ctor_set(v___x_2283_, 2, v___x_2280_);
lean_ctor_set_uint8(v___x_2283_, sizeof(void*)*3, v___x_2279_);
return v___x_2283_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2284_; lean_object* v___f_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___f_2284_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___f_2285_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2286_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v___f_2285_);
lean_ctor_set(v___x_2287_, 2, v___f_2284_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2290_ = l_Lean_registerBuiltinAttribute(v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v_a_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object* v_s_2293_, lean_object* v_x_2294_, lean_object* v_a_2295_){
_start:
{
switch(lean_obj_tag(v_x_2294_))
{
case 0:
{
lean_object* v_val_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v_s_2293_);
v_val_2297_ = lean_ctor_get(v_x_2294_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_x_2294_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2299_ = v_x_2294_;
v_isShared_2300_ = v_isSharedCheck_2305_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_val_2297_);
lean_dec(v_x_2294_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2305_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_val_2297_);
v___x_2302_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
}
}
case 1:
{
lean_object* v_val_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v_s_2293_);
v_val_2306_ = lean_ctor_get(v_x_2294_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_x_2294_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2308_ = v_x_2294_;
v_isShared_2309_ = v_isSharedCheck_2314_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_val_2306_);
lean_dec(v_x_2294_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2314_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_val_2306_);
v___x_2311_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
}
case 2:
{
lean_object* v_catName_2315_; lean_object* v_declName_2316_; uint8_t v_behavior_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v_s_2293_);
v_catName_2315_ = lean_ctor_get(v_x_2294_, 0);
v_declName_2316_ = lean_ctor_get(v_x_2294_, 1);
v_behavior_2317_ = lean_ctor_get_uint8(v_x_2294_, sizeof(void*)*2);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_x_2294_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2319_ = v_x_2294_;
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_declName_2316_);
lean_inc(v_catName_2315_);
lean_dec(v_x_2294_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_catName_2315_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_declName_2316_);
lean_ctor_set_uint8(v_reuseFailAlloc_2324_, sizeof(void*)*2, v_behavior_2317_);
v___x_2322_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
}
default: 
{
lean_object* v_catName_2326_; lean_object* v_declName_2327_; lean_object* v_prio_2328_; lean_object* v_categories_2329_; lean_object* v___x_2330_; 
v_catName_2326_ = lean_ctor_get(v_x_2294_, 0);
lean_inc(v_catName_2326_);
v_declName_2327_ = lean_ctor_get(v_x_2294_, 1);
lean_inc_n(v_declName_2327_, 2);
v_prio_2328_ = lean_ctor_get(v_x_2294_, 2);
lean_inc(v_prio_2328_);
lean_dec_ref_known(v_x_2294_, 3);
v_categories_2329_ = lean_ctor_get(v_s_2293_, 2);
lean_inc_ref(v_categories_2329_);
lean_dec_ref(v_s_2293_);
v___x_2330_ = l_Lean_Parser_mkParserOfConstant(v_categories_2329_, v_declName_2327_, v_a_2295_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2342_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2342_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2342_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v_fst_2335_; lean_object* v_snd_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; lean_object* v___x_2340_; 
v_fst_2335_ = lean_ctor_get(v_a_2331_, 0);
lean_inc(v_fst_2335_);
v_snd_2336_ = lean_ctor_get(v_a_2331_, 1);
lean_inc(v_snd_2336_);
lean_dec(v_a_2331_);
v___x_2337_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_2337_, 0, v_catName_2326_);
lean_ctor_set(v___x_2337_, 1, v_declName_2327_);
lean_ctor_set(v___x_2337_, 2, v_snd_2336_);
lean_ctor_set(v___x_2337_, 3, v_prio_2328_);
v___x_2338_ = lean_unbox(v_fst_2335_);
lean_dec(v_fst_2335_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*4, v___x_2338_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2337_);
v___x_2340_ = v___x_2333_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2337_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_prio_2328_);
lean_dec(v_declName_2327_);
lean_dec(v_catName_2326_);
v_a_2343_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2330_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2330_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object* v_s_2351_, lean_object* v_x_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(v_s_2351_, v_x_2352_, v_a_2353_);
lean_dec_ref(v_a_2353_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v_x_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v_a_2357_);
lean_inc_ref_n(v___x_2358_, 2);
v___x_2359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
lean_ctor_set(v___x_2359_, 2, v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_x_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v_x_2360_, v_a_2361_);
lean_dec_ref(v_x_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v___y_2363_){
_start:
{
lean_inc_ref(v___y_2363_);
return v___y_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v___y_2364_);
lean_dec_ref(v___y_2364_);
return v_res_2365_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2376_; lean_object* v___f_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___f_2376_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___f_2377_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2378_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2379_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2380_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2381_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed), 1, 0);
v___x_2382_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2383_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set(v___x_2383_, 1, v___x_2381_);
lean_ctor_set(v___x_2383_, 2, v___x_2380_);
lean_ctor_set(v___x_2383_, 3, v___x_2379_);
lean_ctor_set(v___x_2383_, 4, v___x_2378_);
lean_ctor_set(v___x_2383_, 5, v___f_2377_);
lean_ctor_set(v___x_2383_, 6, v___f_2376_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_);
v___x_2386_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object* v_env_2389_, lean_object* v_catName_2390_){
_start:
{
lean_object* v___x_2391_; lean_object* v_ext_2392_; lean_object* v_toEnvExtension_2393_; lean_object* v_asyncMode_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v_categories_2397_; lean_object* v___x_2398_; 
v___x_2391_ = l_Lean_Parser_parserExtension;
v_ext_2392_ = lean_ctor_get(v___x_2391_, 1);
v_toEnvExtension_2393_ = lean_ctor_get(v_ext_2392_, 0);
v_asyncMode_2394_ = lean_ctor_get(v_toEnvExtension_2393_, 2);
v___x_2395_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2396_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2395_, v___x_2391_, v_env_2389_, v_asyncMode_2394_);
v_categories_2397_ = lean_ctor_get(v___x_2396_, 2);
lean_inc_ref(v_categories_2397_);
lean_dec(v___x_2396_);
v___x_2398_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2397_, v_catName_2390_);
lean_dec_ref(v_categories_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object* v_env_2399_, lean_object* v_catName_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_Parser_getParserCategory_x3f(v_env_2399_, v_catName_2400_);
lean_dec(v_catName_2400_);
return v_res_2401_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object* v_env_2402_, lean_object* v_catName_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_Parser_getParserCategory_x3f(v_env_2402_, v_catName_2403_);
if (lean_obj_tag(v___x_2404_) == 0)
{
uint8_t v___x_2405_; 
v___x_2405_ = 0;
return v___x_2405_;
}
else
{
uint8_t v___x_2406_; 
lean_dec_ref_known(v___x_2404_, 1);
v___x_2406_ = 1;
return v___x_2406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object* v_env_2407_, lean_object* v_catName_2408_){
_start:
{
uint8_t v_res_2409_; lean_object* v_r_2410_; 
v_res_2409_ = l_Lean_Parser_isParserCategory(v_env_2407_, v_catName_2408_);
lean_dec(v_catName_2408_);
v_r_2410_ = lean_box(v_res_2409_);
return v_r_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object* v_env_2411_, lean_object* v_catName_2412_, lean_object* v_declName_2413_, uint8_t v_behavior_2414_){
_start:
{
uint8_t v___x_2415_; 
lean_inc_ref(v_env_2411_);
v___x_2415_ = l_Lean_Parser_isParserCategory(v_env_2411_, v_catName_2412_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2416_ = l_Lean_Parser_parserExtension;
v___x_2417_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2417_, 0, v_catName_2412_);
lean_ctor_set(v___x_2417_, 1, v_declName_2413_);
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*2, v_behavior_2414_);
v___x_2418_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2416_, v_env_2411_, v___x_2417_);
v___x_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
else
{
lean_object* v___x_2420_; 
lean_dec(v_declName_2413_);
lean_dec_ref(v_env_2411_);
v___x_2420_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_2412_);
return v___x_2420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* v_env_2421_, lean_object* v_catName_2422_, lean_object* v_declName_2423_, lean_object* v_behavior_2424_){
_start:
{
uint8_t v_behavior_boxed_2425_; lean_object* v_res_2426_; 
v_behavior_boxed_2425_ = lean_unbox(v_behavior_2424_);
v_res_2426_ = l_Lean_Parser_addParserCategory(v_env_2421_, v_catName_2422_, v_declName_2423_, v_behavior_boxed_2425_);
return v_res_2426_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object* v_env_2427_, lean_object* v_catName_2428_){
_start:
{
lean_object* v___x_2429_; lean_object* v_ext_2430_; lean_object* v_toEnvExtension_2431_; lean_object* v_asyncMode_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v_categories_2435_; lean_object* v___x_2436_; 
v___x_2429_ = l_Lean_Parser_parserExtension;
v_ext_2430_ = lean_ctor_get(v___x_2429_, 1);
v_toEnvExtension_2431_ = lean_ctor_get(v_ext_2430_, 0);
v_asyncMode_2432_ = lean_ctor_get(v_toEnvExtension_2431_, 2);
v___x_2433_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2434_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2433_, v___x_2429_, v_env_2427_, v_asyncMode_2432_);
v_categories_2435_ = lean_ctor_get(v___x_2434_, 2);
lean_inc_ref(v_categories_2435_);
lean_dec(v___x_2434_);
v___x_2436_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2435_, v_catName_2428_);
lean_dec_ref(v_categories_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
uint8_t v___x_2437_; 
v___x_2437_ = 0;
return v___x_2437_;
}
else
{
lean_object* v_val_2438_; uint8_t v_behavior_2439_; 
v_val_2438_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_val_2438_);
lean_dec_ref_known(v___x_2436_, 1);
v_behavior_2439_ = lean_ctor_get_uint8(v_val_2438_, sizeof(void*)*3);
lean_dec(v_val_2438_);
return v_behavior_2439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object* v_env_2440_, lean_object* v_catName_2441_){
_start:
{
uint8_t v_res_2442_; lean_object* v_r_2443_; 
v_res_2442_ = l_Lean_Parser_leadingIdentBehavior(v_env_2440_, v_catName_2441_);
lean_dec(v_catName_2441_);
v_r_2443_ = lean_box(v_res_2442_);
return v_r_2443_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(lean_object* v_x_2444_, lean_object* v_x_2445_){
_start:
{
if (lean_obj_tag(v_x_2445_) == 0)
{
return v_x_2444_;
}
else
{
lean_object* v_head_2446_; lean_object* v_tail_2447_; lean_object* v___x_2448_; 
v_head_2446_ = lean_ctor_get(v_x_2445_, 0);
lean_inc_n(v_head_2446_, 2);
v_tail_2447_ = lean_ctor_get(v_x_2445_, 1);
lean_inc(v_tail_2447_);
lean_dec_ref_known(v_x_2445_, 2);
v___x_2448_ = l_Lean_Data_Trie_insert___redArg(v_x_2444_, v_head_2446_, v_head_2446_);
lean_dec(v_head_2446_);
v_x_2444_ = v___x_2448_;
v_x_2445_ = v_tail_2447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__0(lean_object* v_info_2450_, lean_object* v_ctx_2451_){
_start:
{
lean_object* v_toInputContext_2452_; lean_object* v_toParserModuleContext_2453_; lean_object* v_toCacheableParserContext_2454_; lean_object* v_tokens_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2466_; 
v_toInputContext_2452_ = lean_ctor_get(v_ctx_2451_, 0);
v_toParserModuleContext_2453_ = lean_ctor_get(v_ctx_2451_, 1);
v_toCacheableParserContext_2454_ = lean_ctor_get(v_ctx_2451_, 2);
v_tokens_2455_ = lean_ctor_get(v_ctx_2451_, 3);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_ctx_2451_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2457_ = v_ctx_2451_;
v_isShared_2458_ = v_isSharedCheck_2466_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_tokens_2455_);
lean_inc(v_toCacheableParserContext_2454_);
lean_inc(v_toParserModuleContext_2453_);
lean_inc(v_toInputContext_2452_);
lean_dec(v_ctx_2451_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2466_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v_collectTokens_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v_collectTokens_2459_ = lean_ctor_get(v_info_2450_, 0);
lean_inc_ref(v_collectTokens_2459_);
lean_dec_ref(v_info_2450_);
v___x_2460_ = lean_box(0);
v___x_2461_ = lean_apply_1(v_collectTokens_2459_, v___x_2460_);
v___x_2462_ = l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(v_tokens_2455_, v___x_2461_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 3, v___x_2462_);
v___x_2464_ = v___x_2457_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_toInputContext_2452_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_toParserModuleContext_2453_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_toCacheableParserContext_2454_);
lean_ctor_set(v_reuseFailAlloc_2465_, 3, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1(lean_object* v_categories_2467_, lean_object* v_declName_2468_, lean_object* v___x_2469_, lean_object* v_ctx_2470_, lean_object* v_s_2471_, lean_object* v_evalFallback_x3f_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_Parser_mkParserOfConstant(v_categories_2467_, v_declName_2468_, v___x_2469_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v_snd_2476_; lean_object* v_info_2477_; lean_object* v_fn_2478_; lean_object* v___f_2479_; lean_object* v___x_2480_; 
lean_dec(v_evalFallback_x3f_2472_);
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v_snd_2476_ = lean_ctor_get(v_a_2475_, 1);
lean_inc(v_snd_2476_);
lean_dec(v_a_2475_);
v_info_2477_ = lean_ctor_get(v_snd_2476_, 0);
lean_inc_ref(v_info_2477_);
v_fn_2478_ = lean_ctor_get(v_snd_2476_, 1);
lean_inc_ref(v_fn_2478_);
lean_dec(v_snd_2476_);
v___f_2479_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__0), 2, 1);
lean_closure_set(v___f_2479_, 0, v_info_2477_);
v___x_2480_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2479_, v_fn_2478_, v_ctx_2470_, v_s_2471_);
return v___x_2480_;
}
else
{
if (lean_obj_tag(v_evalFallback_x3f_2472_) == 1)
{
lean_object* v_val_2481_; lean_object* v___x_2482_; 
lean_dec_ref_known(v___x_2474_, 1);
v_val_2481_ = lean_ctor_get(v_evalFallback_x3f_2472_, 0);
lean_inc(v_val_2481_);
lean_dec_ref_known(v_evalFallback_x3f_2472_, 1);
v___x_2482_ = lean_apply_2(v_val_2481_, v_ctx_2470_, v_s_2471_);
return v___x_2482_;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; lean_object* v___x_2487_; 
lean_dec(v_evalFallback_x3f_2472_);
lean_dec_ref(v_ctx_2470_);
v_a_2483_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2474_, 1);
v___x_2484_ = lean_io_error_to_string(v_a_2483_);
v___x_2485_ = lean_box(0);
v___x_2486_ = 1;
v___x_2487_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2471_, v___x_2484_, v___x_2485_, v___x_2486_);
return v___x_2487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed(lean_object* v_categories_2488_, lean_object* v_declName_2489_, lean_object* v___x_2490_, lean_object* v_ctx_2491_, lean_object* v_s_2492_, lean_object* v_evalFallback_x3f_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_Parser_evalParserConstUnsafe___lam__1(v_categories_2488_, v_declName_2489_, v___x_2490_, v_ctx_2491_, v_s_2492_, v_evalFallback_x3f_2493_);
lean_dec_ref(v___x_2490_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* v_declName_2496_, lean_object* v_evalFallback_x3f_2497_, lean_object* v_ctx_2498_, lean_object* v_s_2499_){
_start:
{
lean_object* v_toParserModuleContext_2500_; lean_object* v_env_2501_; lean_object* v_options_2502_; lean_object* v___x_2503_; lean_object* v_ext_2504_; lean_object* v_toEnvExtension_2505_; lean_object* v_asyncMode_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v_categories_2509_; lean_object* v___x_2510_; lean_object* v___f_2511_; lean_object* v___x_2512_; 
v_toParserModuleContext_2500_ = lean_ctor_get(v_ctx_2498_, 1);
v_env_2501_ = lean_ctor_get(v_toParserModuleContext_2500_, 0);
v_options_2502_ = lean_ctor_get(v_toParserModuleContext_2500_, 1);
v___x_2503_ = l_Lean_Parser_parserExtension;
v_ext_2504_ = lean_ctor_get(v___x_2503_, 1);
v_toEnvExtension_2505_ = lean_ctor_get(v_ext_2504_, 0);
v_asyncMode_2506_ = lean_ctor_get(v_toEnvExtension_2505_, 2);
v___x_2507_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref_n(v_env_2501_, 2);
v___x_2508_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2507_, v___x_2503_, v_env_2501_, v_asyncMode_2506_);
v_categories_2509_ = lean_ctor_get(v___x_2508_, 2);
lean_inc_ref(v_categories_2509_);
lean_dec(v___x_2508_);
lean_inc_ref(v_options_2502_);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v_env_2501_);
lean_ctor_set(v___x_2510_, 1, v_options_2502_);
v___f_2511_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2511_, 0, v_categories_2509_);
lean_closure_set(v___f_2511_, 1, v_declName_2496_);
lean_closure_set(v___f_2511_, 2, v___x_2510_);
lean_closure_set(v___f_2511_, 3, v_ctx_2498_);
lean_closure_set(v___f_2511_, 4, v_s_2499_);
lean_closure_set(v___f_2511_, 5, v_evalFallback_x3f_2497_);
v___x_2512_ = l_unsafeBaseIO___redArg(v___f_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object* v_name_2513_, lean_object* v_decl_2514_, lean_object* v_ref_2515_){
_start:
{
lean_object* v_defValue_2517_; lean_object* v_descr_2518_; lean_object* v_deprecation_x3f_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v_defValue_2517_ = lean_ctor_get(v_decl_2514_, 0);
v_descr_2518_ = lean_ctor_get(v_decl_2514_, 1);
v_deprecation_x3f_2519_ = lean_ctor_get(v_decl_2514_, 2);
v___x_2520_ = lean_alloc_ctor(1, 0, 1);
v___x_2521_ = lean_unbox(v_defValue_2517_);
lean_ctor_set_uint8(v___x_2520_, 0, v___x_2521_);
lean_inc(v_deprecation_x3f_2519_);
lean_inc_ref(v_descr_2518_);
lean_inc_n(v_name_2513_, 2);
v___x_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2522_, 0, v_name_2513_);
lean_ctor_set(v___x_2522_, 1, v_ref_2515_);
lean_ctor_set(v___x_2522_, 2, v___x_2520_);
lean_ctor_set(v___x_2522_, 3, v_descr_2518_);
lean_ctor_set(v___x_2522_, 4, v_deprecation_x3f_2519_);
v___x_2523_ = lean_register_option(v_name_2513_, v___x_2522_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2531_; 
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; 
v_unused_2532_ = lean_ctor_get(v___x_2523_, 0);
lean_dec(v_unused_2532_);
v___x_2525_ = v___x_2523_;
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
else
{
lean_dec(v___x_2523_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
lean_inc(v_defValue_2517_);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v_name_2513_);
lean_ctor_set(v___x_2527_, 1, v_defValue_2517_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2527_);
v___x_2529_ = v___x_2525_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_name_2513_);
v_a_2533_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2523_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2523_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2541_, lean_object* v_decl_2542_, lean_object* v_ref_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v_name_2541_, v_decl_2542_, v_ref_2543_);
lean_dec_ref(v_decl_2542_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2563_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2564_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2565_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2566_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v___x_2563_, v___x_2564_, v___x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object* v_a_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(lean_object* v_o_2572_, lean_object* v_k_2573_, uint8_t v_v_2574_){
_start:
{
lean_object* v_map_2575_; uint8_t v_hasTrace_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2590_; 
v_map_2575_ = lean_ctor_get(v_o_2572_, 0);
v_hasTrace_2576_ = lean_ctor_get_uint8(v_o_2572_, sizeof(void*)*1);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_o_2572_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2578_ = v_o_2572_;
v_isShared_2579_ = v_isSharedCheck_2590_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_map_2575_);
lean_dec(v_o_2572_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2590_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2580_, 0, v_v_2574_);
lean_inc(v_k_2573_);
v___x_2581_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2573_, v___x_2580_, v_map_2575_);
if (v_hasTrace_2576_ == 0)
{
lean_object* v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2585_; 
v___x_2582_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_2583_ = l_Lean_Name_isPrefixOf(v___x_2582_, v_k_2573_);
lean_dec(v_k_2573_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v___x_2581_);
v___x_2585_ = v___x_2578_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2581_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*1, v___x_2583_);
return v___x_2585_;
}
}
else
{
lean_object* v___x_2588_; 
lean_dec(v_k_2573_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v___x_2581_);
v___x_2588_ = v___x_2578_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2589_, sizeof(void*)*1, v_hasTrace_2576_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___boxed(lean_object* v_o_2591_, lean_object* v_k_2592_, lean_object* v_v_2593_){
_start:
{
uint8_t v_v_boxed_2594_; lean_object* v_res_2595_; 
v_v_boxed_2594_ = lean_unbox(v_v_2593_);
v_res_2595_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_o_2591_, v_k_2592_, v_v_boxed_2594_);
return v_res_2595_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(lean_object* v_opts_2596_, lean_object* v_opt_2597_){
_start:
{
lean_object* v_name_2598_; lean_object* v_defValue_2599_; lean_object* v_map_2600_; lean_object* v___x_2601_; 
v_name_2598_ = lean_ctor_get(v_opt_2597_, 0);
v_defValue_2599_ = lean_ctor_get(v_opt_2597_, 1);
v_map_2600_ = lean_ctor_get(v_opts_2596_, 0);
v___x_2601_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2600_, v_name_2598_);
if (lean_obj_tag(v___x_2601_) == 0)
{
uint8_t v___x_2602_; 
v___x_2602_ = lean_unbox(v_defValue_2599_);
return v___x_2602_;
}
else
{
lean_object* v_val_2603_; 
v_val_2603_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_val_2603_);
lean_dec_ref_known(v___x_2601_, 1);
if (lean_obj_tag(v_val_2603_) == 1)
{
uint8_t v_v_2604_; 
v_v_2604_ = lean_ctor_get_uint8(v_val_2603_, 0);
lean_dec_ref_known(v_val_2603_, 0);
return v_v_2604_;
}
else
{
uint8_t v___x_2605_; 
lean_dec(v_val_2603_);
v___x_2605_ = lean_unbox(v_defValue_2599_);
return v___x_2605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1___boxed(lean_object* v_opts_2606_, lean_object* v_opt_2607_){
_start:
{
uint8_t v_res_2608_; lean_object* v_r_2609_; 
v_res_2608_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_opts_2606_, v_opt_2607_);
lean_dec_ref(v_opt_2607_);
lean_dec_ref(v_opts_2606_);
v_r_2609_ = lean_box(v_res_2608_);
return v_r_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0(uint8_t v_suppressInsideQuot_2615_, lean_object* v_ctx_2616_){
_start:
{
lean_object* v_toParserModuleContext_2617_; lean_object* v_toInputContext_2618_; lean_object* v_toCacheableParserContext_2619_; lean_object* v_tokens_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2640_; 
v_toParserModuleContext_2617_ = lean_ctor_get(v_ctx_2616_, 1);
v_toInputContext_2618_ = lean_ctor_get(v_ctx_2616_, 0);
v_toCacheableParserContext_2619_ = lean_ctor_get(v_ctx_2616_, 2);
v_tokens_2620_ = lean_ctor_get(v_ctx_2616_, 3);
v_isSharedCheck_2640_ = !lean_is_exclusive(v_ctx_2616_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2622_ = v_ctx_2616_;
v_isShared_2623_ = v_isSharedCheck_2640_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_tokens_2620_);
lean_inc(v_toCacheableParserContext_2619_);
lean_inc(v_toParserModuleContext_2617_);
lean_inc(v_toInputContext_2618_);
lean_dec(v_ctx_2616_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2640_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v_env_2624_; lean_object* v_options_2625_; lean_object* v_currNamespace_2626_; lean_object* v_openDecls_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2639_; 
v_env_2624_ = lean_ctor_get(v_toParserModuleContext_2617_, 0);
v_options_2625_ = lean_ctor_get(v_toParserModuleContext_2617_, 1);
v_currNamespace_2626_ = lean_ctor_get(v_toParserModuleContext_2617_, 2);
v_openDecls_2627_ = lean_ctor_get(v_toParserModuleContext_2617_, 3);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_toParserModuleContext_2617_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2629_ = v_toParserModuleContext_2617_;
v_isShared_2630_ = v_isSharedCheck_2639_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_openDecls_2627_);
lean_inc(v_currNamespace_2626_);
lean_inc(v_options_2625_);
lean_inc(v_env_2624_);
lean_dec(v_toParserModuleContext_2617_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2639_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2631_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_2632_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_2625_, v___x_2631_, v_suppressInsideQuot_2615_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 1, v___x_2632_);
v___x_2634_ = v___x_2629_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_env_2624_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2638_, 2, v_currNamespace_2626_);
lean_ctor_set(v_reuseFailAlloc_2638_, 3, v_openDecls_2627_);
v___x_2634_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2636_; 
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 1, v___x_2634_);
v___x_2636_ = v___x_2622_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_toInputContext_2618_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v_toCacheableParserContext_2619_);
lean_ctor_set(v_reuseFailAlloc_2637_, 3, v_tokens_2620_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0___boxed(lean_object* v_suppressInsideQuot_2641_, lean_object* v_ctx_2642_){
_start:
{
uint8_t v_suppressInsideQuot_boxed_2643_; lean_object* v_res_2644_; 
v_suppressInsideQuot_boxed_2643_ = lean_unbox(v_suppressInsideQuot_2641_);
v_res_2644_ = l_Lean_Parser_evalInsideQuot___lam__0(v_suppressInsideQuot_boxed_2643_, v_ctx_2642_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object* v_fn_2645_, lean_object* v_declName_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_toCacheableParserContext_2649_; lean_object* v_toParserModuleContext_2650_; lean_object* v_quotDepth_2651_; uint8_t v_suppressInsideQuot_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v_toCacheableParserContext_2649_ = lean_ctor_get(v___y_2647_, 2);
v_toParserModuleContext_2650_ = lean_ctor_get(v___y_2647_, 1);
v_quotDepth_2651_ = lean_ctor_get(v_toCacheableParserContext_2649_, 1);
v_suppressInsideQuot_2652_ = lean_ctor_get_uint8(v_toCacheableParserContext_2649_, sizeof(void*)*4);
v___x_2653_ = lean_unsigned_to_nat(0u);
v___x_2654_ = lean_nat_dec_lt(v___x_2653_, v_quotDepth_2651_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; 
lean_dec(v_declName_2646_);
v___x_2655_ = lean_apply_2(v_fn_2645_, v___y_2647_, v___y_2648_);
return v___x_2655_;
}
else
{
if (v_suppressInsideQuot_2652_ == 0)
{
lean_object* v_env_2656_; lean_object* v_options_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v_env_2656_ = lean_ctor_get(v_toParserModuleContext_2650_, 0);
v_options_2657_ = lean_ctor_get(v_toParserModuleContext_2650_, 1);
v___x_2658_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_2659_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_2657_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; 
lean_dec(v_declName_2646_);
v___x_2660_ = lean_apply_2(v_fn_2645_, v___y_2647_, v___y_2648_);
return v___x_2660_;
}
else
{
uint8_t v___x_2661_; 
lean_inc(v_declName_2646_);
lean_inc_ref(v_env_2656_);
v___x_2661_ = l_Lean_Environment_contains(v_env_2656_, v_declName_2646_, v___x_2659_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
lean_dec(v_declName_2646_);
v___x_2662_ = lean_apply_2(v_fn_2645_, v___y_2647_, v___y_2648_);
return v___x_2662_;
}
else
{
lean_object* v___x_2663_; lean_object* v___f_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2663_ = lean_box(v_suppressInsideQuot_2652_);
v___f_2664_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2664_, 0, v___x_2663_);
v___x_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2665_, 0, v_fn_2645_);
v___x_2666_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_2666_, 0, v_declName_2646_);
lean_closure_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2664_, v___x_2666_, v___y_2647_, v___y_2648_);
return v___x_2667_;
}
}
}
else
{
lean_object* v___x_2668_; 
lean_dec(v_declName_2646_);
v___x_2668_ = lean_apply_2(v_fn_2645_, v___y_2647_, v___y_2648_);
return v___x_2668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object* v_declName_2669_, lean_object* v_p_2670_){
_start:
{
lean_object* v_info_2671_; lean_object* v_fn_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2680_; 
v_info_2671_ = lean_ctor_get(v_p_2670_, 0);
v_fn_2672_ = lean_ctor_get(v_p_2670_, 1);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_p_2670_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2674_ = v_p_2670_;
v_isShared_2675_ = v_isSharedCheck_2680_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_fn_2672_);
lean_inc(v_info_2671_);
lean_dec(v_p_2670_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2680_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___f_2676_; lean_object* v___x_2678_; 
v___f_2676_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__1), 4, 2);
lean_closure_set(v___f_2676_, 0, v_fn_2672_);
lean_closure_set(v___f_2676_, 1, v_declName_2669_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 1, v___f_2676_);
v___x_2678_ = v___x_2674_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_info_2671_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___f_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object* v_catName_2681_, lean_object* v_declName_2682_, uint8_t v_leading_2683_, lean_object* v_p_2684_, lean_object* v_prio_2685_){
_start:
{
lean_object* v_p_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
lean_inc_n(v_declName_2682_, 2);
v_p_2687_ = l_Lean_Parser_evalInsideQuot(v_declName_2682_, v_p_2684_);
v___x_2688_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_2689_ = lean_st_ref_get(v___x_2688_);
lean_inc_ref(v_p_2687_);
v___x_2690_ = l_Lean_Parser_addParser(v___x_2689_, v_catName_2681_, v_declName_2682_, v_leading_2683_, v_p_2687_, v_prio_2685_);
v___x_2691_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_2690_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2693_; lean_object* v_info_2694_; lean_object* v_collectKinds_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2691_, 1);
v___x_2693_ = lean_st_ref_swap(v___x_2688_, v_a_2692_);
lean_dec(v___x_2693_);
v_info_2694_ = lean_ctor_get(v_p_2687_, 0);
lean_inc_ref(v_info_2694_);
lean_dec_ref(v_p_2687_);
v_collectKinds_2695_ = lean_ctor_get(v_info_2694_, 1);
v___x_2696_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_2697_ = lean_st_ref_take(v___x_2696_);
lean_inc_ref(v_collectKinds_2695_);
v___x_2698_ = lean_apply_1(v_collectKinds_2695_, v___x_2697_);
v___x_2699_ = lean_st_ref_put(v___x_2696_, v___x_2698_);
v___x_2700_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_2694_, v_declName_2682_);
return v___x_2700_;
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec_ref(v_p_2687_);
lean_dec(v_declName_2682_);
v_a_2701_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2691_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2691_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* v_catName_2709_, lean_object* v_declName_2710_, lean_object* v_leading_2711_, lean_object* v_p_2712_, lean_object* v_prio_2713_, lean_object* v_a_2714_){
_start:
{
uint8_t v_leading_boxed_2715_; lean_object* v_res_2716_; 
v_leading_boxed_2715_ = lean_unbox(v_leading_2711_);
v_res_2716_ = l_Lean_Parser_addBuiltinParser(v_catName_2709_, v_declName_2710_, v_leading_boxed_2715_, v_p_2712_, v_prio_2713_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* v_catName_2717_, lean_object* v_declName_2718_, lean_object* v_p_2719_, lean_object* v_prio_2720_){
_start:
{
uint8_t v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = 1;
v___x_2723_ = l_Lean_Parser_addBuiltinParser(v_catName_2717_, v_declName_2718_, v___x_2722_, v_p_2719_, v_prio_2720_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object* v_catName_2724_, lean_object* v_declName_2725_, lean_object* v_p_2726_, lean_object* v_prio_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_Parser_addBuiltinLeadingParser(v_catName_2724_, v_declName_2725_, v_p_2726_, v_prio_2727_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* v_catName_2730_, lean_object* v_declName_2731_, lean_object* v_p_2732_, lean_object* v_prio_2733_){
_start:
{
uint8_t v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = 0;
v___x_2736_ = l_Lean_Parser_addBuiltinParser(v_catName_2730_, v_declName_2731_, v___x_2735_, v_p_2732_, v_prio_2733_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object* v_catName_2737_, lean_object* v_declName_2738_, lean_object* v_p_2739_, lean_object* v_prio_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_Parser_addBuiltinTrailingParser(v_catName_2737_, v_declName_2738_, v_p_2739_, v_prio_2740_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object* v_kind_2743_){
_start:
{
uint8_t v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = 1;
lean_inc(v_kind_2743_);
v___x_2745_ = l_Lean_Name_toString(v_kind_2743_, v___x_2744_);
v___x_2746_ = l_Lean_Parser_mkAntiquot(v___x_2745_, v_kind_2743_, v___x_2744_, v___x_2744_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object* v_kind_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v___x_2750_; lean_object* v_fn_2751_; lean_object* v___x_2752_; 
v___x_2750_ = l_Lean_Parser_mkCategoryAntiquotParser(v_kind_2747_);
v_fn_2751_ = lean_ctor_get(v___x_2750_, 1);
lean_inc_ref(v_fn_2751_);
lean_dec_ref(v___x_2750_);
v___x_2752_ = lean_apply_2(v_fn_2751_, v_a_2748_, v_a_2749_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl___lam__0(lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2756_; lean_object* v_fn_2757_; lean_object* v___x_2758_; 
v___x_2756_ = l_Lean_Parser_mkCategoryAntiquotParser(v___y_2753_);
v_fn_2757_ = lean_ctor_get(v___x_2756_, 1);
lean_inc_ref(v_fn_2757_);
lean_dec_ref(v___x_2756_);
v___x_2758_ = lean_apply_2(v_fn_2757_, v___y_2754_, v___y_2755_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* v_catName_2767_, lean_object* v_ctx_2768_, lean_object* v_s_2769_){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; uint8_t v___x_2773_; lean_object* v___y_2775_; 
v___x_2770_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2771_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__1));
v___x_2772_ = lean_name_eq(v_catName_2767_, v___x_2771_);
v___x_2773_ = 1;
if (v___x_2772_ == 0)
{
v___y_2775_ = v_catName_2767_;
goto v___jp_2774_;
}
else
{
lean_object* v___x_2797_; 
lean_dec(v_catName_2767_);
v___x_2797_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__5));
v___y_2775_ = v___x_2797_;
goto v___jp_2774_;
}
v___jp_2774_:
{
lean_object* v_toParserModuleContext_2776_; lean_object* v_env_2777_; lean_object* v___x_2778_; lean_object* v_ext_2779_; lean_object* v_toEnvExtension_2780_; lean_object* v_asyncMode_2781_; lean_object* v___x_2782_; lean_object* v_categories_2783_; lean_object* v___x_2784_; 
v_toParserModuleContext_2776_ = lean_ctor_get(v_ctx_2768_, 1);
v_env_2777_ = lean_ctor_get(v_toParserModuleContext_2776_, 0);
v___x_2778_ = l_Lean_Parser_parserExtension;
v_ext_2779_ = lean_ctor_get(v___x_2778_, 1);
v_toEnvExtension_2780_ = lean_ctor_get(v_ext_2779_, 0);
v_asyncMode_2781_ = lean_ctor_get(v_toEnvExtension_2780_, 2);
lean_inc_ref(v_env_2777_);
v___x_2782_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2770_, v___x_2778_, v_env_2777_, v_asyncMode_2781_);
v_categories_2783_ = lean_ctor_get(v___x_2782_, 2);
lean_inc_ref(v_categories_2783_);
lean_dec(v___x_2782_);
v___x_2784_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2783_, v___y_2775_);
lean_dec_ref(v_categories_2783_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
lean_dec_ref(v_ctx_2768_);
v___x_2785_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__2));
v___x_2786_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2775_, v___x_2773_);
v___x_2787_ = lean_string_append(v___x_2785_, v___x_2786_);
lean_dec_ref(v___x_2786_);
v___x_2788_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__3));
v___x_2789_ = lean_string_append(v___x_2787_, v___x_2788_);
v___x_2790_ = lean_box(0);
v___x_2791_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2769_, v___x_2789_, v___x_2790_, v___x_2773_);
return v___x_2791_;
}
else
{
lean_object* v_val_2792_; lean_object* v_tables_2793_; uint8_t v_behavior_2794_; lean_object* v___f_2795_; lean_object* v___x_2796_; 
v_val_2792_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_val_2792_);
lean_dec_ref_known(v___x_2784_, 1);
v_tables_2793_ = lean_ctor_get(v_val_2792_, 2);
lean_inc_ref(v_tables_2793_);
v_behavior_2794_ = lean_ctor_get_uint8(v_val_2792_, sizeof(void*)*3);
lean_dec(v_val_2792_);
lean_inc(v___y_2775_);
v___f_2795_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl___lam__0), 3, 1);
lean_closure_set(v___f_2795_, 0, v___y_2775_);
v___x_2796_ = l_Lean_Parser_prattParser(v___y_2775_, v_tables_2793_, v_behavior_2794_, v___f_2795_, v_ctx_2768_, v_s_2769_);
return v___x_2796_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2800_ = l_Lean_Parser_categoryParserFnRef;
v___x_2801_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_));
v___x_2802_ = lean_box(0);
v___x_2803_ = lean_st_ref_swap(v___x_2800_, v___x_2801_);
lean_dec(v___x_2803_);
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object* v_a_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
return v_res_2806_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0);
v___x_2810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object* v_ext_2811_, lean_object* v_b_2812_, uint8_t v_kind_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_toCold_2817_; lean_object* v_currNamespace_2818_; lean_object* v___x_2819_; lean_object* v_env_2820_; lean_object* v_nextMacroScope_2821_; lean_object* v_ngen_2822_; lean_object* v_auxDeclNGen_2823_; lean_object* v_traceState_2824_; lean_object* v_recordedDeps_2825_; lean_object* v_messages_2826_; lean_object* v_infoState_2827_; lean_object* v_snapshotTasks_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2840_; 
v_toCold_2817_ = lean_ctor_get(v___y_2814_, 0);
v_currNamespace_2818_ = lean_ctor_get(v_toCold_2817_, 4);
v___x_2819_ = lean_st_ref_take(v___y_2815_);
v_env_2820_ = lean_ctor_get(v___x_2819_, 0);
v_nextMacroScope_2821_ = lean_ctor_get(v___x_2819_, 1);
v_ngen_2822_ = lean_ctor_get(v___x_2819_, 2);
v_auxDeclNGen_2823_ = lean_ctor_get(v___x_2819_, 3);
v_traceState_2824_ = lean_ctor_get(v___x_2819_, 4);
v_recordedDeps_2825_ = lean_ctor_get(v___x_2819_, 6);
v_messages_2826_ = lean_ctor_get(v___x_2819_, 7);
v_infoState_2827_ = lean_ctor_get(v___x_2819_, 8);
v_snapshotTasks_2828_ = lean_ctor_get(v___x_2819_, 9);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; 
v_unused_2841_ = lean_ctor_get(v___x_2819_, 5);
lean_dec(v_unused_2841_);
v___x_2830_ = v___x_2819_;
v_isShared_2831_ = v_isSharedCheck_2840_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_snapshotTasks_2828_);
lean_inc(v_infoState_2827_);
lean_inc(v_messages_2826_);
lean_inc(v_recordedDeps_2825_);
lean_inc(v_traceState_2824_);
lean_inc(v_auxDeclNGen_2823_);
lean_inc(v_ngen_2822_);
lean_inc(v_nextMacroScope_2821_);
lean_inc(v_env_2820_);
lean_dec(v___x_2819_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2840_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2832_ = lean_box(0);
lean_inc(v_currNamespace_2818_);
v___x_2833_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2820_, v_ext_2811_, v_b_2812_, v_kind_2813_, v_currNamespace_2818_);
v___x_2834_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 5, v___x_2834_);
lean_ctor_set(v___x_2830_, 0, v___x_2833_);
v___x_2836_ = v___x_2830_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_nextMacroScope_2821_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_ngen_2822_);
lean_ctor_set(v_reuseFailAlloc_2839_, 3, v_auxDeclNGen_2823_);
lean_ctor_set(v_reuseFailAlloc_2839_, 4, v_traceState_2824_);
lean_ctor_set(v_reuseFailAlloc_2839_, 5, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2839_, 6, v_recordedDeps_2825_);
lean_ctor_set(v_reuseFailAlloc_2839_, 7, v_messages_2826_);
lean_ctor_set(v_reuseFailAlloc_2839_, 8, v_infoState_2827_);
lean_ctor_set(v_reuseFailAlloc_2839_, 9, v_snapshotTasks_2828_);
v___x_2836_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = lean_st_ref_put(v___y_2815_, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2832_);
return v___x_2838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object* v_ext_2842_, lean_object* v_b_2843_, lean_object* v_kind_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
uint8_t v_kind_boxed_2848_; lean_object* v_res_2849_; 
v_kind_boxed_2848_ = lean_unbox(v_kind_2844_);
v_res_2849_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2842_, v_b_2843_, v_kind_boxed_2848_, v___y_2845_, v___y_2846_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object* v_00_u03b1_2850_, lean_object* v_00_u03b2_2851_, lean_object* v_00_u03c3_2852_, lean_object* v_ext_2853_, lean_object* v_b_2854_, uint8_t v_kind_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2853_, v_b_2854_, v_kind_2855_, v___y_2856_, v___y_2857_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object* v_00_u03b1_2860_, lean_object* v_00_u03b2_2861_, lean_object* v_00_u03c3_2862_, lean_object* v_ext_2863_, lean_object* v_b_2864_, lean_object* v_kind_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
uint8_t v_kind_boxed_2869_; lean_object* v_res_2870_; 
v_kind_boxed_2869_ = lean_unbox(v_kind_2865_);
v_res_2870_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(v_00_u03b1_2860_, v_00_u03b2_2861_, v_00_u03c3_2862_, v_ext_2863_, v_b_2864_, v_kind_boxed_2869_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object* v_x_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
if (lean_obj_tag(v_x_2871_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v_a_2875_ = lean_ctor_get(v_x_2871_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v_x_2871_, 1);
v___x_2876_ = l_Lean_stringToMessageData(v_a_2875_);
v___x_2877_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2876_, v___y_2872_, v___y_2873_);
return v___x_2877_;
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
v_a_2878_ = lean_ctor_get(v_x_2871_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_x_2871_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v_x_2871_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v_x_2871_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
lean_ctor_set_tag(v___x_2880_, 0);
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object* v_x_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2886_, v___y_2887_, v___y_2888_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object* v_tk_2891_, uint8_t v_kind_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v_env_2898_; lean_object* v___x_2899_; lean_object* v_ext_2900_; lean_object* v_toEnvExtension_2901_; lean_object* v_asyncMode_2902_; lean_object* v___x_2903_; lean_object* v_tokens_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2896_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2897_ = lean_st_ref_get(v_a_2894_);
v_env_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc_ref(v_env_2898_);
lean_dec(v___x_2897_);
v___x_2899_ = l_Lean_Parser_parserExtension;
v_ext_2900_ = lean_ctor_get(v___x_2899_, 1);
v_toEnvExtension_2901_ = lean_ctor_get(v_ext_2900_, 0);
v_asyncMode_2902_ = lean_ctor_get(v_toEnvExtension_2901_, 2);
v___x_2903_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2896_, v___x_2899_, v_env_2898_, v_asyncMode_2902_);
v_tokens_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc_ref(v_tokens_2904_);
lean_dec(v___x_2903_);
lean_inc_ref(v_tk_2891_);
v___x_2905_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_2904_, v_tk_2891_);
v___x_2906_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v___x_2905_, v_a_2893_, v_a_2894_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
lean_dec_ref_known(v___x_2906_, 1);
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_tk_2891_);
v___x_2908_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_2899_, v___x_2907_, v_kind_2892_, v_a_2893_, v_a_2894_);
return v___x_2908_;
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec_ref(v_tk_2891_);
v_a_2909_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2906_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2906_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object* v_tk_2917_, lean_object* v_kind_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_){
_start:
{
uint8_t v_kind_boxed_2922_; lean_object* v_res_2923_; 
v_kind_boxed_2922_ = lean_unbox(v_kind_2918_);
v_res_2923_ = l_Lean_Parser_addToken(v_tk_2917_, v_kind_boxed_2922_, v_a_2919_, v_a_2920_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_object* v_00_u03b1_2924_, lean_object* v_x_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2925_, v___y_2926_, v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___boxed(lean_object* v_00_u03b1_2930_, lean_object* v_x_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(v_00_u03b1_2930_, v_x_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object* v_env_2936_, lean_object* v_k_2937_){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = l_Lean_Parser_parserExtension;
v___x_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2939_, 0, v_k_2937_);
v___x_2940_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2938_, v_env_2936_, v___x_2939_);
return v___x_2940_;
}
}
static uint8_t _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0(void){
_start:
{
lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2941_ = lean_box(0);
v___x_2942_ = lean_internal_is_stage0(v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object* v_env_2943_, lean_object* v_k_2944_){
_start:
{
lean_object* v___x_2945_; lean_object* v_ext_2946_; lean_object* v_toEnvExtension_2947_; lean_object* v_asyncMode_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v_kinds_2951_; uint8_t v___x_2952_; 
v___x_2945_ = l_Lean_Parser_parserExtension;
v_ext_2946_ = lean_ctor_get(v___x_2945_, 1);
v_toEnvExtension_2947_ = lean_ctor_get(v_ext_2946_, 0);
v_asyncMode_2948_ = lean_ctor_get(v_toEnvExtension_2947_, 2);
v___x_2949_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_2943_);
v___x_2950_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2949_, v___x_2945_, v_env_2943_, v_asyncMode_2948_);
v_kinds_2951_ = lean_ctor_get(v___x_2950_, 1);
lean_inc_ref(v_kinds_2951_);
lean_dec(v___x_2950_);
v___x_2952_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_2951_, v_k_2944_);
lean_dec_ref(v_kinds_2951_);
if (v___x_2952_ == 0)
{
uint8_t v___x_2953_; 
v___x_2953_ = lean_uint8_once(&l_Lean_Parser_isValidSyntaxNodeKind___closed__0, &l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once, _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0);
if (v___x_2953_ == 0)
{
lean_dec(v_k_2944_);
lean_dec_ref(v_env_2943_);
return v___x_2953_;
}
else
{
uint8_t v___x_2954_; 
v___x_2954_ = l_Lean_Environment_contains(v_env_2943_, v_k_2944_, v___x_2953_);
return v___x_2954_;
}
}
else
{
lean_dec(v_k_2944_);
lean_dec_ref(v_env_2943_);
return v___x_2952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* v_env_2955_, lean_object* v_k_2956_){
_start:
{
uint8_t v_res_2957_; lean_object* v_r_2958_; 
v_res_2957_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_2955_, v_k_2956_);
v_r_2958_ = lean_box(v_res_2957_);
return v_r_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds___lam__0(lean_object* v_ks_2959_, lean_object* v_k_2960_, lean_object* v_x_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2962_, 0, v_k_2960_);
lean_ctor_set(v___x_2962_, 1, v_ks_2959_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2963_, lean_object* v_keys_2964_, lean_object* v_vals_2965_, lean_object* v_i_2966_, lean_object* v_acc_2967_){
_start:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = lean_array_get_size(v_keys_2964_);
v___x_2969_ = lean_nat_dec_lt(v_i_2966_, v___x_2968_);
if (v___x_2969_ == 0)
{
lean_dec(v_i_2966_);
lean_dec(v_f_2963_);
return v_acc_2967_;
}
else
{
lean_object* v_k_2970_; lean_object* v_v_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v_k_2970_ = lean_array_fget_borrowed(v_keys_2964_, v_i_2966_);
v_v_2971_ = lean_array_fget_borrowed(v_vals_2965_, v_i_2966_);
lean_inc(v_f_2963_);
lean_inc(v_v_2971_);
lean_inc(v_k_2970_);
v___x_2972_ = lean_apply_3(v_f_2963_, v_acc_2967_, v_k_2970_, v_v_2971_);
v___x_2973_ = lean_unsigned_to_nat(1u);
v___x_2974_ = lean_nat_add(v_i_2966_, v___x_2973_);
lean_dec(v_i_2966_);
v_i_2966_ = v___x_2974_;
v_acc_2967_ = v___x_2972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2976_, lean_object* v_keys_2977_, lean_object* v_vals_2978_, lean_object* v_i_2979_, lean_object* v_acc_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2976_, v_keys_2977_, v_vals_2978_, v_i_2979_, v_acc_2980_);
lean_dec_ref(v_vals_2978_);
lean_dec_ref(v_keys_2977_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2982_, lean_object* v_as_2983_, size_t v_i_2984_, size_t v_stop_2985_, lean_object* v_b_2986_){
_start:
{
lean_object* v___y_2988_; uint8_t v___x_2992_; 
v___x_2992_ = lean_usize_dec_eq(v_i_2984_, v_stop_2985_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_array_uget_borrowed(v_as_2983_, v_i_2984_);
switch(lean_obj_tag(v___x_2993_))
{
case 0:
{
lean_object* v_key_2994_; lean_object* v_val_2995_; lean_object* v___x_2996_; 
v_key_2994_ = lean_ctor_get(v___x_2993_, 0);
v_val_2995_ = lean_ctor_get(v___x_2993_, 1);
lean_inc(v_f_2982_);
lean_inc(v_val_2995_);
lean_inc(v_key_2994_);
v___x_2996_ = lean_apply_3(v_f_2982_, v_b_2986_, v_key_2994_, v_val_2995_);
v___y_2988_ = v___x_2996_;
goto v___jp_2987_;
}
case 1:
{
lean_object* v_node_2997_; lean_object* v___x_2998_; 
v_node_2997_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_f_2982_);
v___x_2998_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_2982_, v_node_2997_, v_b_2986_);
v___y_2988_ = v___x_2998_;
goto v___jp_2987_;
}
default: 
{
v___y_2988_ = v_b_2986_;
goto v___jp_2987_;
}
}
}
else
{
lean_dec(v_f_2982_);
return v_b_2986_;
}
v___jp_2987_:
{
size_t v___x_2989_; size_t v___x_2990_; 
v___x_2989_ = ((size_t)1ULL);
v___x_2990_ = lean_usize_add(v_i_2984_, v___x_2989_);
v_i_2984_ = v___x_2990_;
v_b_2986_ = v___y_2988_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2999_, lean_object* v_x_3000_, lean_object* v_x_3001_){
_start:
{
if (lean_obj_tag(v_x_3000_) == 0)
{
lean_object* v_es_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; 
v_es_3002_ = lean_ctor_get(v_x_3000_, 0);
v___x_3003_ = lean_unsigned_to_nat(0u);
v___x_3004_ = lean_array_get_size(v_es_3002_);
v___x_3005_ = lean_nat_dec_lt(v___x_3003_, v___x_3004_);
if (v___x_3005_ == 0)
{
lean_dec(v_f_2999_);
return v_x_3001_;
}
else
{
size_t v___x_3006_; size_t v___x_3007_; lean_object* v___x_3008_; 
v___x_3006_ = ((size_t)0ULL);
v___x_3007_ = lean_usize_of_nat(v___x_3004_);
v___x_3008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2999_, v_es_3002_, v___x_3006_, v___x_3007_, v_x_3001_);
return v___x_3008_;
}
}
else
{
lean_object* v_ks_3009_; lean_object* v_vs_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_ks_3009_ = lean_ctor_get(v_x_3000_, 0);
v_vs_3010_ = lean_ctor_get(v_x_3000_, 1);
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2999_, v_ks_3009_, v_vs_3010_, v___x_3011_, v_x_3001_);
return v___x_3012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3013_, lean_object* v_x_3014_, lean_object* v_x_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3013_, v_x_3014_, v_x_3015_);
lean_dec_ref(v_x_3014_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3017_, lean_object* v_as_3018_, lean_object* v_i_3019_, lean_object* v_stop_3020_, lean_object* v_b_3021_){
_start:
{
size_t v_i_boxed_3022_; size_t v_stop_boxed_3023_; lean_object* v_res_3024_; 
v_i_boxed_3022_ = lean_unbox_usize(v_i_3019_);
lean_dec(v_i_3019_);
v_stop_boxed_3023_ = lean_unbox_usize(v_stop_3020_);
lean_dec(v_stop_3020_);
v_res_3024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3017_, v_as_3018_, v_i_boxed_3022_, v_stop_boxed_3023_, v_b_3021_);
lean_dec_ref(v_as_3018_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object* v_f_3025_, lean_object* v_x1_3026_, lean_object* v_x2_3027_, lean_object* v_x3_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_apply_3(v_f_3025_, v_x1_3026_, v_x2_3027_, v_x3_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object* v_map_3030_, lean_object* v_f_3031_, lean_object* v_init_3032_){
_start:
{
lean_object* v___f_3033_; lean_object* v___x_3034_; 
v___f_3033_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3033_, 0, v_f_3031_);
v___x_3034_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v___f_3033_, v_map_3030_, v_init_3032_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object* v_map_3035_, lean_object* v_f_3036_, lean_object* v_init_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3035_, v_f_3036_, v_init_3037_);
lean_dec_ref(v_map_3035_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* v_env_3040_){
_start:
{
lean_object* v___x_3041_; lean_object* v_ext_3042_; lean_object* v_toEnvExtension_3043_; lean_object* v_asyncMode_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v_kinds_3047_; lean_object* v___f_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3041_ = l_Lean_Parser_parserExtension;
v_ext_3042_ = lean_ctor_get(v___x_3041_, 1);
v_toEnvExtension_3043_ = lean_ctor_get(v_ext_3042_, 0);
v_asyncMode_3044_ = lean_ctor_get(v_toEnvExtension_3043_, 2);
v___x_3045_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3046_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3045_, v___x_3041_, v_env_3040_, v_asyncMode_3044_);
v_kinds_3047_ = lean_ctor_get(v___x_3046_, 1);
lean_inc_ref(v_kinds_3047_);
lean_dec(v___x_3046_);
v___f_3048_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKinds___closed__0));
v___x_3049_ = lean_box(0);
v___x_3050_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_kinds_3047_, v___f_3048_, v___x_3049_);
lean_dec_ref(v_kinds_3047_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object* v_00_u03c3_3051_, lean_object* v_00_u03b2_3052_, lean_object* v_map_3053_, lean_object* v_f_3054_, lean_object* v_init_3055_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3053_, v_f_3054_, v_init_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object* v_00_u03c3_3057_, lean_object* v_00_u03b2_3058_, lean_object* v_map_3059_, lean_object* v_f_3060_, lean_object* v_init_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(v_00_u03c3_3057_, v_00_u03b2_3058_, v_map_3059_, v_f_3060_, v_init_3061_);
lean_dec_ref(v_map_3059_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object* v_map_3063_, lean_object* v_f_3064_, lean_object* v_init_3065_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3064_, v_map_3063_, v_init_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object* v_map_3067_, lean_object* v_f_3068_, lean_object* v_init_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(v_map_3067_, v_f_3068_, v_init_3069_);
lean_dec_ref(v_map_3067_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object* v_00_u03c3_3071_, lean_object* v_00_u03b2_3072_, lean_object* v_map_3073_, lean_object* v_f_3074_, lean_object* v_init_3075_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3074_, v_map_3073_, v_init_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3077_, lean_object* v_00_u03b2_3078_, lean_object* v_map_3079_, lean_object* v_f_3080_, lean_object* v_init_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(v_00_u03c3_3077_, v_00_u03b2_3078_, v_map_3079_, v_f_3080_, v_init_3081_);
lean_dec_ref(v_map_3079_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3083_, lean_object* v_00_u03b1_3084_, lean_object* v_00_u03b2_3085_, lean_object* v_f_3086_, lean_object* v_x_3087_, lean_object* v_x_3088_){
_start:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3086_, v_x_3087_, v_x_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3090_, lean_object* v_00_u03b1_3091_, lean_object* v_00_u03b2_3092_, lean_object* v_f_3093_, lean_object* v_x_3094_, lean_object* v_x_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(v_00_u03c3_3090_, v_00_u03b1_3091_, v_00_u03b2_3092_, v_f_3093_, v_x_3094_, v_x_3095_);
lean_dec_ref(v_x_3094_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3097_, lean_object* v_00_u03b2_3098_, lean_object* v_00_u03c3_3099_, lean_object* v_f_3100_, lean_object* v_as_3101_, size_t v_i_3102_, size_t v_stop_3103_, lean_object* v_b_3104_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3100_, v_as_3101_, v_i_3102_, v_stop_3103_, v_b_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3106_, lean_object* v_00_u03b2_3107_, lean_object* v_00_u03c3_3108_, lean_object* v_f_3109_, lean_object* v_as_3110_, lean_object* v_i_3111_, lean_object* v_stop_3112_, lean_object* v_b_3113_){
_start:
{
size_t v_i_boxed_3114_; size_t v_stop_boxed_3115_; lean_object* v_res_3116_; 
v_i_boxed_3114_ = lean_unbox_usize(v_i_3111_);
lean_dec(v_i_3111_);
v_stop_boxed_3115_ = lean_unbox_usize(v_stop_3112_);
lean_dec(v_stop_3112_);
v_res_3116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3106_, v_00_u03b2_3107_, v_00_u03c3_3108_, v_f_3109_, v_as_3110_, v_i_boxed_3114_, v_stop_boxed_3115_, v_b_3113_);
lean_dec_ref(v_as_3110_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3117_, lean_object* v_00_u03b1_3118_, lean_object* v_00_u03b2_3119_, lean_object* v_f_3120_, lean_object* v_keys_3121_, lean_object* v_vals_3122_, lean_object* v_heq_3123_, lean_object* v_i_3124_, lean_object* v_acc_3125_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3120_, v_keys_3121_, v_vals_3122_, v_i_3124_, v_acc_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3127_, lean_object* v_00_u03b1_3128_, lean_object* v_00_u03b2_3129_, lean_object* v_f_3130_, lean_object* v_keys_3131_, lean_object* v_vals_3132_, lean_object* v_heq_3133_, lean_object* v_i_3134_, lean_object* v_acc_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3127_, v_00_u03b1_3128_, v_00_u03b2_3129_, v_f_3130_, v_keys_3131_, v_vals_3132_, v_heq_3133_, v_i_3134_, v_acc_3135_);
lean_dec_ref(v_vals_3132_);
lean_dec_ref(v_keys_3131_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* v_env_3137_){
_start:
{
lean_object* v___x_3138_; lean_object* v_ext_3139_; lean_object* v_toEnvExtension_3140_; lean_object* v_asyncMode_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v_tokens_3144_; 
v___x_3138_ = l_Lean_Parser_parserExtension;
v_ext_3139_ = lean_ctor_get(v___x_3138_, 1);
v_toEnvExtension_3140_ = lean_ctor_get(v_ext_3139_, 0);
v_asyncMode_3141_ = lean_ctor_get(v_toEnvExtension_3140_, 2);
v___x_3142_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3143_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3142_, v___x_3138_, v_env_3137_, v_asyncMode_3141_);
v_tokens_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc_ref(v_tokens_3144_);
lean_dec(v___x_3143_);
return v_tokens_3144_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__8));
v___x_3170_ = l_Lean_mkAtom(v___x_3169_);
return v___x_3170_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__10, &l_Lean_Parser_mkInputContext___auto__1___closed__10_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__10);
v___x_3172_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3173_ = lean_array_push(v___x_3172_, v___x_3171_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3184_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3185_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3186_ = lean_array_push(v___x_3185_, v___x_3184_);
return v___x_3186_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3187_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__15, &l_Lean_Parser_mkInputContext___auto__1___closed__15_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__15);
v___x_3188_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__13));
v___x_3189_ = lean_box(2);
v___x_3190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_ctor_set(v___x_3190_, 1, v___x_3188_);
lean_ctor_set(v___x_3190_, 2, v___x_3187_);
return v___x_3190_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__16, &l_Lean_Parser_mkInputContext___auto__1___closed__16_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__16);
v___x_3192_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__11, &l_Lean_Parser_mkInputContext___auto__1___closed__11_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__11);
v___x_3193_ = lean_array_push(v___x_3192_, v___x_3191_);
return v___x_3193_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3195_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__17, &l_Lean_Parser_mkInputContext___auto__1___closed__17_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__17);
v___x_3196_ = lean_array_push(v___x_3195_, v___x_3194_);
return v___x_3196_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3198_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__18, &l_Lean_Parser_mkInputContext___auto__1___closed__18_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__18);
v___x_3199_ = lean_array_push(v___x_3198_, v___x_3197_);
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3200_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3201_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__19, &l_Lean_Parser_mkInputContext___auto__1___closed__19_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__19);
v___x_3202_ = lean_array_push(v___x_3201_, v___x_3200_);
return v___x_3202_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3203_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3204_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__20, &l_Lean_Parser_mkInputContext___auto__1___closed__20_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__20);
v___x_3205_ = lean_array_push(v___x_3204_, v___x_3203_);
return v___x_3205_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3206_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__21, &l_Lean_Parser_mkInputContext___auto__1___closed__21_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__21);
v___x_3207_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__9));
v___x_3208_ = lean_box(2);
v___x_3209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v___x_3207_);
lean_ctor_set(v___x_3209_, 2, v___x_3206_);
return v___x_3209_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__22, &l_Lean_Parser_mkInputContext___auto__1___closed__22_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__22);
v___x_3211_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3212_ = lean_array_push(v___x_3211_, v___x_3210_);
return v___x_3212_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3213_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__23, &l_Lean_Parser_mkInputContext___auto__1___closed__23_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__23);
v___x_3214_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3215_ = lean_box(2);
v___x_3216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set(v___x_3216_, 1, v___x_3214_);
lean_ctor_set(v___x_3216_, 2, v___x_3213_);
return v___x_3216_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3217_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__24, &l_Lean_Parser_mkInputContext___auto__1___closed__24_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__24);
v___x_3218_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3219_ = lean_array_push(v___x_3218_, v___x_3217_);
return v___x_3219_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3220_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__25, &l_Lean_Parser_mkInputContext___auto__1___closed__25_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__25);
v___x_3221_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3222_ = lean_box(2);
v___x_3223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
lean_ctor_set(v___x_3223_, 1, v___x_3221_);
lean_ctor_set(v___x_3223_, 2, v___x_3220_);
return v___x_3223_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__26, &l_Lean_Parser_mkInputContext___auto__1___closed__26_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__26);
v___x_3225_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3226_ = lean_array_push(v___x_3225_, v___x_3224_);
return v___x_3226_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3227_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__27, &l_Lean_Parser_mkInputContext___auto__1___closed__27_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__27);
v___x_3228_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3229_ = lean_box(2);
v___x_3230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
lean_ctor_set(v___x_3230_, 1, v___x_3228_);
lean_ctor_set(v___x_3230_, 2, v___x_3227_);
return v___x_3230_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1(void){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__28, &l_Lean_Parser_mkInputContext___auto__1___closed__28_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__28);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object* v_input_3232_, lean_object* v_fileName_3233_, uint8_t v_normalizeLineEndings_3234_, lean_object* v_endPos_3235_){
_start:
{
lean_object* v_fst_3237_; lean_object* v_snd_3238_; lean_object* v_text_3244_; 
v_text_3244_ = l_Lean_FileMap_ofString(v_input_3232_);
if (v_normalizeLineEndings_3234_ == 0)
{
v_fst_3237_ = v_text_3244_;
v_snd_3238_ = v_endPos_3235_;
goto v___jp_3236_;
}
else
{
lean_object* v_source_3245_; lean_object* v_endPos_x27_3246_; lean_object* v___x_3247_; lean_object* v_text_3248_; lean_object* v___x_3249_; 
v_source_3245_ = lean_ctor_get(v_text_3244_, 0);
lean_inc_ref(v_source_3245_);
v_endPos_x27_3246_ = l_Lean_FileMap_toPosition(v_text_3244_, v_endPos_3235_);
lean_dec(v_endPos_3235_);
v___x_3247_ = l_String_crlfToLf(v_source_3245_);
lean_dec_ref(v_source_3245_);
v_text_3248_ = l_Lean_FileMap_ofString(v___x_3247_);
v___x_3249_ = l_Lean_FileMap_ofPosition(v_text_3248_, v_endPos_x27_3246_);
v_fst_3237_ = v_text_3248_;
v_snd_3238_ = v___x_3249_;
goto v___jp_3236_;
}
v___jp_3236_:
{
lean_object* v_source_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; 
v_source_3239_ = lean_ctor_get(v_fst_3237_, 0);
lean_inc_ref(v_source_3239_);
v___x_3240_ = lean_string_utf8_byte_size(v_source_3239_);
v___x_3241_ = lean_nat_dec_le(v_snd_3238_, v___x_3240_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; 
lean_dec(v_snd_3238_);
v___x_3242_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3242_, 0, v_source_3239_);
lean_ctor_set(v___x_3242_, 1, v_fileName_3233_);
lean_ctor_set(v___x_3242_, 2, v_fst_3237_);
lean_ctor_set(v___x_3242_, 3, v___x_3240_);
return v___x_3242_;
}
else
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3243_, 0, v_source_3239_);
lean_ctor_set(v___x_3243_, 1, v_fileName_3233_);
lean_ctor_set(v___x_3243_, 2, v_fst_3237_);
lean_ctor_set(v___x_3243_, 3, v_snd_3238_);
return v___x_3243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object* v_input_3250_, lean_object* v_fileName_3251_, lean_object* v_normalizeLineEndings_3252_, lean_object* v_endPos_3253_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3254_; lean_object* v_res_3255_; 
v_normalizeLineEndings_boxed_3254_ = lean_unbox(v_normalizeLineEndings_3252_);
v_res_3255_ = l_Lean_Parser_mkInputContext___redArg(v_input_3250_, v_fileName_3251_, v_normalizeLineEndings_boxed_3254_, v_endPos_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object* v_input_3256_, lean_object* v_fileName_3257_, uint8_t v_normalizeLineEndings_3258_, lean_object* v_endPos_3259_, lean_object* v_endPos__valid_3260_){
_start:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Lean_Parser_mkInputContext___redArg(v_input_3256_, v_fileName_3257_, v_normalizeLineEndings_3258_, v_endPos_3259_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object* v_input_3262_, lean_object* v_fileName_3263_, lean_object* v_normalizeLineEndings_3264_, lean_object* v_endPos_3265_, lean_object* v_endPos__valid_3266_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3267_; lean_object* v_res_3268_; 
v_normalizeLineEndings_boxed_3267_ = lean_unbox(v_normalizeLineEndings_3264_);
v_res_3268_ = l_Lean_Parser_mkInputContext(v_input_3262_, v_fileName_3263_, v_normalizeLineEndings_boxed_3267_, v_endPos_3265_, v_endPos__valid_3266_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* v_input_3271_){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3272_ = l_Lean_Parser_SyntaxStack_empty;
v___x_3273_ = lean_unsigned_to_nat(0u);
v___x_3274_ = l_Lean_Parser_initCacheForInput(v_input_3271_);
v___x_3275_ = lean_box(0);
v___x_3276_ = ((lean_object*)(l_Lean_Parser_mkParserState___closed__0));
v___x_3277_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3272_);
lean_ctor_set(v___x_3277_, 1, v___x_3273_);
lean_ctor_set(v___x_3277_, 2, v___x_3273_);
lean_ctor_set(v___x_3277_, 3, v___x_3274_);
lean_ctor_set(v___x_3277_, 4, v___x_3275_);
lean_ctor_set(v___x_3277_, 5, v___x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* v_input_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_Lean_Parser_mkParserState(v_input_3278_);
lean_dec_ref(v_input_3278_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* v_env_3282_, lean_object* v_catName_3283_, lean_object* v_input_3284_, lean_object* v_fileName_3285_){
_start:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v_p_3288_; uint8_t v___x_3289_; lean_object* v___x_3290_; lean_object* v_ictx_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v_s_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
v___x_3286_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__0));
v___x_3287_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 1);
lean_closure_set(v___x_3287_, 0, v_catName_3283_);
v_p_3288_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_3288_, 0, v___x_3286_);
lean_closure_set(v_p_3288_, 1, v___x_3287_);
v___x_3289_ = 1;
v___x_3290_ = lean_string_utf8_byte_size(v_input_3284_);
lean_inc_ref(v_input_3284_);
v_ictx_3291_ = l_Lean_Parser_mkInputContext___redArg(v_input_3284_, v_fileName_3285_, v___x_3289_, v___x_3290_);
v___x_3292_ = l_Lean_Options_empty;
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_box(0);
lean_inc_ref(v_env_3282_);
v___x_3295_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3295_, 0, v_env_3282_);
lean_ctor_set(v___x_3295_, 1, v___x_3292_);
lean_ctor_set(v___x_3295_, 2, v___x_3293_);
lean_ctor_set(v___x_3295_, 3, v___x_3294_);
v___x_3296_ = l_Lean_Parser_getTokenTable(v_env_3282_);
v___x_3297_ = l_Lean_Parser_mkParserState(v_input_3284_);
lean_dec_ref(v_input_3284_);
lean_inc_ref(v_ictx_3291_);
v_s_3298_ = l_Lean_Parser_ParserFn_run(v_p_3288_, v_ictx_3291_, v___x_3295_, v___x_3296_, v___x_3297_);
lean_inc_ref(v_s_3298_);
v___x_3299_ = l_Lean_Parser_ParserState_allErrors(v_s_3298_);
v___x_3300_ = lean_array_get_size(v___x_3299_);
lean_dec_ref(v___x_3299_);
v___x_3301_ = lean_unsigned_to_nat(0u);
v___x_3302_ = lean_nat_dec_eq(v___x_3300_, v___x_3301_);
if (v___x_3302_ == 0)
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3291_, v_s_3298_);
v___x_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
return v___x_3304_;
}
else
{
lean_object* v_stxStack_3305_; lean_object* v_pos_3306_; uint8_t v___x_3307_; 
v_stxStack_3305_ = lean_ctor_get(v_s_3298_, 0);
lean_inc_ref(v_stxStack_3305_);
v_pos_3306_ = lean_ctor_get(v_s_3298_, 2);
lean_inc(v_pos_3306_);
v___x_3307_ = l_Lean_Parser_InputContext_atEnd(v_ictx_3291_, v_pos_3306_);
lean_dec(v_pos_3306_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
lean_dec_ref(v_stxStack_3305_);
v___x_3308_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__1));
v___x_3309_ = l_Lean_Parser_ParserState_mkError(v_s_3298_, v___x_3308_);
v___x_3310_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3291_, v___x_3309_);
v___x_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
return v___x_3311_;
}
else
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_dec_ref(v_s_3298_);
lean_dec_ref(v_ictx_3291_);
v___x_3312_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3305_);
lean_dec_ref(v_stxStack_3305_);
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
return v___x_3313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* v_addFnName_3314_, lean_object* v_catName_3315_, lean_object* v_declName_3316_, lean_object* v_prio_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v_val_3333_; lean_object* v___x_3334_; 
v___x_3321_ = lean_box(0);
v___x_3322_ = l_Lean_mkConst(v_addFnName_3314_, v___x_3321_);
v___x_3323_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_catName_3315_);
lean_inc_n(v_declName_3316_, 2);
v___x_3324_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3316_);
v___x_3325_ = l_Lean_mkConst(v_declName_3316_, v___x_3321_);
v___x_3326_ = l_Lean_mkRawNatLit(v_prio_3317_);
v___x_3327_ = lean_unsigned_to_nat(4u);
v___x_3328_ = lean_mk_empty_array_with_capacity(v___x_3327_);
v___x_3329_ = lean_array_push(v___x_3328_, v___x_3323_);
v___x_3330_ = lean_array_push(v___x_3329_, v___x_3324_);
v___x_3331_ = lean_array_push(v___x_3330_, v___x_3325_);
v___x_3332_ = lean_array_push(v___x_3331_, v___x_3326_);
v_val_3333_ = l_Lean_mkAppN(v___x_3322_, v___x_3332_);
lean_dec_ref(v___x_3332_);
v___x_3334_ = l_Lean_declareBuiltin(v_declName_3316_, v_val_3333_, v_a_3318_, v_a_3319_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object* v_addFnName_3335_, lean_object* v_catName_3336_, lean_object* v_declName_3337_, lean_object* v_prio_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3335_, v_catName_3336_, v_declName_3337_, v_prio_3338_, v_a_3339_, v_a_3340_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* v_catName_3348_, lean_object* v_declName_3349_, lean_object* v_prio_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3354_ = ((lean_object*)(l_Lean_Parser_declareLeadingBuiltinParser___closed__1));
v___x_3355_ = l_Lean_Parser_declareBuiltinParser(v___x_3354_, v_catName_3348_, v_declName_3349_, v_prio_3350_, v_a_3351_, v_a_3352_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object* v_catName_3356_, lean_object* v_declName_3357_, lean_object* v_prio_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3356_, v_declName_3357_, v_prio_3358_, v_a_3359_, v_a_3360_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* v_catName_3368_, lean_object* v_declName_3369_, lean_object* v_prio_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = ((lean_object*)(l_Lean_Parser_declareTrailingBuiltinParser___closed__1));
v___x_3375_ = l_Lean_Parser_declareBuiltinParser(v___x_3374_, v_catName_3368_, v_declName_3369_, v_prio_3370_, v_a_3371_, v_a_3372_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object* v_catName_3376_, lean_object* v_declName_3377_, lean_object* v_prio_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3376_, v_declName_3377_, v_prio_3378_, v_a_3379_, v_a_3380_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* v_args_3389_){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v___x_3390_ = l_Lean_Syntax_getNumArgs(v_args_3389_);
v___x_3391_ = lean_unsigned_to_nat(0u);
v___x_3392_ = lean_nat_dec_eq(v___x_3390_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; uint8_t v___x_3394_; 
v___x_3393_ = lean_unsigned_to_nat(1u);
v___x_3394_ = lean_nat_dec_eq(v___x_3390_, v___x_3393_);
lean_dec(v___x_3390_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; 
v___x_3395_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__1));
return v___x_3395_;
}
else
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = l_Lean_Syntax_getArg(v_args_3389_, v___x_3391_);
v___x_3397_ = l_Lean_Syntax_isNatLit_x3f(v___x_3396_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3398_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__2));
v___x_3399_ = l_Lean_Syntax_formatStx(v___x_3396_, v___x_3397_, v___x_3392_);
v___x_3400_ = l_Std_Format_defWidth;
v___x_3401_ = l_Std_Format_pretty(v___x_3399_, v___x_3400_, v___x_3391_, v___x_3391_);
v___x_3402_ = lean_string_append(v___x_3398_, v___x_3401_);
lean_dec_ref(v___x_3401_);
v___x_3403_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3404_ = lean_string_append(v___x_3402_, v___x_3403_);
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
return v___x_3405_;
}
else
{
lean_object* v_val_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec(v___x_3396_);
v_val_3406_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3397_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_val_3406_);
lean_dec(v___x_3397_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_val_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
}
else
{
lean_object* v___x_3414_; 
lean_dec(v___x_3390_);
v___x_3414_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__3));
return v___x_3414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* v_args_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_Parser_getParserPriority(v_args_3415_);
lean_dec(v_args_3415_);
return v_res_3416_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0));
v___x_3419_ = l_Lean_stringToMessageData(v___x_3418_);
return v___x_3419_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2));
v___x_3422_ = l_Lean_stringToMessageData(v___x_3421_);
return v___x_3422_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3424_ = l_Lean_stringToMessageData(v___x_3423_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object* v_name_3428_, uint8_t v_kind_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___y_3439_; 
v___x_3433_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1);
v___x_3434_ = l_Lean_MessageData_ofName(v_name_3428_);
v___x_3435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3433_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
v___x_3436_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3435_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
switch(v_kind_3429_)
{
case 0:
{
lean_object* v___x_3446_; 
v___x_3446_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5));
v___y_3439_ = v___x_3446_;
goto v___jp_3438_;
}
case 1:
{
lean_object* v___x_3447_; 
v___x_3447_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6));
v___y_3439_ = v___x_3447_;
goto v___jp_3438_;
}
default: 
{
lean_object* v___x_3448_; 
v___x_3448_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7));
v___y_3439_ = v___x_3448_;
goto v___jp_3438_;
}
}
v___jp_3438_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_inc_ref(v___y_3439_);
v___x_3440_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3440_, 0, v___y_3439_);
v___x_3441_ = l_Lean_MessageData_ofFormat(v___x_3440_);
v___x_3442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3437_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
v___x_3443_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3442_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v___x_3445_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3444_, v___y_3430_, v___y_3431_);
return v___x_3445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object* v_name_3449_, lean_object* v_kind_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
uint8_t v_kind_boxed_3454_; lean_object* v_res_3455_; 
v_kind_boxed_3454_ = lean_unbox(v_kind_3450_);
v_res_3455_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3449_, v_kind_boxed_3454_, v___y_3451_, v___y_3452_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3456_, lean_object* v_msg_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_toCold_3461_; lean_object* v_currRecDepth_3462_; lean_object* v_ref_3463_; uint16_t v_optionFlags_3464_; uint8_t v_suppressElabErrors_3465_; uint8_t v_isRecordingDeps_3466_; lean_object* v_ref_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v_toCold_3461_ = lean_ctor_get(v___y_3458_, 0);
v_currRecDepth_3462_ = lean_ctor_get(v___y_3458_, 1);
v_ref_3463_ = lean_ctor_get(v___y_3458_, 2);
v_optionFlags_3464_ = lean_ctor_get_uint16(v___y_3458_, sizeof(void*)*3);
v_suppressElabErrors_3465_ = lean_ctor_get_uint8(v___y_3458_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3466_ = lean_ctor_get_uint8(v___y_3458_, sizeof(void*)*3 + 3);
v_ref_3467_ = l_Lean_replaceRef(v_ref_3456_, v_ref_3463_);
lean_inc(v_currRecDepth_3462_);
lean_inc_ref(v_toCold_3461_);
v___x_3468_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3468_, 0, v_toCold_3461_);
lean_ctor_set(v___x_3468_, 1, v_currRecDepth_3462_);
lean_ctor_set(v___x_3468_, 2, v_ref_3467_);
lean_ctor_set_uint16(v___x_3468_, sizeof(void*)*3, v_optionFlags_3464_);
lean_ctor_set_uint8(v___x_3468_, sizeof(void*)*3 + 2, v_suppressElabErrors_3465_);
lean_ctor_set_uint8(v___x_3468_, sizeof(void*)*3 + 3, v_isRecordingDeps_3466_);
v___x_3469_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_3457_, v___x_3468_, v___y_3459_);
lean_dec_ref_known(v___x_3468_, 3);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3470_, lean_object* v_msg_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3470_, v_msg_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v_ref_3470_);
return v_res_3475_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_3478_ = l_Lean_stringToMessageData(v___x_3477_);
return v___x_3478_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_3481_ = l_Lean_stringToMessageData(v___x_3480_);
return v___x_3481_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_3484_ = l_Lean_stringToMessageData(v___x_3483_);
return v___x_3484_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_3487_ = l_Lean_stringToMessageData(v___x_3486_);
return v___x_3487_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_3490_ = l_Lean_stringToMessageData(v___x_3489_);
return v___x_3490_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_3493_ = l_Lean_stringToMessageData(v___x_3492_);
return v___x_3493_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_3496_ = l_Lean_stringToMessageData(v___x_3495_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_3497_, lean_object* v_declHint_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v_env_3503_; uint8_t v___x_3504_; 
v___x_3501_ = lean_box(0);
v___x_3502_ = lean_st_ref_get(v___y_3499_);
v_env_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc_ref(v_env_3503_);
lean_dec(v___x_3502_);
v___x_3504_ = l_Lean_Name_isAnonymous(v_declHint_3498_);
if (v___x_3504_ == 0)
{
uint8_t v_isExporting_3505_; 
v_isExporting_3505_ = lean_ctor_get_uint8(v_env_3503_, sizeof(void*)*8);
if (v_isExporting_3505_ == 0)
{
lean_object* v___x_3506_; 
lean_dec_ref(v_env_3503_);
lean_dec(v_declHint_3498_);
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v_msg_3497_);
return v___x_3506_;
}
else
{
lean_object* v___x_3507_; uint8_t v___x_3508_; 
lean_inc_ref(v_env_3503_);
v___x_3507_ = l_Lean_Environment_setExporting(v_env_3503_, v___x_3504_);
lean_inc(v_declHint_3498_);
lean_inc_ref(v___x_3507_);
v___x_3508_ = l_Lean_Environment_contains(v___x_3507_, v_declHint_3498_, v_isExporting_3505_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; 
lean_dec_ref(v___x_3507_);
lean_dec_ref(v_env_3503_);
lean_dec(v_declHint_3498_);
v___x_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3509_, 0, v_msg_3497_);
return v___x_3509_;
}
else
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v_c_3515_; lean_object* v___x_3516_; 
v___x_3510_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_3511_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_3512_ = l_Lean_Options_empty;
v___x_3513_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3507_);
lean_ctor_set(v___x_3513_, 1, v___x_3510_);
lean_ctor_set(v___x_3513_, 2, v___x_3511_);
lean_ctor_set(v___x_3513_, 3, v___x_3512_);
lean_inc(v_declHint_3498_);
v___x_3514_ = l_Lean_MessageData_ofConstName(v_declHint_3498_, v___x_3504_);
v_c_3515_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3515_, 0, v___x_3513_);
lean_ctor_set(v_c_3515_, 1, v___x_3514_);
v___x_3516_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3503_, v_declHint_3498_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_dec_ref(v_env_3503_);
lean_dec(v_declHint_3498_);
v___x_3517_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
lean_ctor_set(v___x_3518_, 1, v_c_3515_);
v___x_3519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_3520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = l_Lean_MessageData_note(v___x_3520_);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v_msg_3497_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
return v___x_3523_;
}
else
{
lean_object* v_val_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3558_; 
v_val_3524_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3526_ = v___x_3516_;
v_isShared_3527_ = v_isSharedCheck_3558_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_val_3524_);
lean_dec(v___x_3516_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3558_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_mod_3530_; uint8_t v___x_3531_; 
v___x_3528_ = l_Lean_Environment_header(v_env_3503_);
lean_dec_ref(v_env_3503_);
v___x_3529_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3528_);
v_mod_3530_ = lean_array_get(v___x_3501_, v___x_3529_, v_val_3524_);
lean_dec(v_val_3524_);
lean_dec_ref(v___x_3529_);
v___x_3531_ = l_Lean_isPrivateName(v_declHint_3498_);
lean_dec(v_declHint_3498_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3532_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
lean_ctor_set(v___x_3533_, 1, v_c_3515_);
v___x_3534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = l_Lean_MessageData_ofName(v_mod_3530_);
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3535_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
v___x_3538_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_3539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3537_);
lean_ctor_set(v___x_3539_, 1, v___x_3538_);
v___x_3540_ = l_Lean_MessageData_note(v___x_3539_);
v___x_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3541_, 0, v_msg_3497_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set_tag(v___x_3526_, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3541_);
v___x_3543_ = v___x_3526_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
else
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3545_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
lean_ctor_set(v___x_3546_, 1, v_c_3515_);
v___x_3547_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_3548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3546_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = l_Lean_MessageData_ofName(v_mod_3530_);
v___x_3550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3548_);
lean_ctor_set(v___x_3550_, 1, v___x_3549_);
v___x_3551_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_3552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3550_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = l_Lean_MessageData_note(v___x_3552_);
v___x_3554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3554_, 0, v_msg_3497_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set_tag(v___x_3526_, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3554_);
v___x_3556_ = v___x_3526_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3559_; 
lean_dec_ref(v_env_3503_);
lean_dec(v_declHint_3498_);
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v_msg_3497_);
return v___x_3559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_3560_, lean_object* v_declHint_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3560_, v_declHint_3561_, v___y_3562_);
lean_dec(v___y_3562_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_3565_, lean_object* v_declHint_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___x_3570_; lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3580_; 
v___x_3570_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3565_, v_declHint_3566_, v___y_3568_);
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3573_ = v___x_3570_;
v_isShared_3574_ = v_isSharedCheck_3580_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3570_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3580_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3578_; 
v___x_3575_ = l_Lean_unknownIdentifierMessageTag;
v___x_3576_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
lean_ctor_set(v___x_3576_, 1, v_a_3571_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3576_);
v___x_3578_ = v___x_3573_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_3581_, lean_object* v_declHint_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3581_, v_declHint_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3587_, lean_object* v_msg_3588_, lean_object* v_declHint_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v___x_3593_; lean_object* v_a_3594_; lean_object* v___x_3595_; 
v___x_3593_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3588_, v_declHint_3589_, v___y_3590_, v___y_3591_);
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3587_, v_a_3594_, v___y_3590_, v___y_3591_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3596_, lean_object* v_msg_3597_, lean_object* v_declHint_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3596_, v_msg_3597_, v_declHint_3598_, v___y_3599_, v___y_3600_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v_ref_3596_);
return v_res_3602_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_3604_ = l_Lean_stringToMessageData(v___x_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3605_, lean_object* v_constName_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v___x_3610_; uint8_t v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3610_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3611_ = 0;
lean_inc(v_constName_3606_);
v___x_3612_ = l_Lean_MessageData_ofConstName(v_constName_3606_, v___x_3611_);
v___x_3613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3610_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3613_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3605_, v___x_3615_, v_constName_3606_, v___y_3607_, v___y_3608_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3617_, lean_object* v_constName_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3617_, v_constName_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v_ref_3617_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object* v_constName_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_ref_3627_; lean_object* v___x_3628_; 
v_ref_3627_ = lean_ctor_get(v___y_3624_, 2);
v___x_3628_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3627_, v_constName_3623_, v___y_3624_, v___y_3625_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3629_, v___y_3630_, v___y_3631_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object* v_constName_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v___x_3638_; lean_object* v_env_3639_; uint8_t v___x_3640_; lean_object* v___x_3641_; 
v___x_3638_ = lean_st_ref_get(v___y_3636_);
v_env_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc_ref(v_env_3639_);
lean_dec(v___x_3638_);
v___x_3640_ = 0;
lean_inc(v_constName_3634_);
v___x_3641_ = l_Lean_Environment_find_x3f(v_env_3639_, v_constName_3634_, v___x_3640_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3634_, v___y_3635_, v___y_3636_);
return v___x_3642_;
}
else
{
lean_object* v_val_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
lean_dec(v_constName_3634_);
v_val_3643_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3641_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_val_3643_);
lean_dec(v___x_3641_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 0);
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_val_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object* v_constName_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3651_, v___y_3652_, v___y_3653_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
return v_res_3655_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1(void){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0));
v___x_3658_ = l_Lean_stringToMessageData(v___x_3657_);
return v___x_3658_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2));
v___x_3661_ = l_Lean_stringToMessageData(v___x_3660_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* v_attrName_3662_, lean_object* v_catName_3663_, lean_object* v_declName_3664_, lean_object* v_stx_3665_, uint8_t v_kind_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___x_3690_; 
v___x_3690_ = l_Lean_Attribute_Builtin_getPrio(v_stx_3665_, v_a_3667_, v_a_3668_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; lean_object* v___y_3693_; lean_object* v___y_3694_; uint8_t v___x_3722_; uint8_t v___x_3723_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___x_3690_, 1);
v___x_3722_ = 0;
v___x_3723_ = l_Lean_instBEqAttributeKind_beq(v_kind_3666_, v___x_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; 
lean_dec(v_a_3691_);
lean_dec(v_declName_3664_);
lean_dec(v_catName_3663_);
v___x_3724_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_attrName_3662_, v_kind_3666_, v_a_3667_, v_a_3668_);
return v___x_3724_;
}
else
{
lean_dec(v_attrName_3662_);
v___y_3693_ = v_a_3667_;
v___y_3694_ = v_a_3668_;
goto v___jp_3692_;
}
v___jp_3692_:
{
lean_object* v___x_3695_; 
lean_inc(v_declName_3664_);
v___x_3695_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_declName_3664_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3697_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___x_3695_, 1);
v___x_3697_ = l_Lean_ConstantInfo_type(v_a_3696_);
if (lean_obj_tag(v___x_3697_) == 4)
{
lean_object* v_declName_3698_; 
v_declName_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_declName_3698_);
lean_dec_ref_known(v___x_3697_, 2);
if (lean_obj_tag(v_declName_3698_) == 1)
{
lean_object* v_pre_3699_; 
v_pre_3699_ = lean_ctor_get(v_declName_3698_, 0);
lean_inc(v_pre_3699_);
if (lean_obj_tag(v_pre_3699_) == 1)
{
lean_object* v_pre_3700_; 
v_pre_3700_ = lean_ctor_get(v_pre_3699_, 0);
lean_inc(v_pre_3700_);
if (lean_obj_tag(v_pre_3700_) == 1)
{
lean_object* v_pre_3701_; 
v_pre_3701_ = lean_ctor_get(v_pre_3700_, 0);
if (lean_obj_tag(v_pre_3701_) == 0)
{
lean_object* v_str_3702_; lean_object* v_str_3703_; lean_object* v_str_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v_str_3702_ = lean_ctor_get(v_declName_3698_, 1);
lean_inc_ref(v_str_3702_);
lean_dec_ref_known(v_declName_3698_, 2);
v_str_3703_ = lean_ctor_get(v_pre_3699_, 1);
lean_inc_ref(v_str_3703_);
lean_dec_ref_known(v_pre_3699_, 2);
v_str_3704_ = lean_ctor_get(v_pre_3700_, 1);
lean_inc_ref(v_str_3704_);
lean_dec_ref_known(v_pre_3700_, 2);
v___x_3705_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3706_ = lean_string_dec_eq(v_str_3704_, v___x_3705_);
lean_dec_ref(v_str_3704_);
if (v___x_3706_ == 0)
{
lean_dec_ref(v_str_3703_);
lean_dec_ref(v_str_3702_);
lean_dec(v_a_3691_);
lean_dec(v_catName_3663_);
v___y_3677_ = v_a_3696_;
v___y_3678_ = v___y_3693_;
v___y_3679_ = v___y_3694_;
goto v___jp_3676_;
}
else
{
lean_object* v___x_3707_; uint8_t v___x_3708_; 
v___x_3707_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3708_ = lean_string_dec_eq(v_str_3703_, v___x_3707_);
lean_dec_ref(v_str_3703_);
if (v___x_3708_ == 0)
{
lean_dec_ref(v_str_3702_);
lean_dec(v_a_3691_);
lean_dec(v_catName_3663_);
v___y_3677_ = v_a_3696_;
v___y_3678_ = v___y_3693_;
v___y_3679_ = v___y_3694_;
goto v___jp_3676_;
}
else
{
lean_object* v___x_3709_; uint8_t v___x_3710_; 
v___x_3709_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_3710_ = lean_string_dec_eq(v_str_3702_, v___x_3709_);
if (v___x_3710_ == 0)
{
uint8_t v___x_3711_; 
v___x_3711_ = lean_string_dec_eq(v_str_3702_, v___x_3707_);
lean_dec_ref(v_str_3702_);
if (v___x_3711_ == 0)
{
lean_dec(v_a_3691_);
lean_dec(v_catName_3663_);
v___y_3677_ = v_a_3696_;
v___y_3678_ = v___y_3693_;
v___y_3679_ = v___y_3694_;
goto v___jp_3676_;
}
else
{
lean_object* v___x_3712_; 
lean_dec(v_a_3696_);
lean_inc(v_declName_3664_);
lean_inc(v_catName_3663_);
v___x_3712_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3663_, v_declName_3664_, v_a_3691_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_dec_ref_known(v___x_3712_, 1);
v___y_3671_ = v___y_3693_;
v___y_3672_ = v___y_3694_;
goto v___jp_3670_;
}
else
{
lean_dec(v_declName_3664_);
lean_dec(v_catName_3663_);
return v___x_3712_;
}
}
}
else
{
lean_object* v___x_3713_; 
lean_dec_ref(v_str_3702_);
lean_dec(v_a_3696_);
lean_inc(v_declName_3664_);
lean_inc(v_catName_3663_);
v___x_3713_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3663_, v_declName_3664_, v_a_3691_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_dec_ref_known(v___x_3713_, 1);
v___y_3671_ = v___y_3693_;
v___y_3672_ = v___y_3694_;
goto v___jp_3670_;
}
else
{
lean_dec(v_declName_3664_);
lean_dec(v_catName_3663_);
return v___x_3713_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3700_, 2);
lean_dec_ref_known(v_pre_3699_, 2);
lean_dec_ref_known(v_declName_3698_, 2);
lean_dec(v_a_3691_);
lean_dec(v_catName_3663_);
v___y_3677_ = v_a_3696_;
v___y_3678_ = v___y_3693_;
v___y_3679_ = v___y_3694_;
goto v___jp_3676_;
}
}
else
{
lean_dec_ref_known(v_pre_3699_, 2);
lean_dec(v_pre_3700_);
lean_dec_ref_known(v_declName_3698_, 2);
lean_dec(v_a_3691_);
lean_dec(v_catName_3663_);
v___y_3677_ = v_a_3696_;
v___y_3678_ = v___y_3693_;
v___y_3679_ = v___y_3694_;
goto v___jp_3676_;
}
}
else
{
lean_dec(v_pre_3699_);
lean_dec_ref_known(v_declName_3698_, 2);
lean_dec(v_a_3691_);
lean_dec(v_catName_3663_);
v___y_3677_ = v_a_3696_;
v___y_3678_ = v___y_3693_;
v___y_3679_ = v___y_3694_;
goto v___jp_3676_;
}
}
else
{
lean_dec(v_declName_3698_);
lean_dec(v_a_3691_);
lean_dec(v_catName_3663_);
v___y_3677_ = v_a_3696_;
v___y_3678_ = v___y_3693_;
v___y_3679_ = v___y_3694_;
goto v___jp_3676_;
}
}
else
{
lean_dec_ref(v___x_3697_);
lean_dec(v_a_3691_);
lean_dec(v_catName_3663_);
v___y_3677_ = v_a_3696_;
v___y_3678_ = v___y_3693_;
v___y_3679_ = v___y_3694_;
goto v___jp_3676_;
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_dec(v_a_3691_);
lean_dec(v_declName_3664_);
lean_dec(v_catName_3663_);
v_a_3714_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3695_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3695_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec(v_declName_3664_);
lean_dec(v_catName_3663_);
lean_dec(v_attrName_3662_);
v_a_3725_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3690_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3690_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
v___jp_3670_:
{
lean_object* v___x_3673_; 
lean_inc(v_declName_3664_);
v___x_3673_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_3664_, v___y_3671_, v___y_3672_);
if (lean_obj_tag(v___x_3673_) == 0)
{
uint8_t v___x_3674_; lean_object* v___x_3675_; 
lean_dec_ref_known(v___x_3673_, 1);
v___x_3674_ = 1;
v___x_3675_ = l_Lean_Parser_runParserAttributeHooks(v_catName_3663_, v_declName_3664_, v___x_3674_, v___y_3671_, v___y_3672_);
return v___x_3675_;
}
else
{
lean_dec(v_declName_3664_);
lean_dec(v_catName_3663_);
return v___x_3673_;
}
}
v___jp_3676_:
{
lean_object* v___x_3680_; uint8_t v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3680_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
v___x_3681_ = 0;
v___x_3682_ = l_Lean_MessageData_ofConstName(v_declName_3664_, v___x_3681_);
v___x_3683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3680_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
v___x_3685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3683_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = l_Lean_ConstantInfo_type(v___y_3677_);
lean_dec_ref(v___y_3677_);
v___x_3687_ = l_Lean_indentExpr(v___x_3686_);
v___x_3688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3685_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3688_, v___y_3678_, v___y_3679_);
return v___x_3689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* v_attrName_3733_, lean_object* v_catName_3734_, lean_object* v_declName_3735_, lean_object* v_stx_3736_, lean_object* v_kind_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
uint8_t v_kind_boxed_3741_; lean_object* v_res_3742_; 
v_kind_boxed_3741_ = lean_unbox(v_kind_3737_);
v_res_3742_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3733_, v_catName_3734_, v_declName_3735_, v_stx_3736_, v_kind_boxed_3741_, v_a_3738_, v_a_3739_);
lean_dec(v_a_3739_);
lean_dec_ref(v_a_3738_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object* v_00_u03b1_3743_, lean_object* v_name_3744_, uint8_t v_kind_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3744_, v_kind_3745_, v___y_3746_, v___y_3747_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b1_3750_, lean_object* v_name_3751_, lean_object* v_kind_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
uint8_t v_kind_boxed_3756_; lean_object* v_res_3757_; 
v_kind_boxed_3756_ = lean_unbox(v_kind_3752_);
v_res_3757_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(v_00_u03b1_3750_, v_name_3751_, v_kind_boxed_3756_, v___y_3753_, v___y_3754_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object* v_00_u03b1_3758_, lean_object* v_constName_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3759_, v___y_3760_, v___y_3761_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3764_, lean_object* v_constName_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(v_00_u03b1_3764_, v_constName_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3770_, lean_object* v_ref_3771_, lean_object* v_constName_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3771_, v_constName_3772_, v___y_3773_, v___y_3774_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3777_, lean_object* v_ref_3778_, lean_object* v_constName_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(v_00_u03b1_3777_, v_ref_3778_, v_constName_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v_ref_3778_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3784_, lean_object* v_ref_3785_, lean_object* v_msg_3786_, lean_object* v_declHint_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3785_, v_msg_3786_, v_declHint_3787_, v___y_3788_, v___y_3789_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3792_, lean_object* v_ref_3793_, lean_object* v_msg_3794_, lean_object* v_declHint_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3792_, v_ref_3793_, v_msg_3794_, v_declHint_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v_ref_3793_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_3800_, lean_object* v_declHint_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v___x_3805_; 
v___x_3805_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3800_, v_declHint_3801_, v___y_3803_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_3806_, lean_object* v_declHint_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_3806_, v_declHint_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3812_, lean_object* v_ref_3813_, lean_object* v_msg_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3813_, v_msg_3814_, v___y_3815_, v___y_3816_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3819_, lean_object* v_ref_3820_, lean_object* v_msg_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3819_, v_ref_3820_, v_msg_3821_, v___y_3822_, v___y_3823_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v_ref_3820_);
return v_res_3825_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2(void){
_start:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3832_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0));
v___x_3833_ = l_Lean_mkAtom(v___x_3832_);
return v___x_3833_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3834_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2);
v___x_3835_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3836_ = lean_array_push(v___x_3835_, v___x_3834_);
return v___x_3836_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7));
v___x_3846_ = l_Lean_mkAtom(v___x_3845_);
return v___x_3846_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3847_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8);
v___x_3848_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3849_ = lean_array_push(v___x_3848_, v___x_3847_);
return v___x_3849_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3850_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9);
v___x_3851_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6));
v___x_3852_ = lean_box(2);
v___x_3853_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
lean_ctor_set(v___x_3853_, 1, v___x_3851_);
lean_ctor_set(v___x_3853_, 2, v___x_3850_);
return v___x_3853_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3854_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10);
v___x_3855_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3);
v___x_3856_ = lean_array_push(v___x_3855_, v___x_3854_);
return v___x_3856_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3857_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11);
v___x_3858_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1));
v___x_3859_ = lean_box(2);
v___x_3860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3859_);
lean_ctor_set(v___x_3860_, 1, v___x_3858_);
lean_ctor_set(v___x_3860_, 2, v___x_3857_);
return v___x_3860_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3861_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12);
v___x_3862_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3863_ = lean_array_push(v___x_3862_, v___x_3861_);
return v___x_3863_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3864_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13);
v___x_3865_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3866_ = lean_box(2);
v___x_3867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
lean_ctor_set(v___x_3867_, 1, v___x_3865_);
lean_ctor_set(v___x_3867_, 2, v___x_3864_);
return v___x_3867_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3868_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14);
v___x_3869_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3870_ = lean_array_push(v___x_3869_, v___x_3868_);
return v___x_3870_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3871_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15);
v___x_3872_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3873_ = lean_box(2);
v___x_3874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
lean_ctor_set(v___x_3874_, 1, v___x_3872_);
lean_ctor_set(v___x_3874_, 2, v___x_3871_);
return v___x_3874_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3875_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16);
v___x_3876_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3877_ = lean_array_push(v___x_3876_, v___x_3875_);
return v___x_3877_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3878_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17);
v___x_3879_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3880_ = lean_box(2);
v___x_3881_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
lean_ctor_set(v___x_3881_, 1, v___x_3879_);
lean_ctor_set(v___x_3881_, 2, v___x_3878_);
return v___x_3881_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object* v_attrName_3883_, lean_object* v_decl_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3888_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3889_ = l_Lean_MessageData_ofName(v_attrName_3883_);
v___x_3890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3888_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3890_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
v___x_3893_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3892_, v___y_3885_, v___y_3886_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object* v_attrName_3894_, lean_object* v_decl_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_3894_, v_decl_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v_decl_3895_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object* v_attrName_3900_, lean_object* v_catName_3901_, lean_object* v_declName_3902_, lean_object* v_stx_3903_, uint8_t v_kind_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3900_, v_catName_3901_, v_declName_3902_, v_stx_3903_, v_kind_3904_, v___y_3905_, v___y_3906_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object* v_attrName_3909_, lean_object* v_catName_3910_, lean_object* v_declName_3911_, lean_object* v_stx_3912_, lean_object* v_kind_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
uint8_t v_kind_boxed_3917_; lean_object* v_res_3918_; 
v_kind_boxed_3917_ = lean_unbox(v_kind_3913_);
v_res_3918_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_3909_, v_catName_3910_, v_declName_3911_, v_stx_3912_, v_kind_boxed_3917_, v___y_3914_, v___y_3915_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
return v_res_3918_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__0));
v___x_3921_ = lean_mk_io_user_error(v___x_3920_);
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* v_attrName_3924_, lean_object* v_declName_3925_, uint8_t v_behavior_3926_, lean_object* v_ref_3927_){
_start:
{
if (lean_obj_tag(v_declName_3925_) == 1)
{
lean_object* v_pre_3932_; 
v_pre_3932_ = lean_ctor_get(v_declName_3925_, 0);
if (lean_obj_tag(v_pre_3932_) == 1)
{
lean_object* v_pre_3933_; 
v_pre_3933_ = lean_ctor_get(v_pre_3932_, 0);
if (lean_obj_tag(v_pre_3933_) == 1)
{
lean_object* v_pre_3934_; 
v_pre_3934_ = lean_ctor_get(v_pre_3933_, 0);
if (lean_obj_tag(v_pre_3934_) == 1)
{
lean_object* v_pre_3935_; 
v_pre_3935_ = lean_ctor_get(v_pre_3934_, 0);
if (lean_obj_tag(v_pre_3935_) == 0)
{
lean_object* v_str_3936_; lean_object* v_str_3937_; lean_object* v_str_3938_; lean_object* v_str_3939_; lean_object* v___x_3940_; uint8_t v___x_3941_; 
v_str_3936_ = lean_ctor_get(v_declName_3925_, 1);
v_str_3937_ = lean_ctor_get(v_pre_3932_, 1);
v_str_3938_ = lean_ctor_get(v_pre_3933_, 1);
v_str_3939_ = lean_ctor_get(v_pre_3934_, 1);
v___x_3940_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3941_ = lean_string_dec_eq(v_str_3939_, v___x_3940_);
if (v___x_3941_ == 0)
{
lean_dec_ref_known(v_declName_3925_, 2);
lean_dec(v_ref_3927_);
lean_dec(v_attrName_3924_);
goto v___jp_3929_;
}
else
{
lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___x_3942_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3943_ = lean_string_dec_eq(v_str_3938_, v___x_3942_);
if (v___x_3943_ == 0)
{
lean_dec_ref_known(v_declName_3925_, 2);
lean_dec(v_ref_3927_);
lean_dec(v_attrName_3924_);
goto v___jp_3929_;
}
else
{
lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3944_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__2));
v___x_3945_ = lean_string_dec_eq(v_str_3937_, v___x_3944_);
if (v___x_3945_ == 0)
{
lean_dec_ref_known(v_declName_3925_, 2);
lean_dec(v_ref_3927_);
lean_dec(v_attrName_3924_);
goto v___jp_3929_;
}
else
{
lean_object* v___f_3946_; lean_object* v___x_3947_; lean_object* v_catName_3948_; lean_object* v___f_3949_; lean_object* v___x_3950_; 
lean_inc_n(v_attrName_3924_, 2);
v___f_3946_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3946_, 0, v_attrName_3924_);
v___x_3947_ = lean_box(0);
lean_inc_ref(v_str_3936_);
v_catName_3948_ = l_Lean_Name_str___override(v___x_3947_, v_str_3936_);
lean_inc(v_catName_3948_);
v___f_3949_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3949_, 0, v_attrName_3924_);
lean_closure_set(v___f_3949_, 1, v_catName_3948_);
v___x_3950_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_3948_, v_declName_3925_, v_behavior_3926_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v___x_3951_; uint8_t v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
lean_dec_ref_known(v___x_3950_, 1);
v___x_3951_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__3));
v___x_3952_ = 1;
v___x_3953_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3953_, 0, v_ref_3927_);
lean_ctor_set(v___x_3953_, 1, v_attrName_3924_);
lean_ctor_set(v___x_3953_, 2, v___x_3951_);
lean_ctor_set_uint8(v___x_3953_, sizeof(void*)*3, v___x_3952_);
v___x_3954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
lean_ctor_set(v___x_3954_, 1, v___f_3949_);
lean_ctor_set(v___x_3954_, 2, v___f_3946_);
v___x_3955_ = l_Lean_registerBuiltinAttribute(v___x_3954_);
return v___x_3955_;
}
else
{
lean_dec_ref(v___f_3949_);
lean_dec_ref(v___f_3946_);
lean_dec(v_ref_3927_);
lean_dec(v_attrName_3924_);
return v___x_3950_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_declName_3925_, 2);
lean_dec(v_ref_3927_);
lean_dec(v_attrName_3924_);
goto v___jp_3929_;
}
}
else
{
lean_dec_ref_known(v_declName_3925_, 2);
lean_dec(v_ref_3927_);
lean_dec(v_attrName_3924_);
goto v___jp_3929_;
}
}
else
{
lean_dec_ref_known(v_declName_3925_, 2);
lean_dec(v_ref_3927_);
lean_dec(v_attrName_3924_);
goto v___jp_3929_;
}
}
else
{
lean_dec_ref_known(v_declName_3925_, 2);
lean_dec(v_ref_3927_);
lean_dec(v_attrName_3924_);
goto v___jp_3929_;
}
}
else
{
lean_dec(v_ref_3927_);
lean_dec(v_declName_3925_);
lean_dec(v_attrName_3924_);
goto v___jp_3929_;
}
v___jp_3929_:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3930_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___closed__1, &l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
v___x_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
return v___x_3931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* v_attrName_3956_, lean_object* v_declName_3957_, lean_object* v_behavior_3958_, lean_object* v_ref_3959_, lean_object* v_a_3960_){
_start:
{
uint8_t v_behavior_boxed_3961_; lean_object* v_res_3962_; 
v_behavior_boxed_3961_ = lean_unbox(v_behavior_3958_);
v_res_3962_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_3956_, v_declName_3957_, v_behavior_boxed_3961_, v_ref_3959_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object* v_kind_3963_, lean_object* v_x_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v___x_3968_; lean_object* v_env_3969_; lean_object* v_nextMacroScope_3970_; lean_object* v_ngen_3971_; lean_object* v_auxDeclNGen_3972_; lean_object* v_traceState_3973_; lean_object* v_recordedDeps_3974_; lean_object* v_messages_3975_; lean_object* v_infoState_3976_; lean_object* v_snapshotTasks_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3989_; 
v___x_3968_ = lean_st_ref_take(v___y_3966_);
v_env_3969_ = lean_ctor_get(v___x_3968_, 0);
v_nextMacroScope_3970_ = lean_ctor_get(v___x_3968_, 1);
v_ngen_3971_ = lean_ctor_get(v___x_3968_, 2);
v_auxDeclNGen_3972_ = lean_ctor_get(v___x_3968_, 3);
v_traceState_3973_ = lean_ctor_get(v___x_3968_, 4);
v_recordedDeps_3974_ = lean_ctor_get(v___x_3968_, 6);
v_messages_3975_ = lean_ctor_get(v___x_3968_, 7);
v_infoState_3976_ = lean_ctor_get(v___x_3968_, 8);
v_snapshotTasks_3977_ = lean_ctor_get(v___x_3968_, 9);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3989_ == 0)
{
lean_object* v_unused_3990_; 
v_unused_3990_ = lean_ctor_get(v___x_3968_, 5);
lean_dec(v_unused_3990_);
v___x_3979_ = v___x_3968_;
v_isShared_3980_ = v_isSharedCheck_3989_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_snapshotTasks_3977_);
lean_inc(v_infoState_3976_);
lean_inc(v_messages_3975_);
lean_inc(v_recordedDeps_3974_);
lean_inc(v_traceState_3973_);
lean_inc(v_auxDeclNGen_3972_);
lean_inc(v_ngen_3971_);
lean_inc(v_nextMacroScope_3970_);
lean_inc(v_env_3969_);
lean_dec(v___x_3968_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3989_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3985_; 
v___x_3981_ = lean_box(0);
v___x_3982_ = l_Lean_Parser_addSyntaxNodeKind(v_env_3969_, v_kind_3963_);
v___x_3983_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 5, v___x_3983_);
lean_ctor_set(v___x_3979_, 0, v___x_3982_);
v___x_3985_ = v___x_3979_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v___x_3982_);
lean_ctor_set(v_reuseFailAlloc_3988_, 1, v_nextMacroScope_3970_);
lean_ctor_set(v_reuseFailAlloc_3988_, 2, v_ngen_3971_);
lean_ctor_set(v_reuseFailAlloc_3988_, 3, v_auxDeclNGen_3972_);
lean_ctor_set(v_reuseFailAlloc_3988_, 4, v_traceState_3973_);
lean_ctor_set(v_reuseFailAlloc_3988_, 5, v___x_3983_);
lean_ctor_set(v_reuseFailAlloc_3988_, 6, v_recordedDeps_3974_);
lean_ctor_set(v_reuseFailAlloc_3988_, 7, v_messages_3975_);
lean_ctor_set(v_reuseFailAlloc_3988_, 8, v_infoState_3976_);
lean_ctor_set(v_reuseFailAlloc_3988_, 9, v_snapshotTasks_3977_);
v___x_3985_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3986_ = lean_st_ref_put(v___y_3966_, v___x_3985_);
v___x_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3981_);
return v___x_3987_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object* v_kind_3991_, lean_object* v_x_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_3991_, v_x_3992_, v___y_3993_, v___y_3994_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_3997_, lean_object* v_keys_3998_, lean_object* v_vals_3999_, lean_object* v_i_4000_, lean_object* v_acc_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v___x_4005_; uint8_t v___x_4006_; 
v___x_4005_ = lean_array_get_size(v_keys_3998_);
v___x_4006_ = lean_nat_dec_lt(v_i_4000_, v___x_4005_);
if (v___x_4006_ == 0)
{
lean_object* v___x_4007_; 
lean_dec(v_i_4000_);
lean_dec_ref(v_f_3997_);
v___x_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4007_, 0, v_acc_4001_);
return v___x_4007_;
}
else
{
lean_object* v_k_4008_; lean_object* v_v_4009_; lean_object* v___x_4010_; 
v_k_4008_ = lean_array_fget_borrowed(v_keys_3998_, v_i_4000_);
v_v_4009_ = lean_array_fget_borrowed(v_vals_3999_, v_i_4000_);
lean_inc_ref(v_f_3997_);
lean_inc(v___y_4003_);
lean_inc_ref(v___y_4002_);
lean_inc(v_v_4009_);
lean_inc(v_k_4008_);
v___x_4010_ = lean_apply_6(v_f_3997_, v_acc_4001_, v_k_4008_, v_v_4009_, v___y_4002_, v___y_4003_, lean_box(0));
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v___x_4012_ = lean_unsigned_to_nat(1u);
v___x_4013_ = lean_nat_add(v_i_4000_, v___x_4012_);
lean_dec(v_i_4000_);
v_i_4000_ = v___x_4013_;
v_acc_4001_ = v_a_4011_;
goto _start;
}
else
{
lean_dec(v_i_4000_);
lean_dec_ref(v_f_3997_);
return v___x_4010_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_4015_, lean_object* v_keys_4016_, lean_object* v_vals_4017_, lean_object* v_i_4018_, lean_object* v_acc_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4015_, v_keys_4016_, v_vals_4017_, v_i_4018_, v_acc_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec_ref(v_vals_4017_);
lean_dec_ref(v_keys_4016_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_4024_, lean_object* v_as_4025_, size_t v_i_4026_, size_t v_stop_4027_, lean_object* v_b_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_a_4033_; lean_object* v___y_4038_; uint8_t v___x_4040_; 
v___x_4040_ = lean_usize_dec_eq(v_i_4026_, v_stop_4027_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4041_; 
v___x_4041_ = lean_array_uget_borrowed(v_as_4025_, v_i_4026_);
switch(lean_obj_tag(v___x_4041_))
{
case 0:
{
lean_object* v_key_4042_; lean_object* v_val_4043_; lean_object* v___x_4044_; 
v_key_4042_ = lean_ctor_get(v___x_4041_, 0);
v_val_4043_ = lean_ctor_get(v___x_4041_, 1);
lean_inc_ref(v_f_4024_);
lean_inc(v___y_4030_);
lean_inc_ref(v___y_4029_);
lean_inc(v_val_4043_);
lean_inc(v_key_4042_);
v___x_4044_ = lean_apply_6(v_f_4024_, v_b_4028_, v_key_4042_, v_val_4043_, v___y_4029_, v___y_4030_, lean_box(0));
v___y_4038_ = v___x_4044_;
goto v___jp_4037_;
}
case 1:
{
lean_object* v_node_4045_; lean_object* v___x_4046_; 
v_node_4045_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_node_4045_);
lean_inc_ref(v_f_4024_);
v___x_4046_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4024_, v_node_4045_, v_b_4028_, v___y_4029_, v___y_4030_);
v___y_4038_ = v___x_4046_;
goto v___jp_4037_;
}
default: 
{
v_a_4033_ = v_b_4028_;
goto v___jp_4032_;
}
}
}
else
{
lean_object* v___x_4047_; 
lean_dec_ref(v_f_4024_);
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v_b_4028_);
return v___x_4047_;
}
v___jp_4032_:
{
size_t v___x_4034_; size_t v___x_4035_; 
v___x_4034_ = ((size_t)1ULL);
v___x_4035_ = lean_usize_add(v_i_4026_, v___x_4034_);
v_i_4026_ = v___x_4035_;
v_b_4028_ = v_a_4033_;
goto _start;
}
v___jp_4037_:
{
if (lean_obj_tag(v___y_4038_) == 0)
{
lean_object* v_a_4039_; 
v_a_4039_ = lean_ctor_get(v___y_4038_, 0);
lean_inc(v_a_4039_);
lean_dec_ref_known(v___y_4038_, 1);
v_a_4033_ = v_a_4039_;
goto v___jp_4032_;
}
else
{
lean_dec_ref(v_f_4024_);
return v___y_4038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object* v_f_4048_, lean_object* v_x_4049_, lean_object* v_x_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
if (lean_obj_tag(v_x_4049_) == 0)
{
lean_object* v_es_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4067_; 
v_es_4054_ = lean_ctor_get(v_x_4049_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_x_4049_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4056_ = v_x_4049_;
v_isShared_4057_ = v_isSharedCheck_4067_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_es_4054_);
lean_dec(v_x_4049_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4067_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; uint8_t v___x_4060_; 
v___x_4058_ = lean_unsigned_to_nat(0u);
v___x_4059_ = lean_array_get_size(v_es_4054_);
v___x_4060_ = lean_nat_dec_lt(v___x_4058_, v___x_4059_);
if (v___x_4060_ == 0)
{
lean_object* v___x_4062_; 
lean_dec_ref(v_es_4054_);
lean_dec_ref(v_f_4048_);
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 0, v_x_4050_);
v___x_4062_ = v___x_4056_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_x_4050_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
else
{
size_t v___x_4064_; size_t v___x_4065_; lean_object* v___x_4066_; 
lean_del_object(v___x_4056_);
v___x_4064_ = ((size_t)0ULL);
v___x_4065_ = lean_usize_of_nat(v___x_4059_);
v___x_4066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4048_, v_es_4054_, v___x_4064_, v___x_4065_, v_x_4050_, v___y_4051_, v___y_4052_);
lean_dec_ref(v_es_4054_);
return v___x_4066_;
}
}
}
else
{
lean_object* v_ks_4068_; lean_object* v_vs_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_ks_4068_ = lean_ctor_get(v_x_4049_, 0);
lean_inc_ref(v_ks_4068_);
v_vs_4069_ = lean_ctor_get(v_x_4049_, 1);
lean_inc_ref(v_vs_4069_);
lean_dec_ref_known(v_x_4049_, 2);
v___x_4070_ = lean_unsigned_to_nat(0u);
v___x_4071_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4048_, v_ks_4068_, v_vs_4069_, v___x_4070_, v_x_4050_, v___y_4051_, v___y_4052_);
lean_dec_ref(v_vs_4069_);
lean_dec_ref(v_ks_4068_);
return v___x_4071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_4072_, lean_object* v_x_4073_, lean_object* v_x_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4072_, v_x_4073_, v_x_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_4079_, lean_object* v_as_4080_, lean_object* v_i_4081_, lean_object* v_stop_4082_, lean_object* v_b_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
size_t v_i_boxed_4087_; size_t v_stop_boxed_4088_; lean_object* v_res_4089_; 
v_i_boxed_4087_ = lean_unbox_usize(v_i_4081_);
lean_dec(v_i_4081_);
v_stop_boxed_4088_ = lean_unbox_usize(v_stop_4082_);
lean_dec(v_stop_4082_);
v_res_4089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4079_, v_as_4080_, v_i_boxed_4087_, v_stop_boxed_4088_, v_b_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec_ref(v_as_4080_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object* v_f_4090_, lean_object* v_x_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v___x_4097_; 
lean_inc(v___y_4095_);
lean_inc_ref(v___y_4094_);
v___x_4097_ = lean_apply_5(v_f_4090_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, lean_box(0));
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object* v_f_4098_, lean_object* v_x_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4098_, v_x_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object* v_map_4106_, lean_object* v_f_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___f_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___f_4111_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4111_, 0, v_f_4107_);
v___x_4112_ = lean_box(0);
v___x_4113_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v___f_4111_, v_map_4106_, v___x_4112_, v___y_4108_, v___y_4109_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object* v_map_4114_, lean_object* v_f_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4114_, v_f_4115_, v___y_4116_, v___y_4117_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
return v_res_4119_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4121_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0));
v___x_4122_ = l_Lean_stringToMessageData(v___x_4121_);
return v___x_4122_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4123_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_4124_ = l_Lean_stringToMessageData(v___x_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t v_attrKind_4125_, lean_object* v_declName_4126_, lean_object* v_as_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
if (lean_obj_tag(v_as_4127_) == 0)
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
lean_dec(v_declName_4126_);
v___x_4131_ = lean_box(0);
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
return v___x_4132_;
}
else
{
lean_object* v_head_4133_; lean_object* v_tail_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4164_; 
v_head_4133_ = lean_ctor_get(v_as_4127_, 0);
v_tail_4134_ = lean_ctor_get(v_as_4127_, 1);
v_isSharedCheck_4164_ = !lean_is_exclusive(v_as_4127_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4136_ = v_as_4127_;
v_isShared_4137_ = v_isSharedCheck_4164_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_tail_4134_);
lean_inc(v_head_4133_);
lean_dec(v_as_4127_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4164_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___y_4139_; lean_object* v___x_4141_; 
v___x_4141_ = l_Lean_Parser_addToken(v_head_4133_, v_attrKind_4125_, v___y_4128_, v___y_4129_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_del_object(v___x_4136_);
v___y_4139_ = v___x_4141_;
goto v___jp_4138_;
}
else
{
lean_object* v_a_4142_; uint8_t v___y_4144_; uint8_t v___x_4162_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
v___x_4162_ = l_Lean_Exception_isInterrupt(v_a_4142_);
if (v___x_4162_ == 0)
{
uint8_t v___x_4163_; 
lean_inc(v_a_4142_);
v___x_4163_ = l_Lean_Exception_isRuntime(v_a_4142_);
v___y_4144_ = v___x_4163_;
goto v___jp_4143_;
}
else
{
v___y_4144_ = v___x_4162_;
goto v___jp_4143_;
}
v___jp_4143_:
{
if (v___y_4144_ == 0)
{
if (lean_obj_tag(v_a_4142_) == 0)
{
lean_object* v_msg_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4160_; 
lean_dec_ref_known(v___x_4141_, 1);
v_msg_4145_ = lean_ctor_get(v_a_4142_, 1);
v_isSharedCheck_4160_ = !lean_is_exclusive(v_a_4142_);
if (v_isSharedCheck_4160_ == 0)
{
lean_object* v_unused_4161_; 
v_unused_4161_ = lean_ctor_get(v_a_4142_, 0);
lean_dec(v_unused_4161_);
v___x_4147_ = v_a_4142_;
v_isShared_4148_ = v_isSharedCheck_4160_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_msg_4145_);
lean_dec(v_a_4142_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4160_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4152_; 
v___x_4149_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1);
lean_inc(v_declName_4126_);
v___x_4150_ = l_Lean_MessageData_ofConstName(v_declName_4126_, v___y_4144_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set_tag(v___x_4147_, 7);
lean_ctor_set(v___x_4147_, 1, v___x_4150_);
lean_ctor_set(v___x_4147_, 0, v___x_4149_);
v___x_4152_ = v___x_4147_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4149_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v___x_4150_);
v___x_4152_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
lean_object* v___x_4153_; lean_object* v___x_4155_; 
v___x_4153_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2);
if (v_isShared_4137_ == 0)
{
lean_ctor_set_tag(v___x_4136_, 7);
lean_ctor_set(v___x_4136_, 1, v___x_4153_);
lean_ctor_set(v___x_4136_, 0, v___x_4152_);
v___x_4155_ = v___x_4136_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4152_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v___x_4153_);
v___x_4155_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
lean_ctor_set(v___x_4156_, 1, v_msg_4145_);
v___x_4157_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4156_, v___y_4128_, v___y_4129_);
v___y_4139_ = v___x_4157_;
goto v___jp_4138_;
}
}
}
}
else
{
lean_dec(v_a_4142_);
lean_del_object(v___x_4136_);
v___y_4139_ = v___x_4141_;
goto v___jp_4138_;
}
}
else
{
lean_dec(v_a_4142_);
lean_del_object(v___x_4136_);
v___y_4139_ = v___x_4141_;
goto v___jp_4138_;
}
}
}
v___jp_4138_:
{
if (lean_obj_tag(v___y_4139_) == 0)
{
lean_dec_ref_known(v___y_4139_, 1);
v_as_4127_ = v_tail_4134_;
goto _start;
}
else
{
lean_dec(v_tail_4134_);
lean_dec(v_declName_4126_);
return v___y_4139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object* v_attrKind_4165_, lean_object* v_declName_4166_, lean_object* v_as_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
uint8_t v_attrKind_boxed_4171_; lean_object* v_res_4172_; 
v_attrKind_boxed_4171_ = lean_unbox(v_attrKind_4165_);
v_res_4172_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_boxed_4171_, v_declName_4166_, v_as_4167_, v___y_4168_, v___y_4169_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object* v_catName_4174_, lean_object* v_declName_4175_, lean_object* v_stx_4176_, uint8_t v_attrKind_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_){
_start:
{
lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___f_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___f_4186_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0));
v___x_4187_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4188_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4176_, v_a_4178_, v_a_4179_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; lean_object* v___x_4190_; lean_object* v_env_4191_; lean_object* v___x_4192_; lean_object* v_ext_4193_; lean_object* v_toEnvExtension_4194_; lean_object* v_asyncMode_4195_; lean_object* v___x_4196_; lean_object* v_categories_4197_; lean_object* v___x_4198_; lean_object* v_env_4199_; lean_object* v_ref_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v___x_4188_, 1);
v___x_4190_ = lean_st_ref_get(v_a_4179_);
v_env_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc_ref(v_env_4191_);
lean_dec(v___x_4190_);
v___x_4192_ = l_Lean_Parser_parserExtension;
v_ext_4193_ = lean_ctor_get(v___x_4192_, 1);
v_toEnvExtension_4194_ = lean_ctor_get(v_ext_4193_, 0);
v_asyncMode_4195_ = lean_ctor_get(v_toEnvExtension_4194_, 2);
v___x_4196_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4187_, v___x_4192_, v_env_4191_, v_asyncMode_4195_);
v_categories_4197_ = lean_ctor_get(v___x_4196_, 2);
lean_inc_ref_n(v_categories_4197_, 2);
lean_dec(v___x_4196_);
v___x_4198_ = lean_st_ref_get(v_a_4179_);
v_env_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc_ref(v_env_4199_);
lean_dec(v___x_4198_);
v_ref_4200_ = lean_ctor_get(v_a_4178_, 2);
v___x_4201_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4178_);
v___x_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4202_, 0, v_env_4199_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
lean_inc(v_declName_4175_);
v___x_4203_ = l_Lean_Parser_mkParserOfConstant(v_categories_4197_, v_declName_4175_, v___x_4202_);
lean_dec_ref_known(v___x_4202_, 2);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v_snd_4205_; lean_object* v_info_4206_; lean_object* v_fst_4207_; lean_object* v_collectTokens_4208_; lean_object* v_collectKinds_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4203_, 1);
v_snd_4205_ = lean_ctor_get(v_a_4204_, 1);
lean_inc(v_snd_4205_);
v_info_4206_ = lean_ctor_get(v_snd_4205_, 0);
v_fst_4207_ = lean_ctor_get(v_a_4204_, 0);
lean_inc(v_fst_4207_);
lean_dec(v_a_4204_);
v_collectTokens_4208_ = lean_ctor_get(v_info_4206_, 0);
v_collectKinds_4209_ = lean_ctor_get(v_info_4206_, 1);
v___x_4210_ = lean_box(0);
lean_inc_ref(v_collectTokens_4208_);
v___x_4211_ = lean_apply_1(v_collectTokens_4208_, v___x_4210_);
lean_inc(v_declName_4175_);
v___x_4212_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4177_, v_declName_4175_, v___x_4211_, v_a_4178_, v_a_4179_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
lean_dec_ref_known(v___x_4212_, 1);
v___x_4213_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
lean_inc_ref(v_collectKinds_4209_);
v___x_4214_ = lean_apply_1(v_collectKinds_4209_, v___x_4213_);
v___x_4215_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v___x_4214_, v___f_4186_, v_a_4178_, v_a_4179_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v___x_4216_; uint8_t v___x_4217_; uint8_t v___x_4218_; lean_object* v___x_4219_; 
lean_dec_ref_known(v___x_4215_, 1);
lean_inc(v_a_4189_);
lean_inc(v_snd_4205_);
lean_inc_n(v_declName_4175_, 2);
lean_inc_n(v_catName_4174_, 2);
v___x_4216_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_4216_, 0, v_catName_4174_);
lean_ctor_set(v___x_4216_, 1, v_declName_4175_);
lean_ctor_set(v___x_4216_, 2, v_snd_4205_);
lean_ctor_set(v___x_4216_, 3, v_a_4189_);
v___x_4217_ = lean_unbox(v_fst_4207_);
lean_ctor_set_uint8(v___x_4216_, sizeof(void*)*4, v___x_4217_);
v___x_4218_ = lean_unbox(v_fst_4207_);
lean_dec(v_fst_4207_);
v___x_4219_ = l_Lean_Parser_addParser(v_categories_4197_, v_catName_4174_, v_declName_4175_, v___x_4218_, v_snd_4205_, v_a_4189_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4229_; 
lean_dec_ref_known(v___x_4216_, 4);
lean_dec(v_declName_4175_);
lean_dec(v_catName_4174_);
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4222_ = v___x_4219_;
v_isShared_4223_ = v_isSharedCheck_4229_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4219_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4229_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
lean_ctor_set_tag(v___x_4222_, 3);
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4220_);
v___x_4225_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = l_Lean_MessageData_ofFormat(v___x_4225_);
v___x_4227_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4226_, v_a_4178_, v_a_4179_);
return v___x_4227_;
}
}
}
else
{
lean_object* v___x_4230_; 
lean_dec_ref_known(v___x_4219_, 1);
v___x_4230_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_4192_, v___x_4216_, v_attrKind_4177_, v_a_4178_, v_a_4179_);
lean_dec_ref(v___x_4230_);
v___y_4182_ = v_a_4178_;
v___y_4183_ = v_a_4179_;
goto v___jp_4181_;
}
}
else
{
lean_dec(v_fst_4207_);
lean_dec(v_snd_4205_);
lean_dec_ref(v_categories_4197_);
lean_dec(v_a_4189_);
lean_dec(v_declName_4175_);
lean_dec(v_catName_4174_);
return v___x_4215_;
}
}
else
{
lean_dec(v_fst_4207_);
lean_dec(v_snd_4205_);
lean_dec_ref(v_categories_4197_);
lean_dec(v_a_4189_);
lean_dec(v_declName_4175_);
lean_dec(v_catName_4174_);
return v___x_4212_;
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4242_; 
lean_dec_ref(v_categories_4197_);
lean_dec(v_a_4189_);
lean_dec(v_declName_4175_);
lean_dec(v_catName_4174_);
v_a_4231_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4233_ = v___x_4203_;
v_isShared_4234_ = v_isSharedCheck_4242_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4203_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4242_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4240_; 
v___x_4235_ = lean_io_error_to_string(v_a_4231_);
v___x_4236_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4235_);
v___x_4237_ = l_Lean_MessageData_ofFormat(v___x_4236_);
lean_inc(v_ref_4200_);
v___x_4238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4238_, 0, v_ref_4200_);
lean_ctor_set(v___x_4238_, 1, v___x_4237_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v___x_4238_);
v___x_4240_ = v___x_4233_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4238_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec(v_declName_4175_);
lean_dec(v_catName_4174_);
v_a_4243_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4188_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4188_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
v___jp_4181_:
{
uint8_t v___x_4184_; lean_object* v___x_4185_; 
v___x_4184_ = 0;
v___x_4185_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4174_, v_declName_4175_, v___x_4184_, v___y_4182_, v___y_4183_);
return v___x_4185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object* v_catName_4251_, lean_object* v_declName_4252_, lean_object* v_stx_4253_, lean_object* v_attrKind_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_){
_start:
{
uint8_t v_attrKind_boxed_4258_; lean_object* v_res_4259_; 
v_attrKind_boxed_4258_ = lean_unbox(v_attrKind_4254_);
v_res_4259_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4251_, v_declName_4252_, v_stx_4253_, v_attrKind_boxed_4258_, v_a_4255_, v_a_4256_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* v___attrName_4260_, lean_object* v_catName_4261_, lean_object* v_declName_4262_, lean_object* v_stx_4263_, uint8_t v_attrKind_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4261_, v_declName_4262_, v_stx_4263_, v_attrKind_4264_, v_a_4265_, v_a_4266_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* v___attrName_4269_, lean_object* v_catName_4270_, lean_object* v_declName_4271_, lean_object* v_stx_4272_, lean_object* v_attrKind_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_){
_start:
{
uint8_t v_attrKind_boxed_4277_; lean_object* v_res_4278_; 
v_attrKind_boxed_4277_ = lean_unbox(v_attrKind_4273_);
v_res_4278_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4269_, v_catName_4270_, v_declName_4271_, v_stx_4272_, v_attrKind_boxed_4277_, v_a_4274_, v_a_4275_);
lean_dec(v_a_4275_);
lean_dec_ref(v_a_4274_);
lean_dec(v___attrName_4269_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object* v_00_u03b2_4279_, lean_object* v_map_4280_, lean_object* v_f_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
lean_object* v___x_4285_; 
v___x_4285_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4280_, v_f_4281_, v___y_4282_, v___y_4283_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b2_4286_, lean_object* v_map_4287_, lean_object* v_f_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(v_00_u03b2_4286_, v_map_4287_, v_f_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object* v_map_4293_, lean_object* v_f_4294_, lean_object* v_init_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4294_, v_map_4293_, v_init_4295_, v___y_4296_, v___y_4297_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object* v_map_4300_, lean_object* v_f_4301_, lean_object* v_init_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4300_, v_f_4301_, v_init_4302_, v___y_4303_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object* v_00_u03c3_4307_, lean_object* v_00_u03b2_4308_, lean_object* v_map_4309_, lean_object* v_f_4310_, lean_object* v_init_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4310_, v_map_4309_, v_init_4311_, v___y_4312_, v___y_4313_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object* v_00_u03c3_4316_, lean_object* v_00_u03b2_4317_, lean_object* v_map_4318_, lean_object* v_f_4319_, lean_object* v_init_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(v_00_u03c3_4316_, v_00_u03b2_4317_, v_map_4318_, v_f_4319_, v_init_4320_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_4325_, lean_object* v_00_u03b1_4326_, lean_object* v_00_u03b2_4327_, lean_object* v_f_4328_, lean_object* v_x_4329_, lean_object* v_x_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4328_, v_x_4329_, v_x_4330_, v___y_4331_, v___y_4332_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03c3_4335_, lean_object* v_00_u03b1_4336_, lean_object* v_00_u03b2_4337_, lean_object* v_f_4338_, lean_object* v_x_4339_, lean_object* v_x_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(v_00_u03c3_4335_, v_00_u03b1_4336_, v_00_u03b2_4337_, v_f_4338_, v_x_4339_, v_x_4340_, v___y_4341_, v___y_4342_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4345_, lean_object* v_00_u03b2_4346_, lean_object* v_00_u03c3_4347_, lean_object* v_f_4348_, lean_object* v_as_4349_, size_t v_i_4350_, size_t v_stop_4351_, lean_object* v_b_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4348_, v_as_4349_, v_i_4350_, v_stop_4351_, v_b_4352_, v___y_4353_, v___y_4354_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4357_, lean_object* v_00_u03b2_4358_, lean_object* v_00_u03c3_4359_, lean_object* v_f_4360_, lean_object* v_as_4361_, lean_object* v_i_4362_, lean_object* v_stop_4363_, lean_object* v_b_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
size_t v_i_boxed_4368_; size_t v_stop_boxed_4369_; lean_object* v_res_4370_; 
v_i_boxed_4368_ = lean_unbox_usize(v_i_4362_);
lean_dec(v_i_4362_);
v_stop_boxed_4369_ = lean_unbox_usize(v_stop_4363_);
lean_dec(v_stop_4363_);
v_res_4370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4357_, v_00_u03b2_4358_, v_00_u03c3_4359_, v_f_4360_, v_as_4361_, v_i_boxed_4368_, v_stop_boxed_4369_, v_b_4364_, v___y_4365_, v___y_4366_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec_ref(v_as_4361_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_4371_, lean_object* v_00_u03b1_4372_, lean_object* v_00_u03b2_4373_, lean_object* v_f_4374_, lean_object* v_keys_4375_, lean_object* v_vals_4376_, lean_object* v_heq_4377_, lean_object* v_i_4378_, lean_object* v_acc_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4383_; 
v___x_4383_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4374_, v_keys_4375_, v_vals_4376_, v_i_4378_, v_acc_4379_, v___y_4380_, v___y_4381_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_4384_, lean_object* v_00_u03b1_4385_, lean_object* v_00_u03b2_4386_, lean_object* v_f_4387_, lean_object* v_keys_4388_, lean_object* v_vals_4389_, lean_object* v_heq_4390_, lean_object* v_i_4391_, lean_object* v_acc_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4384_, v_00_u03b1_4385_, v_00_u03b2_4386_, v_f_4387_, v_keys_4388_, v_vals_4389_, v_heq_4390_, v_i_4391_, v_acc_4392_, v___y_4393_, v___y_4394_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec_ref(v_vals_4389_);
lean_dec_ref(v_keys_4388_);
return v_res_4396_;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___auto__1(void){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object* v_catName_4398_, lean_object* v_declName_4399_, lean_object* v_stx_4400_, uint8_t v_attrKind_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4398_, v_declName_4399_, v_stx_4400_, v_attrKind_4401_, v___y_4402_, v___y_4403_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object* v_catName_4406_, lean_object* v_declName_4407_, lean_object* v_stx_4408_, lean_object* v_attrKind_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
uint8_t v_attrKind_boxed_4413_; lean_object* v_res_4414_; 
v_attrKind_boxed_4413_ = lean_unbox(v_attrKind_4409_);
v_res_4414_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4406_, v_declName_4407_, v_stx_4408_, v_attrKind_boxed_4413_, v___y_4410_, v___y_4411_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* v_attrName_4416_, lean_object* v_catName_4417_, lean_object* v_ref_4418_){
_start:
{
lean_object* v___f_4419_; lean_object* v___f_4420_; lean_object* v___x_4421_; uint8_t v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___f_4419_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4419_, 0, v_catName_4417_);
lean_inc(v_attrName_4416_);
v___f_4420_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4420_, 0, v_attrName_4416_);
v___x_4421_ = ((lean_object*)(l_Lean_Parser_mkParserAttributeImpl___closed__0));
v___x_4422_ = 1;
v___x_4423_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4423_, 0, v_ref_4418_);
lean_ctor_set(v___x_4423_, 1, v_attrName_4416_);
lean_ctor_set(v___x_4423_, 2, v___x_4421_);
lean_ctor_set_uint8(v___x_4423_, sizeof(void*)*3, v___x_4422_);
v___x_4424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4423_);
lean_ctor_set(v___x_4424_, 1, v___f_4419_);
lean_ctor_set(v___x_4424_, 2, v___f_4420_);
return v___x_4424_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4425_; 
v___x_4425_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* v_attrName_4426_, lean_object* v_catName_4427_, lean_object* v_ref_4428_){
_start:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4430_ = l_Lean_Parser_mkParserAttributeImpl(v_attrName_4426_, v_catName_4427_, v_ref_4428_);
v___x_4431_ = l_Lean_registerBuiltinAttribute(v___x_4430_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object* v_attrName_4432_, lean_object* v_catName_4433_, lean_object* v_ref_4434_, lean_object* v_a_4435_){
_start:
{
lean_object* v_res_4436_; 
v_res_4436_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4432_, v_catName_4433_, v_ref_4434_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object* v_ref_4440_, lean_object* v_args_4441_){
_start:
{
if (lean_obj_tag(v_args_4441_) == 1)
{
lean_object* v_head_4444_; 
v_head_4444_ = lean_ctor_get(v_args_4441_, 0);
lean_inc(v_head_4444_);
if (lean_obj_tag(v_head_4444_) == 2)
{
lean_object* v_tail_4445_; 
v_tail_4445_ = lean_ctor_get(v_args_4441_, 1);
lean_inc(v_tail_4445_);
lean_dec_ref_known(v_args_4441_, 2);
if (lean_obj_tag(v_tail_4445_) == 1)
{
lean_object* v_head_4446_; 
v_head_4446_ = lean_ctor_get(v_tail_4445_, 0);
lean_inc(v_head_4446_);
if (lean_obj_tag(v_head_4446_) == 2)
{
lean_object* v_tail_4447_; 
v_tail_4447_ = lean_ctor_get(v_tail_4445_, 1);
lean_inc(v_tail_4447_);
lean_dec_ref_known(v_tail_4445_, 2);
if (lean_obj_tag(v_tail_4447_) == 0)
{
lean_object* v_v_4448_; lean_object* v_v_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4457_; 
v_v_4448_ = lean_ctor_get(v_head_4444_, 0);
lean_inc(v_v_4448_);
lean_dec_ref_known(v_head_4444_, 1);
v_v_4449_ = lean_ctor_get(v_head_4446_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v_head_4446_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4451_ = v_head_4446_;
v_isShared_4452_ = v_isSharedCheck_4457_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_v_4449_);
lean_dec(v_head_4446_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4457_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4453_; lean_object* v___x_4455_; 
v___x_4453_ = l_Lean_Parser_mkParserAttributeImpl(v_v_4448_, v_v_4449_, v_ref_4440_);
if (v_isShared_4452_ == 0)
{
lean_ctor_set_tag(v___x_4451_, 1);
lean_ctor_set(v___x_4451_, 0, v___x_4453_);
v___x_4455_ = v___x_4451_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v___x_4453_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
else
{
lean_dec(v_tail_4447_);
lean_dec_ref_known(v_head_4446_, 1);
lean_dec_ref_known(v_head_4444_, 1);
lean_dec(v_ref_4440_);
goto v___jp_4442_;
}
}
else
{
lean_dec(v_head_4446_);
lean_dec_ref_known(v_tail_4445_, 2);
lean_dec_ref_known(v_head_4444_, 1);
lean_dec(v_ref_4440_);
goto v___jp_4442_;
}
}
else
{
lean_dec_ref_known(v_head_4444_, 1);
lean_dec(v_tail_4445_);
lean_dec(v_ref_4440_);
goto v___jp_4442_;
}
}
else
{
lean_dec_ref_known(v_args_4441_, 2);
lean_dec(v_head_4444_);
lean_dec(v_ref_4440_);
goto v___jp_4442_;
}
}
else
{
lean_dec(v_args_4441_);
lean_dec(v_ref_4440_);
goto v___jp_4442_;
}
v___jp_4442_:
{
lean_object* v___x_4443_; 
v___x_4443_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
return v___x_4443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___f_4463_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4464_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4465_ = l_Lean_registerAttributeImplBuilder(v___x_4464_, v___f_4463_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object* v_a_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
return v_res_4467_;
}
}
static lean_object* _init_l_Lean_Parser_registerParserCategory___auto__1(void){
_start:
{
lean_object* v___x_4468_; 
v___x_4468_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object* v_env_4469_, lean_object* v_attrName_4470_, lean_object* v_catName_4471_, uint8_t v_behavior_4472_, lean_object* v_ref_4473_){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
lean_inc(v_ref_4473_);
lean_inc(v_catName_4471_);
v___x_4475_ = l_Lean_Parser_addParserCategory(v_env_4469_, v_catName_4471_, v_ref_4473_, v_behavior_4472_);
v___x_4476_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_4475_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4490_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4479_ = v___x_4476_;
v_isShared_4480_ = v_isSharedCheck_4490_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4476_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4490_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4481_; lean_object* v___x_4483_; 
v___x_4481_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
if (v_isShared_4480_ == 0)
{
lean_ctor_set_tag(v___x_4479_, 2);
lean_ctor_set(v___x_4479_, 0, v_attrName_4470_);
v___x_4483_ = v___x_4479_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_attrName_4470_);
v___x_4483_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4484_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4484_, 0, v_catName_4471_);
v___x_4485_ = lean_box(0);
v___x_4486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4484_);
lean_ctor_set(v___x_4486_, 1, v___x_4485_);
v___x_4487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4483_);
lean_ctor_set(v___x_4487_, 1, v___x_4486_);
v___x_4488_ = l_Lean_registerAttributeOfBuilder(v_a_4477_, v___x_4481_, v_ref_4473_, v___x_4487_);
return v___x_4488_;
}
}
}
else
{
lean_dec(v_ref_4473_);
lean_dec(v_catName_4471_);
lean_dec(v_attrName_4470_);
return v___x_4476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* v_env_4491_, lean_object* v_attrName_4492_, lean_object* v_catName_4493_, lean_object* v_behavior_4494_, lean_object* v_ref_4495_, lean_object* v_a_4496_){
_start:
{
uint8_t v_behavior_boxed_4497_; lean_object* v_res_4498_; 
v_behavior_boxed_4497_ = lean_unbox(v_behavior_4494_);
v_res_4498_ = l_Lean_Parser_registerParserCategory(v_env_4491_, v_attrName_4492_, v_catName_4493_, v_behavior_boxed_4497_, v_ref_4495_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; uint8_t v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4521_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4522_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4523_ = 0;
v___x_4524_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4525_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4521_, v___x_4522_, v___x_4523_, v___x_4524_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object* v_a_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
return v_res_4527_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4533_ = lean_unsigned_to_nat(3431364690u);
v___x_4534_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4535_ = l_Lean_Name_num___override(v___x_4534_, v___x_4533_);
return v___x_4535_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4536_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4537_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4538_ = l_Lean_Name_str___override(v___x_4537_, v___x_4536_);
return v___x_4538_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4539_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4540_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4541_ = l_Lean_Name_str___override(v___x_4540_, v___x_4539_);
return v___x_4541_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4542_ = lean_unsigned_to_nat(2u);
v___x_4543_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4544_ = l_Lean_Name_num___override(v___x_4543_, v___x_4542_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4546_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4547_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4548_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4549_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4546_, v___x_4547_, v___x_4548_);
return v___x_4549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object* v_a_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
return v_res_4551_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4561_ = lean_unsigned_to_nat(2342493449u);
v___x_4562_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4563_ = l_Lean_Name_num___override(v___x_4562_, v___x_4561_);
return v___x_4563_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4564_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4565_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4566_ = l_Lean_Name_str___override(v___x_4565_, v___x_4564_);
return v___x_4566_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4567_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4568_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4569_ = l_Lean_Name_str___override(v___x_4568_, v___x_4567_);
return v___x_4569_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4570_ = lean_unsigned_to_nat(2u);
v___x_4571_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4572_ = l_Lean_Name_num___override(v___x_4571_, v___x_4570_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; uint8_t v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4574_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4575_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4576_ = 0;
v___x_4577_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4578_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4574_, v___x_4575_, v___x_4576_, v___x_4577_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object* v_a_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
return v_res_4580_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4586_ = lean_unsigned_to_nat(3226070615u);
v___x_4587_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4588_ = l_Lean_Name_num___override(v___x_4587_, v___x_4586_);
return v___x_4588_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4589_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4590_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4591_ = l_Lean_Name_str___override(v___x_4590_, v___x_4589_);
return v___x_4591_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4592_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4593_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4594_ = l_Lean_Name_str___override(v___x_4593_, v___x_4592_);
return v___x_4594_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4595_ = lean_unsigned_to_nat(2u);
v___x_4596_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4597_ = l_Lean_Name_num___override(v___x_4596_, v___x_4595_);
return v___x_4597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4599_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4600_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4601_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4602_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4599_, v___x_4600_, v___x_4601_);
return v___x_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object* v_a_4603_){
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* v_rbp_4605_){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4606_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4607_ = l_Lean_Parser_categoryParser(v___x_4606_, v_rbp_4605_);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t v_addOpenSimple_4608_, lean_object* v_x_4609_, lean_object* v_x_4610_){
_start:
{
if (lean_obj_tag(v_x_4610_) == 0)
{
return v_x_4609_;
}
else
{
lean_object* v_head_4611_; lean_object* v_tail_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4635_; 
v_head_4611_ = lean_ctor_get(v_x_4610_, 0);
v_tail_4612_ = lean_ctor_get(v_x_4610_, 1);
v_isSharedCheck_4635_ = !lean_is_exclusive(v_x_4610_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4614_ = v_x_4610_;
v_isShared_4615_ = v_isSharedCheck_4635_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_tail_4612_);
lean_inc(v_head_4611_);
lean_dec(v_x_4610_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4635_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v_fst_4616_; lean_object* v_snd_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4634_; 
v_fst_4616_ = lean_ctor_get(v_x_4609_, 0);
v_snd_4617_ = lean_ctor_get(v_x_4609_, 1);
v_isSharedCheck_4634_ = !lean_is_exclusive(v_x_4609_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4619_ = v_x_4609_;
v_isShared_4620_ = v_isSharedCheck_4634_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_snd_4617_);
lean_inc(v_fst_4616_);
lean_dec(v_x_4609_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4634_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___y_4622_; 
if (v_addOpenSimple_4608_ == 0)
{
lean_del_object(v___x_4614_);
v___y_4622_ = v_snd_4617_;
goto v___jp_4621_;
}
else
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4632_; 
v___x_4629_ = lean_box(0);
lean_inc(v_head_4611_);
v___x_4630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4630_, 0, v_head_4611_);
lean_ctor_set(v___x_4630_, 1, v___x_4629_);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 1, v_snd_4617_);
lean_ctor_set(v___x_4614_, 0, v___x_4630_);
v___x_4632_ = v___x_4614_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4630_);
lean_ctor_set(v_reuseFailAlloc_4633_, 1, v_snd_4617_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
v___y_4622_ = v___x_4632_;
goto v___jp_4621_;
}
}
v___jp_4621_:
{
lean_object* v___x_4623_; lean_object* v_env_4624_; lean_object* v___x_4626_; 
v___x_4623_ = l_Lean_Parser_parserExtension;
v_env_4624_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v___x_4623_, v_fst_4616_, v_head_4611_);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 1, v___y_4622_);
lean_ctor_set(v___x_4619_, 0, v_env_4624_);
v___x_4626_ = v___x_4619_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_env_4624_);
lean_ctor_set(v_reuseFailAlloc_4628_, 1, v___y_4622_);
v___x_4626_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
v_x_4609_ = v___x_4626_;
v_x_4610_ = v_tail_4612_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object* v_addOpenSimple_4636_, lean_object* v_x_4637_, lean_object* v_x_4638_){
_start:
{
uint8_t v_addOpenSimple_boxed_4639_; lean_object* v_res_4640_; 
v_addOpenSimple_boxed_4639_ = lean_unbox(v_addOpenSimple_4636_);
v_res_4640_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_boxed_4639_, v_x_4637_, v_x_4638_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t v_addOpenSimple_4641_, lean_object* v_as_4642_, size_t v_i_4643_, size_t v_stop_4644_, lean_object* v_b_4645_){
_start:
{
uint8_t v___x_4646_; 
v___x_4646_ = lean_usize_dec_eq(v_i_4643_, v_stop_4644_);
if (v___x_4646_ == 0)
{
lean_object* v_toParserModuleContext_4647_; lean_object* v_toInputContext_4648_; lean_object* v_toCacheableParserContext_4649_; lean_object* v_tokens_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4677_; 
v_toParserModuleContext_4647_ = lean_ctor_get(v_b_4645_, 1);
v_toInputContext_4648_ = lean_ctor_get(v_b_4645_, 0);
v_toCacheableParserContext_4649_ = lean_ctor_get(v_b_4645_, 2);
v_tokens_4650_ = lean_ctor_get(v_b_4645_, 3);
v_isSharedCheck_4677_ = !lean_is_exclusive(v_b_4645_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4652_ = v_b_4645_;
v_isShared_4653_ = v_isSharedCheck_4677_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_tokens_4650_);
lean_inc(v_toCacheableParserContext_4649_);
lean_inc(v_toParserModuleContext_4647_);
lean_inc(v_toInputContext_4648_);
lean_dec(v_b_4645_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4677_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v_env_4654_; lean_object* v_options_4655_; lean_object* v_currNamespace_4656_; lean_object* v_openDecls_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4676_; 
v_env_4654_ = lean_ctor_get(v_toParserModuleContext_4647_, 0);
v_options_4655_ = lean_ctor_get(v_toParserModuleContext_4647_, 1);
v_currNamespace_4656_ = lean_ctor_get(v_toParserModuleContext_4647_, 2);
v_openDecls_4657_ = lean_ctor_get(v_toParserModuleContext_4647_, 3);
v_isSharedCheck_4676_ = !lean_is_exclusive(v_toParserModuleContext_4647_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4659_ = v_toParserModuleContext_4647_;
v_isShared_4660_ = v_isSharedCheck_4676_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_openDecls_4657_);
lean_inc(v_currNamespace_4656_);
lean_inc(v_options_4655_);
lean_inc(v_env_4654_);
lean_dec(v_toParserModuleContext_4647_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4676_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v___x_4661_; lean_object* v_nss_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v_fst_4665_; lean_object* v_snd_4666_; lean_object* v___x_4668_; 
v___x_4661_ = lean_array_uget_borrowed(v_as_4642_, v_i_4643_);
lean_inc(v___x_4661_);
lean_inc(v_openDecls_4657_);
lean_inc(v_currNamespace_4656_);
lean_inc_ref(v_env_4654_);
v_nss_4662_ = l_Lean_ResolveName_resolveNamespace(v_env_4654_, v_currNamespace_4656_, v_openDecls_4657_, v___x_4661_);
v___x_4663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4663_, 0, v_env_4654_);
lean_ctor_set(v___x_4663_, 1, v_openDecls_4657_);
v___x_4664_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4641_, v___x_4663_, v_nss_4662_);
v_fst_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_fst_4665_);
v_snd_4666_ = lean_ctor_get(v___x_4664_, 1);
lean_inc(v_snd_4666_);
lean_dec_ref(v___x_4664_);
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 3, v_snd_4666_);
lean_ctor_set(v___x_4659_, 0, v_fst_4665_);
v___x_4668_ = v___x_4659_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_fst_4665_);
lean_ctor_set(v_reuseFailAlloc_4675_, 1, v_options_4655_);
lean_ctor_set(v_reuseFailAlloc_4675_, 2, v_currNamespace_4656_);
lean_ctor_set(v_reuseFailAlloc_4675_, 3, v_snd_4666_);
v___x_4668_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
lean_object* v___x_4670_; 
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 1, v___x_4668_);
v___x_4670_ = v___x_4652_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_toInputContext_4648_);
lean_ctor_set(v_reuseFailAlloc_4674_, 1, v___x_4668_);
lean_ctor_set(v_reuseFailAlloc_4674_, 2, v_toCacheableParserContext_4649_);
lean_ctor_set(v_reuseFailAlloc_4674_, 3, v_tokens_4650_);
v___x_4670_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
size_t v___x_4671_; size_t v___x_4672_; 
v___x_4671_ = ((size_t)1ULL);
v___x_4672_ = lean_usize_add(v_i_4643_, v___x_4671_);
v_i_4643_ = v___x_4672_;
v_b_4645_ = v___x_4670_;
goto _start;
}
}
}
}
}
else
{
return v_b_4645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object* v_addOpenSimple_4678_, lean_object* v_as_4679_, lean_object* v_i_4680_, lean_object* v_stop_4681_, lean_object* v_b_4682_){
_start:
{
uint8_t v_addOpenSimple_boxed_4683_; size_t v_i_boxed_4684_; size_t v_stop_boxed_4685_; lean_object* v_res_4686_; 
v_addOpenSimple_boxed_4683_ = lean_unbox(v_addOpenSimple_4678_);
v_i_boxed_4684_ = lean_unbox_usize(v_i_4680_);
lean_dec(v_i_4680_);
v_stop_boxed_4685_ = lean_unbox_usize(v_stop_4681_);
lean_dec(v_stop_4681_);
v_res_4686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_boxed_4683_, v_as_4679_, v_i_boxed_4684_, v_stop_boxed_4685_, v_b_4682_);
lean_dec_ref(v_as_4679_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object* v___x_4687_, lean_object* v_ids_4688_, uint8_t v_addOpenSimple_4689_, lean_object* v_c_4690_){
_start:
{
lean_object* v___y_4692_; lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
v___x_4711_ = lean_unsigned_to_nat(0u);
v___x_4712_ = lean_array_get_size(v_ids_4688_);
v___x_4713_ = lean_nat_dec_lt(v___x_4711_, v___x_4712_);
if (v___x_4713_ == 0)
{
v___y_4692_ = v_c_4690_;
goto v___jp_4691_;
}
else
{
uint8_t v___x_4714_; 
v___x_4714_ = lean_nat_dec_le(v___x_4712_, v___x_4712_);
if (v___x_4714_ == 0)
{
if (v___x_4713_ == 0)
{
v___y_4692_ = v_c_4690_;
goto v___jp_4691_;
}
else
{
size_t v___x_4715_; size_t v___x_4716_; lean_object* v___x_4717_; 
v___x_4715_ = ((size_t)0ULL);
v___x_4716_ = lean_usize_of_nat(v___x_4712_);
v___x_4717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4689_, v_ids_4688_, v___x_4715_, v___x_4716_, v_c_4690_);
v___y_4692_ = v___x_4717_;
goto v___jp_4691_;
}
}
else
{
size_t v___x_4718_; size_t v___x_4719_; lean_object* v___x_4720_; 
v___x_4718_ = ((size_t)0ULL);
v___x_4719_ = lean_usize_of_nat(v___x_4712_);
v___x_4720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4689_, v_ids_4688_, v___x_4718_, v___x_4719_, v_c_4690_);
v___y_4692_ = v___x_4720_;
goto v___jp_4691_;
}
}
v___jp_4691_:
{
lean_object* v_toParserModuleContext_4693_; lean_object* v_toInputContext_4694_; lean_object* v_toCacheableParserContext_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4709_; 
v_toParserModuleContext_4693_ = lean_ctor_get(v___y_4692_, 1);
v_toInputContext_4694_ = lean_ctor_get(v___y_4692_, 0);
v_toCacheableParserContext_4695_ = lean_ctor_get(v___y_4692_, 2);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___y_4692_);
if (v_isSharedCheck_4709_ == 0)
{
lean_object* v_unused_4710_; 
v_unused_4710_ = lean_ctor_get(v___y_4692_, 3);
lean_dec(v_unused_4710_);
v___x_4697_ = v___y_4692_;
v_isShared_4698_ = v_isSharedCheck_4709_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_toCacheableParserContext_4695_);
lean_inc(v_toParserModuleContext_4693_);
lean_inc(v_toInputContext_4694_);
lean_dec(v___y_4692_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4709_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v_env_4699_; lean_object* v___x_4700_; lean_object* v_ext_4701_; lean_object* v_toEnvExtension_4702_; lean_object* v_asyncMode_4703_; lean_object* v___x_4704_; lean_object* v_tokens_4705_; lean_object* v___x_4707_; 
v_env_4699_ = lean_ctor_get(v_toParserModuleContext_4693_, 0);
v___x_4700_ = l_Lean_Parser_parserExtension;
v_ext_4701_ = lean_ctor_get(v___x_4700_, 1);
v_toEnvExtension_4702_ = lean_ctor_get(v_ext_4701_, 0);
v_asyncMode_4703_ = lean_ctor_get(v_toEnvExtension_4702_, 2);
lean_inc_ref(v_env_4699_);
v___x_4704_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4687_, v___x_4700_, v_env_4699_, v_asyncMode_4703_);
v_tokens_4705_ = lean_ctor_get(v___x_4704_, 0);
lean_inc_ref(v_tokens_4705_);
lean_dec(v___x_4704_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 3, v_tokens_4705_);
v___x_4707_ = v___x_4697_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_toInputContext_4694_);
lean_ctor_set(v_reuseFailAlloc_4708_, 1, v_toParserModuleContext_4693_);
lean_ctor_set(v_reuseFailAlloc_4708_, 2, v_toCacheableParserContext_4695_);
lean_ctor_set(v_reuseFailAlloc_4708_, 3, v_tokens_4705_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object* v___x_4721_, lean_object* v_ids_4722_, lean_object* v_addOpenSimple_4723_, lean_object* v_c_4724_){
_start:
{
uint8_t v_addOpenSimple_boxed_4725_; lean_object* v_res_4726_; 
v_addOpenSimple_boxed_4725_ = lean_unbox(v_addOpenSimple_4723_);
v_res_4726_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_4721_, v_ids_4722_, v_addOpenSimple_boxed_4725_, v_c_4724_);
lean_dec_ref(v_ids_4722_);
lean_dec_ref(v___x_4721_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* v_ids_4727_, uint8_t v_addOpenSimple_4728_, lean_object* v_p_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___f_4734_; lean_object* v___x_4735_; 
v___x_4732_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4733_ = lean_box(v_addOpenSimple_4728_);
v___f_4734_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4734_, 0, v___x_4732_);
lean_closure_set(v___f_4734_, 1, v_ids_4727_);
lean_closure_set(v___f_4734_, 2, v___x_4733_);
v___x_4735_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_4734_, v_p_4729_, v_a_4730_, v_a_4731_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* v_ids_4736_, lean_object* v_addOpenSimple_4737_, lean_object* v_p_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_){
_start:
{
uint8_t v_addOpenSimple_boxed_4741_; lean_object* v_res_4742_; 
v_addOpenSimple_boxed_4741_ = lean_unbox(v_addOpenSimple_4737_);
v_res_4742_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_4736_, v_addOpenSimple_boxed_4741_, v_p_4738_, v_a_4739_, v_a_4740_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t v_sz_4743_, size_t v_i_4744_, lean_object* v_bs_4745_){
_start:
{
uint8_t v___x_4746_; 
v___x_4746_ = lean_usize_dec_lt(v_i_4744_, v_sz_4743_);
if (v___x_4746_ == 0)
{
return v_bs_4745_;
}
else
{
lean_object* v_v_4747_; lean_object* v___x_4748_; lean_object* v_bs_x27_4749_; lean_object* v___x_4750_; size_t v___x_4751_; size_t v___x_4752_; lean_object* v___x_4753_; 
v_v_4747_ = lean_array_uget(v_bs_4745_, v_i_4744_);
v___x_4748_ = lean_unsigned_to_nat(0u);
v_bs_x27_4749_ = lean_array_uset(v_bs_4745_, v_i_4744_, v___x_4748_);
v___x_4750_ = l_Lean_Syntax_getId(v_v_4747_);
lean_dec(v_v_4747_);
v___x_4751_ = ((size_t)1ULL);
v___x_4752_ = lean_usize_add(v_i_4744_, v___x_4751_);
v___x_4753_ = lean_array_uset(v_bs_x27_4749_, v_i_4744_, v___x_4750_);
v_i_4744_ = v___x_4752_;
v_bs_4745_ = v___x_4753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object* v_sz_4755_, lean_object* v_i_4756_, lean_object* v_bs_4757_){
_start:
{
size_t v_sz_boxed_4758_; size_t v_i_boxed_4759_; lean_object* v_res_4760_; 
v_sz_boxed_4758_ = lean_unbox_usize(v_sz_4755_);
lean_dec(v_sz_4755_);
v_i_boxed_4759_ = lean_unbox_usize(v_i_4756_);
lean_dec(v_i_4756_);
v_res_4760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_boxed_4758_, v_i_boxed_4759_, v_bs_4757_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* v_openDeclStx_4774_, lean_object* v_p_4775_, lean_object* v_c_4776_, lean_object* v_s_4777_){
_start:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; uint8_t v___x_4780_; 
lean_inc(v_openDeclStx_4774_);
v___x_4778_ = l_Lean_Syntax_getKind(v_openDeclStx_4774_);
v___x_4779_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__2));
v___x_4780_ = lean_name_eq(v___x_4778_, v___x_4779_);
if (v___x_4780_ == 0)
{
lean_object* v___x_4781_; uint8_t v___x_4782_; 
v___x_4781_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__4));
v___x_4782_ = lean_name_eq(v___x_4778_, v___x_4781_);
lean_dec(v___x_4778_);
if (v___x_4782_ == 0)
{
lean_object* v___x_4783_; 
lean_dec(v_openDeclStx_4774_);
v___x_4783_ = lean_apply_2(v_p_4775_, v_c_4776_, v_s_4777_);
return v___x_4783_;
}
else
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; size_t v_sz_4787_; size_t v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; 
v___x_4784_ = lean_unsigned_to_nat(1u);
v___x_4785_ = l_Lean_Syntax_getArg(v_openDeclStx_4774_, v___x_4784_);
lean_dec(v_openDeclStx_4774_);
v___x_4786_ = l_Lean_Syntax_getArgs(v___x_4785_);
lean_dec(v___x_4785_);
v_sz_4787_ = lean_array_size(v___x_4786_);
v___x_4788_ = ((size_t)0ULL);
v___x_4789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4787_, v___x_4788_, v___x_4786_);
v___x_4790_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4789_, v___x_4780_, v_p_4775_, v_c_4776_, v_s_4777_);
return v___x_4790_;
}
}
else
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; size_t v_sz_4794_; size_t v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
lean_dec(v___x_4778_);
v___x_4791_ = lean_unsigned_to_nat(0u);
v___x_4792_ = l_Lean_Syntax_getArg(v_openDeclStx_4774_, v___x_4791_);
lean_dec(v_openDeclStx_4774_);
v___x_4793_ = l_Lean_Syntax_getArgs(v___x_4792_);
lean_dec(v___x_4792_);
v_sz_4794_ = lean_array_size(v___x_4793_);
v___x_4795_ = ((size_t)0ULL);
v___x_4796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4794_, v___x_4795_, v___x_4793_);
v___x_4797_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4796_, v___x_4780_, v_p_4775_, v_c_4776_, v_s_4777_);
return v___x_4797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* v_p_4804_, lean_object* v_c_4805_, lean_object* v_s_4806_){
_start:
{
lean_object* v_stxStack_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; 
v_stxStack_4807_ = lean_ctor_get(v_s_4806_, 0);
v___x_4808_ = lean_unsigned_to_nat(0u);
v___x_4809_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4807_);
v___x_4810_ = lean_nat_dec_lt(v___x_4808_, v___x_4809_);
lean_dec(v___x_4809_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4811_; 
v___x_4811_ = lean_apply_2(v_p_4804_, v_c_4805_, v_s_4806_);
return v___x_4811_;
}
else
{
lean_object* v_stx_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; uint8_t v___x_4815_; 
v_stx_4812_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4807_);
lean_inc(v_stx_4812_);
v___x_4813_ = l_Lean_Syntax_getKind(v_stx_4812_);
v___x_4814_ = ((lean_object*)(l_Lean_Parser_withOpenFn___closed__1));
v___x_4815_ = lean_name_eq(v___x_4813_, v___x_4814_);
lean_dec(v___x_4813_);
if (v___x_4815_ == 0)
{
lean_object* v___x_4816_; 
lean_dec(v_stx_4812_);
v___x_4816_ = lean_apply_2(v_p_4804_, v_c_4805_, v_s_4806_);
return v___x_4816_;
}
else
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4817_ = lean_unsigned_to_nat(1u);
v___x_4818_ = l_Lean_Syntax_getArg(v_stx_4812_, v___x_4817_);
lean_dec(v_stx_4812_);
v___x_4819_ = l_Lean_Parser_withOpenDeclFnCore(v___x_4818_, v_p_4804_, v_c_4805_, v_s_4806_);
return v___x_4819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* v_p_4820_){
_start:
{
lean_object* v_info_4821_; lean_object* v_fn_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4830_; 
v_info_4821_ = lean_ctor_get(v_p_4820_, 0);
v_fn_4822_ = lean_ctor_get(v_p_4820_, 1);
v_isSharedCheck_4830_ = !lean_is_exclusive(v_p_4820_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4824_ = v_p_4820_;
v_isShared_4825_ = v_isSharedCheck_4830_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_fn_4822_);
lean_inc(v_info_4821_);
lean_dec(v_p_4820_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4830_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4826_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(v___x_4826_, 0, v_fn_4822_);
if (v_isShared_4825_ == 0)
{
lean_ctor_set(v___x_4824_, 1, v___x_4826_);
v___x_4828_ = v___x_4824_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_info_4821_);
lean_ctor_set(v_reuseFailAlloc_4829_, 1, v___x_4826_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* v_p_4831_, lean_object* v_c_4832_, lean_object* v_s_4833_){
_start:
{
lean_object* v_stxStack_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; uint8_t v___x_4837_; 
v_stxStack_4834_ = lean_ctor_get(v_s_4833_, 0);
v___x_4835_ = lean_unsigned_to_nat(0u);
v___x_4836_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4834_);
v___x_4837_ = lean_nat_dec_lt(v___x_4835_, v___x_4836_);
lean_dec(v___x_4836_);
if (v___x_4837_ == 0)
{
lean_object* v___x_4838_; 
v___x_4838_ = lean_apply_2(v_p_4831_, v_c_4832_, v_s_4833_);
return v___x_4838_;
}
else
{
lean_object* v_stx_4839_; lean_object* v___x_4840_; 
v_stx_4839_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4834_);
v___x_4840_ = l_Lean_Parser_withOpenDeclFnCore(v_stx_4839_, v_p_4831_, v_c_4832_, v_s_4833_);
return v___x_4840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* v_p_4841_){
_start:
{
lean_object* v_info_4842_; lean_object* v_fn_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4851_; 
v_info_4842_ = lean_ctor_get(v_p_4841_, 0);
v_fn_4843_ = lean_ctor_get(v_p_4841_, 1);
v_isSharedCheck_4851_ = !lean_is_exclusive(v_p_4841_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4845_ = v_p_4841_;
v_isShared_4846_ = v_isSharedCheck_4851_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_fn_4843_);
lean_inc(v_info_4842_);
lean_dec(v_p_4841_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4851_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4847_; lean_object* v___x_4849_; 
v___x_4847_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(v___x_4847_, 0, v_fn_4843_);
if (v_isShared_4846_ == 0)
{
lean_ctor_set(v___x_4845_, 1, v___x_4847_);
v___x_4849_ = v___x_4845_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_info_4842_);
lean_ctor_set(v_reuseFailAlloc_4850_, 1, v___x_4847_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object* v_val_4858_){
_start:
{
lean_object* v___x_4866_; 
v___x_4866_ = l_Lean_Syntax_isStrLit_x3f(v_val_4858_);
if (lean_obj_tag(v___x_4866_) == 1)
{
lean_object* v_val_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4875_; 
v_val_4867_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4869_ = v___x_4866_;
v_isShared_4870_ = v_isSharedCheck_4875_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_val_4867_);
lean_dec(v___x_4866_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4875_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4871_; lean_object* v___x_4873_; 
v___x_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4871_, 0, v_val_4867_);
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 0, v___x_4871_);
v___x_4873_ = v___x_4869_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4871_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
else
{
lean_object* v___x_4876_; 
lean_dec(v___x_4866_);
v___x_4876_ = l_Lean_Syntax_isNatLit_x3f(v_val_4858_);
if (lean_obj_tag(v___x_4876_) == 1)
{
lean_object* v_val_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4885_; 
v_val_4877_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4879_ = v___x_4876_;
v_isShared_4880_ = v_isSharedCheck_4885_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_val_4877_);
lean_dec(v___x_4876_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4885_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4881_; lean_object* v___x_4883_; 
v___x_4881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4881_, 0, v_val_4877_);
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 0, v___x_4881_);
v___x_4883_ = v___x_4879_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4881_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
else
{
lean_dec(v___x_4876_);
if (lean_obj_tag(v_val_4858_) == 2)
{
lean_object* v_val_4886_; lean_object* v___x_4887_; uint8_t v___x_4888_; 
v_val_4886_ = lean_ctor_get(v_val_4858_, 1);
v___x_4887_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3));
v___x_4888_ = lean_string_dec_eq(v_val_4886_, v___x_4887_);
if (v___x_4888_ == 0)
{
goto v___jp_4859_;
}
else
{
lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4889_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4889_, 0, v___x_4888_);
v___x_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
return v___x_4890_;
}
}
else
{
goto v___jp_4859_;
}
}
}
v___jp_4859_:
{
if (lean_obj_tag(v_val_4858_) == 2)
{
lean_object* v_val_4860_; lean_object* v___x_4861_; uint8_t v___x_4862_; 
v_val_4860_ = lean_ctor_get(v_val_4858_, 1);
v___x_4861_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0));
v___x_4862_ = lean_string_dec_eq(v_val_4860_, v___x_4861_);
if (v___x_4862_ == 0)
{
lean_object* v___x_4863_; 
v___x_4863_ = lean_box(0);
return v___x_4863_;
}
else
{
lean_object* v___x_4864_; 
v___x_4864_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2));
return v___x_4864_;
}
}
else
{
lean_object* v___x_4865_; 
v___x_4865_ = lean_box(0);
return v___x_4865_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object* v_val_4891_){
_start:
{
lean_object* v_res_4892_; 
v_res_4892_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_val_4891_);
lean_dec(v_val_4891_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object* v_nameStx_4893_, lean_object* v_v_4894_, lean_object* v_c_4895_){
_start:
{
lean_object* v_toParserModuleContext_4896_; lean_object* v_toInputContext_4897_; lean_object* v_toCacheableParserContext_4898_; lean_object* v_tokens_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4936_; 
v_toParserModuleContext_4896_ = lean_ctor_get(v_c_4895_, 1);
v_toInputContext_4897_ = lean_ctor_get(v_c_4895_, 0);
v_toCacheableParserContext_4898_ = lean_ctor_get(v_c_4895_, 2);
v_tokens_4899_ = lean_ctor_get(v_c_4895_, 3);
v_isSharedCheck_4936_ = !lean_is_exclusive(v_c_4895_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4901_ = v_c_4895_;
v_isShared_4902_ = v_isSharedCheck_4936_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_tokens_4899_);
lean_inc(v_toCacheableParserContext_4898_);
lean_inc(v_toParserModuleContext_4896_);
lean_inc(v_toInputContext_4897_);
lean_dec(v_c_4895_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4936_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v_env_4903_; lean_object* v_options_4904_; lean_object* v_currNamespace_4905_; lean_object* v_openDecls_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4935_; 
v_env_4903_ = lean_ctor_get(v_toParserModuleContext_4896_, 0);
v_options_4904_ = lean_ctor_get(v_toParserModuleContext_4896_, 1);
v_currNamespace_4905_ = lean_ctor_get(v_toParserModuleContext_4896_, 2);
v_openDecls_4906_ = lean_ctor_get(v_toParserModuleContext_4896_, 3);
v_isSharedCheck_4935_ = !lean_is_exclusive(v_toParserModuleContext_4896_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4908_ = v_toParserModuleContext_4896_;
v_isShared_4909_ = v_isSharedCheck_4935_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_openDecls_4906_);
lean_inc(v_currNamespace_4905_);
lean_inc(v_options_4904_);
lean_inc(v_env_4903_);
lean_dec(v_toParserModuleContext_4896_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4935_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___y_4911_; lean_object* v_map_4918_; uint8_t v_hasTrace_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4934_; 
v_map_4918_ = lean_ctor_get(v_options_4904_, 0);
v_hasTrace_4919_ = lean_ctor_get_uint8(v_options_4904_, sizeof(void*)*1);
v_isSharedCheck_4934_ = !lean_is_exclusive(v_options_4904_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4921_ = v_options_4904_;
v_isShared_4922_ = v_isSharedCheck_4934_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_map_4918_);
lean_dec(v_options_4904_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4934_;
goto v_resetjp_4920_;
}
v___jp_4910_:
{
lean_object* v___x_4913_; 
if (v_isShared_4909_ == 0)
{
lean_ctor_set(v___x_4908_, 1, v___y_4911_);
v___x_4913_ = v___x_4908_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_env_4903_);
lean_ctor_set(v_reuseFailAlloc_4917_, 1, v___y_4911_);
lean_ctor_set(v_reuseFailAlloc_4917_, 2, v_currNamespace_4905_);
lean_ctor_set(v_reuseFailAlloc_4917_, 3, v_openDecls_4906_);
v___x_4913_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
lean_object* v___x_4915_; 
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 1, v___x_4913_);
v___x_4915_ = v___x_4901_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_toInputContext_4897_);
lean_ctor_set(v_reuseFailAlloc_4916_, 1, v___x_4913_);
lean_ctor_set(v_reuseFailAlloc_4916_, 2, v_toCacheableParserContext_4898_);
lean_ctor_set(v_reuseFailAlloc_4916_, 3, v_tokens_4899_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
v_resetjp_4920_:
{
lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4923_ = l_Lean_Syntax_getId(v_nameStx_4893_);
v___x_4924_ = l_Lean_Name_eraseMacroScopes(v___x_4923_);
lean_dec(v___x_4923_);
lean_inc(v___x_4924_);
v___x_4925_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_4924_, v_v_4894_, v_map_4918_);
if (v_hasTrace_4919_ == 0)
{
lean_object* v___x_4926_; uint8_t v___x_4927_; lean_object* v___x_4929_; 
v___x_4926_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_4927_ = l_Lean_Name_isPrefixOf(v___x_4926_, v___x_4924_);
lean_dec(v___x_4924_);
if (v_isShared_4922_ == 0)
{
lean_ctor_set(v___x_4921_, 0, v___x_4925_);
v___x_4929_ = v___x_4921_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4925_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
lean_ctor_set_uint8(v___x_4929_, sizeof(void*)*1, v___x_4927_);
v___y_4911_ = v___x_4929_;
goto v___jp_4910_;
}
}
else
{
lean_object* v___x_4932_; 
lean_dec(v___x_4924_);
if (v_isShared_4922_ == 0)
{
lean_ctor_set(v___x_4921_, 0, v___x_4925_);
v___x_4932_ = v___x_4921_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v___x_4925_);
lean_ctor_set_uint8(v_reuseFailAlloc_4933_, sizeof(void*)*1, v_hasTrace_4919_);
v___x_4932_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
v___y_4911_ = v___x_4932_;
goto v___jp_4910_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object* v_nameStx_4937_, lean_object* v_v_4938_, lean_object* v_c_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(v_nameStx_4937_, v_v_4938_, v_c_4939_);
lean_dec(v_nameStx_4937_);
return v_res_4940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object* v_nameStx_4941_, lean_object* v_valStx_4942_, lean_object* v_p_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_){
_start:
{
lean_object* v___x_4946_; 
v___x_4946_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_valStx_4942_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v___x_4947_; 
lean_dec(v_nameStx_4941_);
v___x_4947_ = lean_apply_2(v_p_4943_, v_a_4944_, v_a_4945_);
return v___x_4947_;
}
else
{
lean_object* v_val_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
v_val_4948_ = lean_ctor_get(v___x_4946_, 0);
lean_inc(v_val_4948_);
lean_dec_ref_known(v___x_4946_, 1);
v___x_4949_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed), 3, 2);
lean_closure_set(v___x_4949_, 0, v_nameStx_4941_);
lean_closure_set(v___x_4949_, 1, v_val_4948_);
v___x_4950_ = l_Lean_Parser_adaptUncacheableContextFn(v___x_4949_, v_p_4943_, v_a_4944_, v_a_4945_);
return v___x_4950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object* v_nameStx_4951_, lean_object* v_valStx_4952_, lean_object* v_p_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v_nameStx_4951_, v_valStx_4952_, v_p_4953_, v_a_4954_, v_a_4955_);
lean_dec(v_valStx_4952_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object* v_p_4963_, lean_object* v_c_4964_, lean_object* v_s_4965_){
_start:
{
lean_object* v_stxStack_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; uint8_t v___x_4969_; 
v_stxStack_4966_ = lean_ctor_get(v_s_4965_, 0);
v___x_4967_ = lean_unsigned_to_nat(0u);
v___x_4968_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4966_);
v___x_4969_ = lean_nat_dec_lt(v___x_4967_, v___x_4968_);
lean_dec(v___x_4968_);
if (v___x_4969_ == 0)
{
lean_object* v___x_4970_; 
v___x_4970_ = lean_apply_2(v_p_4963_, v_c_4964_, v_s_4965_);
return v___x_4970_;
}
else
{
lean_object* v_stx_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; uint8_t v___x_4974_; 
v_stx_4971_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4966_);
lean_inc(v_stx_4971_);
v___x_4972_ = l_Lean_Syntax_getKind(v_stx_4971_);
v___x_4973_ = ((lean_object*)(l_Lean_Parser_withSetOptionFn___closed__1));
v___x_4974_ = lean_name_eq(v___x_4972_, v___x_4973_);
lean_dec(v___x_4972_);
if (v___x_4974_ == 0)
{
lean_object* v___x_4975_; 
lean_dec(v_stx_4971_);
v___x_4975_ = lean_apply_2(v_p_4963_, v_c_4964_, v_s_4965_);
return v___x_4975_;
}
else
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4976_ = lean_unsigned_to_nat(1u);
v___x_4977_ = l_Lean_Syntax_getArg(v_stx_4971_, v___x_4976_);
v___x_4978_ = lean_unsigned_to_nat(3u);
v___x_4979_ = l_Lean_Syntax_getArg(v_stx_4971_, v___x_4978_);
lean_dec(v_stx_4971_);
v___x_4980_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_4977_, v___x_4979_, v_p_4963_, v_c_4964_, v_s_4965_);
lean_dec(v___x_4979_);
return v___x_4980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object* v_p_4981_){
_start:
{
lean_object* v_info_4982_; lean_object* v_fn_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4991_; 
v_info_4982_ = lean_ctor_get(v_p_4981_, 0);
v_fn_4983_ = lean_ctor_get(v_p_4981_, 1);
v_isSharedCheck_4991_ = !lean_is_exclusive(v_p_4981_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4985_ = v_p_4981_;
v_isShared_4986_ = v_isSharedCheck_4991_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_fn_4983_);
lean_inc(v_info_4982_);
lean_dec(v_p_4981_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4991_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4987_; lean_object* v___x_4989_; 
v___x_4987_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionFn), 3, 1);
lean_closure_set(v___x_4987_, 0, v_fn_4983_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 1, v___x_4987_);
v___x_4989_ = v___x_4985_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_info_4982_);
lean_ctor_set(v_reuseFailAlloc_4990_, 1, v___x_4987_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object* v_p_4992_, lean_object* v_c_4993_, lean_object* v_s_4994_){
_start:
{
lean_object* v_stxStack_4995_; lean_object* v_sz_4996_; lean_object* v___x_4997_; uint8_t v___x_4998_; 
v_stxStack_4995_ = lean_ctor_get(v_s_4994_, 0);
v_sz_4996_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4995_);
v___x_4997_ = lean_unsigned_to_nat(3u);
v___x_4998_ = lean_nat_dec_le(v___x_4997_, v_sz_4996_);
if (v___x_4998_ == 0)
{
lean_object* v___x_4999_; 
lean_dec(v_sz_4996_);
v___x_4999_ = lean_apply_2(v_p_4992_, v_c_4993_, v_s_4994_);
return v___x_4999_;
}
else
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_5000_ = lean_nat_sub(v_sz_4996_, v___x_4997_);
lean_dec(v_sz_4996_);
v___x_5001_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_4995_, v___x_5000_);
lean_dec(v___x_5000_);
v___x_5002_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4995_);
v___x_5003_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5001_, v___x_5002_, v_p_4992_, v_c_4993_, v_s_4994_);
lean_dec(v___x_5002_);
return v___x_5003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object* v_p_5004_){
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
v___x_5010_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionValueFn), 3, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object* v___x_5015_){
_start:
{
lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___x_5017_ = lean_st_ref_get(v___x_5015_);
v___x_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5018_, 0, v___x_5017_);
return v___x_5018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v___x_5019_, lean_object* v___y_5020_){
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_5019_);
lean_dec(v___x_5019_);
return v_res_5021_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5022_; lean_object* v___f_5023_; 
v___x_5022_ = l_Lean_Parser_parserAliasesRef;
v___f_5023_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5023_, 0, v___x_5022_);
return v___f_5023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; 
v___f_5025_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_);
v___x_5026_ = lean_box(0);
v___x_5027_ = lean_box(2);
v___x_5028_ = l_Lean_registerEnvExtension___redArg(v___f_5025_, v___x_5026_, v___x_5027_);
return v___x_5028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v_a_5029_){
_start:
{
lean_object* v_res_5030_; 
v_res_5030_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
return v_res_5030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx(lean_object* v_x_5031_){
_start:
{
switch(lean_obj_tag(v_x_5031_))
{
case 0:
{
lean_object* v___x_5032_; 
v___x_5032_ = lean_unsigned_to_nat(0u);
return v___x_5032_;
}
case 1:
{
lean_object* v___x_5033_; 
v___x_5033_ = lean_unsigned_to_nat(1u);
return v___x_5033_;
}
default: 
{
lean_object* v___x_5034_; 
v___x_5034_ = lean_unsigned_to_nat(2u);
return v___x_5034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___boxed(lean_object* v_x_5035_){
_start:
{
lean_object* v_res_5036_; 
v_res_5036_ = l_Lean_Parser_ParserResolution_ctorIdx(v_x_5035_);
lean_dec_ref(v_x_5035_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object* v_t_5037_, lean_object* v_k_5038_){
_start:
{
switch(lean_obj_tag(v_t_5037_))
{
case 0:
{
lean_object* v_cat_5039_; lean_object* v___x_5040_; 
v_cat_5039_ = lean_ctor_get(v_t_5037_, 0);
lean_inc(v_cat_5039_);
lean_dec_ref_known(v_t_5037_, 1);
v___x_5040_ = lean_apply_1(v_k_5038_, v_cat_5039_);
return v___x_5040_;
}
case 1:
{
lean_object* v_decl_5041_; uint8_t v_isDescr_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v_decl_5041_ = lean_ctor_get(v_t_5037_, 0);
lean_inc(v_decl_5041_);
v_isDescr_5042_ = lean_ctor_get_uint8(v_t_5037_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5037_, 1);
v___x_5043_ = lean_box(v_isDescr_5042_);
v___x_5044_ = lean_apply_2(v_k_5038_, v_decl_5041_, v___x_5043_);
return v___x_5044_;
}
default: 
{
lean_object* v_p_5045_; lean_object* v___x_5046_; 
v_p_5045_ = lean_ctor_get(v_t_5037_, 0);
lean_inc_ref(v_p_5045_);
lean_dec_ref_known(v_t_5037_, 1);
v___x_5046_ = lean_apply_1(v_k_5038_, v_p_5045_);
return v___x_5046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object* v_motive_5047_, lean_object* v_ctorIdx_5048_, lean_object* v_t_5049_, lean_object* v_h_5050_, lean_object* v_k_5051_){
_start:
{
lean_object* v___x_5052_; 
v___x_5052_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5049_, v_k_5051_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object* v_motive_5053_, lean_object* v_ctorIdx_5054_, lean_object* v_t_5055_, lean_object* v_h_5056_, lean_object* v_k_5057_){
_start:
{
lean_object* v_res_5058_; 
v_res_5058_ = l_Lean_Parser_ParserResolution_ctorElim(v_motive_5053_, v_ctorIdx_5054_, v_t_5055_, v_h_5056_, v_k_5057_);
lean_dec(v_ctorIdx_5054_);
return v_res_5058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object* v_t_5059_, lean_object* v_category_5060_){
_start:
{
lean_object* v___x_5061_; 
v___x_5061_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5059_, v_category_5060_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object* v_motive_5062_, lean_object* v_t_5063_, lean_object* v_h_5064_, lean_object* v_category_5065_){
_start:
{
lean_object* v___x_5066_; 
v___x_5066_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5063_, v_category_5065_);
return v___x_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object* v_t_5067_, lean_object* v_parser_5068_){
_start:
{
lean_object* v___x_5069_; 
v___x_5069_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5067_, v_parser_5068_);
return v___x_5069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object* v_motive_5070_, lean_object* v_t_5071_, lean_object* v_h_5072_, lean_object* v_parser_5073_){
_start:
{
lean_object* v___x_5074_; 
v___x_5074_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5071_, v_parser_5073_);
return v___x_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object* v_t_5075_, lean_object* v_alias_5076_){
_start:
{
lean_object* v___x_5077_; 
v___x_5077_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5075_, v_alias_5076_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object* v_motive_5078_, lean_object* v_t_5079_, lean_object* v_h_5080_, lean_object* v_alias_5081_){
_start:
{
lean_object* v___x_5082_; 
v___x_5082_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5079_, v_alias_5081_);
return v___x_5082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object* v_env_5086_, lean_object* v_name_5087_){
_start:
{
uint8_t v___x_5088_; lean_object* v___x_5089_; 
v___x_5088_ = 0;
v___x_5089_ = l_Lean_Environment_find_x3f(v_env_5086_, v_name_5087_, v___x_5088_);
if (lean_obj_tag(v___x_5089_) == 0)
{
lean_object* v___x_5090_; 
v___x_5090_ = lean_box(0);
return v___x_5090_;
}
else
{
lean_object* v_val_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5138_; 
v_val_5091_ = lean_ctor_get(v___x_5089_, 0);
v_isSharedCheck_5138_ = !lean_is_exclusive(v___x_5089_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_5093_ = v___x_5089_;
v_isShared_5094_ = v_isSharedCheck_5138_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_val_5091_);
lean_dec(v___x_5089_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5138_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v___x_5095_; 
v___x_5095_ = l_Lean_ConstantInfo_type(v_val_5091_);
lean_dec(v_val_5091_);
if (lean_obj_tag(v___x_5095_) == 4)
{
lean_object* v_declName_5096_; 
v_declName_5096_ = lean_ctor_get(v___x_5095_, 0);
lean_inc(v_declName_5096_);
lean_dec_ref_known(v___x_5095_, 2);
if (lean_obj_tag(v_declName_5096_) == 1)
{
lean_object* v_pre_5097_; 
v_pre_5097_ = lean_ctor_get(v_declName_5096_, 0);
lean_inc(v_pre_5097_);
if (lean_obj_tag(v_pre_5097_) == 1)
{
lean_object* v_pre_5098_; 
v_pre_5098_ = lean_ctor_get(v_pre_5097_, 0);
switch(lean_obj_tag(v_pre_5098_))
{
case 1:
{
lean_object* v_pre_5099_; 
lean_inc_ref(v_pre_5098_);
lean_del_object(v___x_5093_);
v_pre_5099_ = lean_ctor_get(v_pre_5098_, 0);
if (lean_obj_tag(v_pre_5099_) == 0)
{
lean_object* v_str_5100_; lean_object* v_str_5101_; lean_object* v_str_5102_; lean_object* v___x_5103_; uint8_t v___x_5104_; 
v_str_5100_ = lean_ctor_get(v_declName_5096_, 1);
lean_inc_ref(v_str_5100_);
lean_dec_ref_known(v_declName_5096_, 2);
v_str_5101_ = lean_ctor_get(v_pre_5097_, 1);
lean_inc_ref(v_str_5101_);
lean_dec_ref_known(v_pre_5097_, 2);
v_str_5102_ = lean_ctor_get(v_pre_5098_, 1);
lean_inc_ref(v_str_5102_);
lean_dec_ref_known(v_pre_5098_, 2);
v___x_5103_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5104_ = lean_string_dec_eq(v_str_5102_, v___x_5103_);
lean_dec_ref(v_str_5102_);
if (v___x_5104_ == 0)
{
lean_object* v___x_5105_; 
lean_dec_ref(v_str_5101_);
lean_dec_ref(v_str_5100_);
v___x_5105_ = lean_box(0);
return v___x_5105_;
}
else
{
lean_object* v___x_5106_; uint8_t v___x_5107_; 
v___x_5106_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_5107_ = lean_string_dec_eq(v_str_5101_, v___x_5106_);
lean_dec_ref(v_str_5101_);
if (v___x_5107_ == 0)
{
lean_object* v___x_5108_; 
lean_dec_ref(v_str_5100_);
v___x_5108_ = lean_box(0);
return v___x_5108_;
}
else
{
uint8_t v___x_5109_; 
v___x_5109_ = lean_string_dec_eq(v_str_5100_, v___x_5106_);
if (v___x_5109_ == 0)
{
lean_object* v___x_5110_; uint8_t v___x_5111_; 
v___x_5110_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_5111_ = lean_string_dec_eq(v_str_5100_, v___x_5110_);
lean_dec_ref(v_str_5100_);
if (v___x_5111_ == 0)
{
lean_object* v___x_5112_; 
v___x_5112_ = lean_box(0);
return v___x_5112_;
}
else
{
lean_object* v___x_5113_; 
v___x_5113_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5113_;
}
}
else
{
lean_object* v___x_5114_; 
lean_dec_ref(v_str_5100_);
v___x_5114_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5114_;
}
}
}
}
else
{
lean_object* v___x_5115_; 
lean_dec_ref_known(v_pre_5098_, 2);
lean_dec_ref_known(v_pre_5097_, 2);
lean_dec_ref_known(v_declName_5096_, 2);
v___x_5115_ = lean_box(0);
return v___x_5115_;
}
}
case 0:
{
lean_object* v_str_5116_; lean_object* v_str_5117_; lean_object* v___x_5118_; uint8_t v___x_5119_; 
v_str_5116_ = lean_ctor_get(v_declName_5096_, 1);
lean_inc_ref(v_str_5116_);
lean_dec_ref_known(v_declName_5096_, 2);
v_str_5117_ = lean_ctor_get(v_pre_5097_, 1);
lean_inc_ref(v_str_5117_);
lean_dec_ref_known(v_pre_5097_, 2);
v___x_5118_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5119_ = lean_string_dec_eq(v_str_5117_, v___x_5118_);
lean_dec_ref(v_str_5117_);
if (v___x_5119_ == 0)
{
lean_object* v___x_5120_; 
lean_dec_ref(v_str_5116_);
lean_del_object(v___x_5093_);
v___x_5120_ = lean_box(0);
return v___x_5120_;
}
else
{
lean_object* v___x_5121_; uint8_t v___x_5122_; 
v___x_5121_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_5122_ = lean_string_dec_eq(v_str_5116_, v___x_5121_);
if (v___x_5122_ == 0)
{
lean_object* v___x_5123_; uint8_t v___x_5124_; 
v___x_5123_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_5124_ = lean_string_dec_eq(v_str_5116_, v___x_5123_);
lean_dec_ref(v_str_5116_);
if (v___x_5124_ == 0)
{
lean_object* v___x_5125_; 
lean_del_object(v___x_5093_);
v___x_5125_ = lean_box(0);
return v___x_5125_;
}
else
{
lean_object* v___x_5126_; lean_object* v___x_5128_; 
v___x_5126_ = lean_box(v___x_5119_);
if (v_isShared_5094_ == 0)
{
lean_ctor_set(v___x_5093_, 0, v___x_5126_);
v___x_5128_ = v___x_5093_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5126_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
else
{
lean_object* v___x_5130_; lean_object* v___x_5132_; 
lean_dec_ref(v_str_5116_);
v___x_5130_ = lean_box(v___x_5119_);
if (v_isShared_5094_ == 0)
{
lean_ctor_set(v___x_5093_, 0, v___x_5130_);
v___x_5132_ = v___x_5093_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v___x_5130_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
return v___x_5132_;
}
}
}
}
default: 
{
lean_object* v___x_5134_; 
lean_dec_ref_known(v_pre_5097_, 2);
lean_dec_ref_known(v_declName_5096_, 2);
lean_del_object(v___x_5093_);
v___x_5134_ = lean_box(0);
return v___x_5134_;
}
}
}
else
{
lean_object* v___x_5135_; 
lean_dec_ref_known(v_declName_5096_, 2);
lean_dec(v_pre_5097_);
lean_del_object(v___x_5093_);
v___x_5135_ = lean_box(0);
return v___x_5135_;
}
}
else
{
lean_object* v___x_5136_; 
lean_dec(v_declName_5096_);
lean_del_object(v___x_5093_);
v___x_5136_ = lean_box(0);
return v___x_5136_;
}
}
else
{
lean_object* v___x_5137_; 
lean_dec_ref(v___x_5095_);
lean_del_object(v___x_5093_);
v___x_5137_ = lean_box(0);
return v___x_5137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object* v_env_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_){
_start:
{
if (lean_obj_tag(v_a_5140_) == 0)
{
lean_object* v___x_5142_; 
lean_dec_ref(v_env_5139_);
v___x_5142_ = lean_array_to_list(v_a_5141_);
return v___x_5142_;
}
else
{
lean_object* v_head_5143_; lean_object* v_snd_5144_; 
v_head_5143_ = lean_ctor_get(v_a_5140_, 0);
v_snd_5144_ = lean_ctor_get(v_head_5143_, 1);
if (lean_obj_tag(v_snd_5144_) == 0)
{
lean_object* v_tail_5145_; lean_object* v_fst_5146_; lean_object* v___x_5147_; 
lean_inc(v_head_5143_);
v_tail_5145_ = lean_ctor_get(v_a_5140_, 1);
lean_inc(v_tail_5145_);
lean_dec_ref_known(v_a_5140_, 2);
v_fst_5146_ = lean_ctor_get(v_head_5143_, 0);
lean_inc_n(v_fst_5146_, 2);
lean_dec(v_head_5143_);
lean_inc_ref(v_env_5139_);
v___x_5147_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5139_, v_fst_5146_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_dec(v_fst_5146_);
v_a_5140_ = v_tail_5145_;
goto _start;
}
else
{
lean_object* v_val_5149_; lean_object* v___x_5150_; uint8_t v___x_5151_; lean_object* v___x_5152_; 
v_val_5149_ = lean_ctor_get(v___x_5147_, 0);
lean_inc(v_val_5149_);
lean_dec_ref_known(v___x_5147_, 1);
v___x_5150_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5150_, 0, v_fst_5146_);
v___x_5151_ = lean_unbox(v_val_5149_);
lean_dec(v_val_5149_);
lean_ctor_set_uint8(v___x_5150_, sizeof(void*)*1, v___x_5151_);
v___x_5152_ = lean_array_push(v_a_5141_, v___x_5150_);
v_a_5140_ = v_tail_5145_;
v_a_5141_ = v___x_5152_;
goto _start;
}
}
else
{
lean_object* v_tail_5154_; 
v_tail_5154_ = lean_ctor_get(v_a_5140_, 1);
lean_inc(v_tail_5154_);
lean_dec_ref_known(v_a_5140_, 2);
v_a_5140_ = v_tail_5154_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object* v_env_5159_, lean_object* v_as_x27_5160_, lean_object* v_b_5161_){
_start:
{
if (lean_obj_tag(v_as_x27_5160_) == 0)
{
lean_dec_ref(v_env_5159_);
lean_inc_ref(v_b_5161_);
return v_b_5161_;
}
else
{
lean_object* v_head_5162_; lean_object* v_tail_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; 
v_head_5162_ = lean_ctor_get(v_as_x27_5160_, 0);
v_tail_5163_ = lean_ctor_get(v_as_x27_5160_, 1);
v___x_5164_ = lean_box(0);
v___x_5165_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_5162_) == 1)
{
lean_object* v_fields_5166_; 
v_fields_5166_ = lean_ctor_get(v_head_5162_, 1);
if (lean_obj_tag(v_fields_5166_) == 0)
{
lean_object* v_n_5167_; lean_object* v___x_5168_; 
v_n_5167_ = lean_ctor_get(v_head_5162_, 0);
lean_inc(v_n_5167_);
lean_inc_ref(v_env_5159_);
v___x_5168_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5159_, v_n_5167_);
if (lean_obj_tag(v___x_5168_) == 1)
{
lean_object* v_val_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5181_; 
lean_dec_ref(v_env_5159_);
v_val_5169_ = lean_ctor_get(v___x_5168_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5168_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5171_ = v___x_5168_;
v_isShared_5172_ = v_isSharedCheck_5181_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_val_5169_);
lean_dec(v___x_5168_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5181_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5173_; uint8_t v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5178_; 
lean_inc(v_n_5167_);
v___x_5173_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5173_, 0, v_n_5167_);
v___x_5174_ = lean_unbox(v_val_5169_);
lean_dec(v_val_5169_);
lean_ctor_set_uint8(v___x_5173_, sizeof(void*)*1, v___x_5174_);
v___x_5175_ = lean_box(0);
v___x_5176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5176_, 0, v___x_5173_);
lean_ctor_set(v___x_5176_, 1, v___x_5175_);
if (v_isShared_5172_ == 0)
{
lean_ctor_set(v___x_5171_, 0, v___x_5176_);
v___x_5178_ = v___x_5171_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v___x_5176_);
v___x_5178_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
lean_object* v___x_5179_; 
v___x_5179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5179_, 0, v___x_5178_);
lean_ctor_set(v___x_5179_, 1, v___x_5164_);
return v___x_5179_;
}
}
}
else
{
lean_dec(v___x_5168_);
v_as_x27_5160_ = v_tail_5163_;
v_b_5161_ = v___x_5165_;
goto _start;
}
}
else
{
v_as_x27_5160_ = v_tail_5163_;
v_b_5161_ = v___x_5165_;
goto _start;
}
}
else
{
v_as_x27_5160_ = v_tail_5163_;
v_b_5161_ = v___x_5165_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object* v_env_5185_, lean_object* v_as_x27_5186_, lean_object* v_b_5187_){
_start:
{
lean_object* v_res_5188_; 
v_res_5188_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5185_, v_as_x27_5186_, v_b_5187_);
lean_dec_ref(v_b_5187_);
lean_dec(v_as_x27_5186_);
return v_res_5188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object* v_env_5191_, lean_object* v_opts_5192_, lean_object* v_currNamespace_5193_, lean_object* v_openDecls_5194_, lean_object* v_ident_5195_){
_start:
{
if (lean_obj_tag(v_ident_5195_) == 3)
{
lean_object* v_val_5196_; lean_object* v_preresolved_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v_fst_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5235_; 
v_val_5196_ = lean_ctor_get(v_ident_5195_, 2);
lean_inc(v_val_5196_);
v_preresolved_5197_ = lean_ctor_get(v_ident_5195_, 3);
lean_inc(v_preresolved_5197_);
lean_dec_ref_known(v_ident_5195_, 4);
v___x_5198_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
lean_inc_ref(v_env_5191_);
v___x_5199_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5191_, v_preresolved_5197_, v___x_5198_);
lean_dec(v_preresolved_5197_);
v_fst_5200_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5235_ == 0)
{
lean_object* v_unused_5236_; 
v_unused_5236_ = lean_ctor_get(v___x_5199_, 1);
lean_dec(v_unused_5236_);
v___x_5202_ = v___x_5199_;
v_isShared_5203_ = v_isSharedCheck_5235_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_fst_5200_);
lean_dec(v___x_5199_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5235_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
if (lean_obj_tag(v_fst_5200_) == 0)
{
lean_object* v___x_5204_; uint8_t v___x_5205_; 
v___x_5204_ = l_Lean_Name_eraseMacroScopes(v_val_5196_);
lean_inc_ref(v_env_5191_);
v___x_5205_ = l_Lean_Parser_isParserCategory(v_env_5191_, v___x_5204_);
if (v___x_5205_ == 0)
{
lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; uint8_t v___x_5209_; 
lean_inc_ref_n(v_env_5191_, 2);
v___x_5206_ = l_Lean_ResolveName_resolveGlobalName(v_env_5191_, v_opts_5192_, v_currNamespace_5193_, v_openDecls_5194_, v_val_5196_);
v___x_5207_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0));
v___x_5208_ = l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(v_env_5191_, v___x_5206_, v___x_5207_);
v___x_5209_ = l_List_isEmpty___redArg(v___x_5208_);
if (v___x_5209_ == 0)
{
lean_dec(v___x_5204_);
lean_del_object(v___x_5202_);
lean_dec_ref(v_env_5191_);
return v___x_5208_;
}
else
{
lean_object* v___x_5210_; lean_object* v_asyncMode_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; 
lean_dec(v___x_5208_);
v___x_5210_ = l_Lean_Parser_aliasExtension;
v_asyncMode_5211_ = lean_ctor_get(v___x_5210_, 2);
v___x_5212_ = lean_box(1);
v___x_5213_ = lean_box(0);
v___x_5214_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5212_, v___x_5210_, v_env_5191_, v_asyncMode_5211_, v___x_5213_);
v___x_5215_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5214_, v___x_5204_);
lean_dec(v___x_5204_);
lean_dec(v___x_5214_);
if (lean_obj_tag(v___x_5215_) == 1)
{
lean_object* v_val_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5227_; 
v_val_5216_ = lean_ctor_get(v___x_5215_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5215_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5218_ = v___x_5215_;
v_isShared_5219_ = v_isSharedCheck_5227_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_val_5216_);
lean_dec(v___x_5215_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5227_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
lean_ctor_set_tag(v___x_5218_, 2);
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_val_5216_);
v___x_5221_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
lean_object* v___x_5222_; lean_object* v___x_5224_; 
v___x_5222_ = lean_box(0);
if (v_isShared_5203_ == 0)
{
lean_ctor_set_tag(v___x_5202_, 1);
lean_ctor_set(v___x_5202_, 1, v___x_5222_);
lean_ctor_set(v___x_5202_, 0, v___x_5221_);
v___x_5224_ = v___x_5202_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v___x_5221_);
lean_ctor_set(v_reuseFailAlloc_5225_, 1, v___x_5222_);
v___x_5224_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
return v___x_5224_;
}
}
}
}
else
{
lean_object* v___x_5228_; 
lean_dec(v___x_5215_);
lean_del_object(v___x_5202_);
v___x_5228_ = lean_box(0);
return v___x_5228_;
}
}
}
else
{
lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5232_; 
lean_dec(v_val_5196_);
lean_dec(v_openDecls_5194_);
lean_dec(v_currNamespace_5193_);
lean_dec_ref(v_env_5191_);
v___x_5229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5229_, 0, v___x_5204_);
v___x_5230_ = lean_box(0);
if (v_isShared_5203_ == 0)
{
lean_ctor_set_tag(v___x_5202_, 1);
lean_ctor_set(v___x_5202_, 1, v___x_5230_);
lean_ctor_set(v___x_5202_, 0, v___x_5229_);
v___x_5232_ = v___x_5202_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v___x_5229_);
lean_ctor_set(v_reuseFailAlloc_5233_, 1, v___x_5230_);
v___x_5232_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
return v___x_5232_;
}
}
}
else
{
lean_object* v_val_5234_; 
lean_del_object(v___x_5202_);
lean_dec(v_val_5196_);
lean_dec(v_openDecls_5194_);
lean_dec(v_currNamespace_5193_);
lean_dec_ref(v_env_5191_);
v_val_5234_ = lean_ctor_get(v_fst_5200_, 0);
lean_inc(v_val_5234_);
lean_dec_ref_known(v_fst_5200_, 1);
return v_val_5234_;
}
}
}
else
{
lean_object* v___x_5237_; 
lean_dec(v_ident_5195_);
lean_dec(v_openDecls_5194_);
lean_dec(v_currNamespace_5193_);
lean_dec_ref(v_env_5191_);
v___x_5237_ = lean_box(0);
return v___x_5237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object* v_env_5238_, lean_object* v_opts_5239_, lean_object* v_currNamespace_5240_, lean_object* v_openDecls_5241_, lean_object* v_ident_5242_){
_start:
{
lean_object* v_res_5243_; 
v_res_5243_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5238_, v_opts_5239_, v_currNamespace_5240_, v_openDecls_5241_, v_ident_5242_);
lean_dec_ref(v_opts_5239_);
return v_res_5243_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object* v_env_5244_, lean_object* v_as_5245_, lean_object* v_as_x27_5246_, lean_object* v_b_5247_, lean_object* v_a_5248_){
_start:
{
lean_object* v___x_5249_; 
v___x_5249_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5244_, v_as_x27_5246_, v_b_5247_);
return v___x_5249_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object* v_env_5250_, lean_object* v_as_5251_, lean_object* v_as_x27_5252_, lean_object* v_b_5253_, lean_object* v_a_5254_){
_start:
{
lean_object* v_res_5255_; 
v_res_5255_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(v_env_5250_, v_as_5251_, v_as_x27_5252_, v_b_5253_, v_a_5254_);
lean_dec_ref(v_b_5253_);
lean_dec(v_as_x27_5252_);
lean_dec(v_as_5251_);
return v_res_5255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object* v_ctx_5256_, lean_object* v_id_5257_, uint8_t v_unsetExporting_5258_){
_start:
{
lean_object* v___y_5260_; 
if (v_unsetExporting_5258_ == 0)
{
lean_object* v_toParserModuleContext_5266_; lean_object* v_env_5267_; 
v_toParserModuleContext_5266_ = lean_ctor_get(v_ctx_5256_, 1);
v_env_5267_ = lean_ctor_get(v_toParserModuleContext_5266_, 0);
lean_inc_ref(v_env_5267_);
v___y_5260_ = v_env_5267_;
goto v___jp_5259_;
}
else
{
lean_object* v_toParserModuleContext_5268_; lean_object* v_env_5269_; uint8_t v___x_5270_; lean_object* v___x_5271_; 
v_toParserModuleContext_5268_ = lean_ctor_get(v_ctx_5256_, 1);
v_env_5269_ = lean_ctor_get(v_toParserModuleContext_5268_, 0);
v___x_5270_ = 0;
lean_inc_ref(v_env_5269_);
v___x_5271_ = l_Lean_Environment_setExporting(v_env_5269_, v___x_5270_);
v___y_5260_ = v___x_5271_;
goto v___jp_5259_;
}
v___jp_5259_:
{
lean_object* v_toParserModuleContext_5261_; lean_object* v_options_5262_; lean_object* v_currNamespace_5263_; lean_object* v_openDecls_5264_; lean_object* v___x_5265_; 
v_toParserModuleContext_5261_ = lean_ctor_get(v_ctx_5256_, 1);
lean_inc_ref(v_toParserModuleContext_5261_);
lean_dec_ref(v_ctx_5256_);
v_options_5262_ = lean_ctor_get(v_toParserModuleContext_5261_, 1);
lean_inc_ref(v_options_5262_);
v_currNamespace_5263_ = lean_ctor_get(v_toParserModuleContext_5261_, 2);
lean_inc(v_currNamespace_5263_);
v_openDecls_5264_ = lean_ctor_get(v_toParserModuleContext_5261_, 3);
lean_inc(v_openDecls_5264_);
lean_dec_ref(v_toParserModuleContext_5261_);
v___x_5265_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v___y_5260_, v_options_5262_, v_currNamespace_5263_, v_openDecls_5264_, v_id_5257_);
lean_dec_ref(v_options_5262_);
return v___x_5265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object* v_ctx_5272_, lean_object* v_id_5273_, lean_object* v_unsetExporting_5274_){
_start:
{
uint8_t v_unsetExporting_boxed_5275_; lean_object* v_res_5276_; 
v_unsetExporting_boxed_5275_ = lean_unbox(v_unsetExporting_5274_);
v_res_5276_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5272_, v_id_5273_, v_unsetExporting_boxed_5275_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object* v_id_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_){
_start:
{
lean_object* v___x_5281_; lean_object* v_toCold_5282_; lean_object* v_env_5283_; lean_object* v_currNamespace_5284_; lean_object* v_openDecls_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5281_ = lean_st_ref_get(v_a_5279_);
v_toCold_5282_ = lean_ctor_get(v_a_5278_, 0);
v_env_5283_ = lean_ctor_get(v___x_5281_, 0);
lean_inc_ref(v_env_5283_);
lean_dec(v___x_5281_);
v_currNamespace_5284_ = lean_ctor_get(v_toCold_5282_, 4);
v_openDecls_5285_ = lean_ctor_get(v_toCold_5282_, 5);
v___x_5286_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_5278_);
lean_inc(v_openDecls_5285_);
lean_inc(v_currNamespace_5284_);
v___x_5287_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5283_, v___x_5286_, v_currNamespace_5284_, v_openDecls_5285_, v_id_5277_);
lean_dec_ref(v___x_5286_);
v___x_5288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5288_, 0, v___x_5287_);
return v___x_5288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object* v_id_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_){
_start:
{
lean_object* v_res_5293_; 
v_res_5293_ = l_Lean_Parser_resolveParserName(v_id_5289_, v_a_5290_, v_a_5291_);
lean_dec(v_a_5291_);
lean_dec_ref(v_a_5290_);
return v_res_5293_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object* v_x_5294_, lean_object* v_x_5295_){
_start:
{
if (lean_obj_tag(v_x_5294_) == 0)
{
if (lean_obj_tag(v_x_5295_) == 0)
{
uint8_t v___x_5296_; 
v___x_5296_ = 1;
return v___x_5296_;
}
else
{
uint8_t v___x_5297_; 
v___x_5297_ = 0;
return v___x_5297_;
}
}
else
{
if (lean_obj_tag(v_x_5295_) == 0)
{
uint8_t v___x_5298_; 
v___x_5298_ = 0;
return v___x_5298_;
}
else
{
lean_object* v_val_5299_; lean_object* v_val_5300_; uint8_t v___x_5301_; 
v_val_5299_ = lean_ctor_get(v_x_5294_, 0);
v_val_5300_ = lean_ctor_get(v_x_5295_, 0);
v___x_5301_ = l_Lean_Parser_instBEqError_beq(v_val_5299_, v_val_5300_);
return v___x_5301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object* v_x_5302_, lean_object* v_x_5303_){
_start:
{
uint8_t v_res_5304_; lean_object* v_r_5305_; 
v_res_5304_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5302_, v_x_5303_);
lean_dec(v_x_5303_);
lean_dec(v_x_5302_);
v_r_5305_ = lean_box(v_res_5304_);
return v_r_5305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t v___x_5306_, lean_object* v_ctx_5307_){
_start:
{
lean_object* v_toParserModuleContext_5308_; lean_object* v_toInputContext_5309_; lean_object* v_toCacheableParserContext_5310_; lean_object* v_tokens_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5336_; 
v_toParserModuleContext_5308_ = lean_ctor_get(v_ctx_5307_, 1);
v_toInputContext_5309_ = lean_ctor_get(v_ctx_5307_, 0);
v_toCacheableParserContext_5310_ = lean_ctor_get(v_ctx_5307_, 2);
v_tokens_5311_ = lean_ctor_get(v_ctx_5307_, 3);
v_isSharedCheck_5336_ = !lean_is_exclusive(v_ctx_5307_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5313_ = v_ctx_5307_;
v_isShared_5314_ = v_isSharedCheck_5336_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_tokens_5311_);
lean_inc(v_toCacheableParserContext_5310_);
lean_inc(v_toParserModuleContext_5308_);
lean_inc(v_toInputContext_5309_);
lean_dec(v_ctx_5307_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5336_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v_env_5315_; lean_object* v_options_5316_; lean_object* v_currNamespace_5317_; lean_object* v_openDecls_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5335_; 
v_env_5315_ = lean_ctor_get(v_toParserModuleContext_5308_, 0);
v_options_5316_ = lean_ctor_get(v_toParserModuleContext_5308_, 1);
v_currNamespace_5317_ = lean_ctor_get(v_toParserModuleContext_5308_, 2);
v_openDecls_5318_ = lean_ctor_get(v_toParserModuleContext_5308_, 3);
v_isSharedCheck_5335_ = !lean_is_exclusive(v_toParserModuleContext_5308_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5320_ = v_toParserModuleContext_5308_;
v_isShared_5321_ = v_isSharedCheck_5335_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_openDecls_5318_);
lean_inc(v_currNamespace_5317_);
lean_inc(v_options_5316_);
lean_inc(v_env_5315_);
lean_dec(v_toParserModuleContext_5308_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5335_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5322_; uint8_t v___y_5324_; lean_object* v___x_5332_; uint8_t v___x_5333_; 
v___x_5322_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_5332_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_5333_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_5316_, v___x_5332_);
if (v___x_5333_ == 0)
{
uint8_t v___x_5334_; 
v___x_5334_ = 1;
v___y_5324_ = v___x_5334_;
goto v___jp_5323_;
}
else
{
v___y_5324_ = v___x_5306_;
goto v___jp_5323_;
}
v___jp_5323_:
{
lean_object* v___x_5325_; lean_object* v___x_5327_; 
v___x_5325_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_5316_, v___x_5322_, v___y_5324_);
if (v_isShared_5321_ == 0)
{
lean_ctor_set(v___x_5320_, 1, v___x_5325_);
v___x_5327_ = v___x_5320_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_env_5315_);
lean_ctor_set(v_reuseFailAlloc_5331_, 1, v___x_5325_);
lean_ctor_set(v_reuseFailAlloc_5331_, 2, v_currNamespace_5317_);
lean_ctor_set(v_reuseFailAlloc_5331_, 3, v_openDecls_5318_);
v___x_5327_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
lean_object* v___x_5329_; 
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 1, v___x_5327_);
v___x_5329_ = v___x_5313_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_toInputContext_5309_);
lean_ctor_set(v_reuseFailAlloc_5330_, 1, v___x_5327_);
lean_ctor_set(v_reuseFailAlloc_5330_, 2, v_toCacheableParserContext_5310_);
lean_ctor_set(v_reuseFailAlloc_5330_, 3, v_tokens_5311_);
v___x_5329_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
return v___x_5329_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object* v___x_5337_, lean_object* v_ctx_5338_){
_start:
{
uint8_t v___x_1069__boxed_5339_; lean_object* v_res_5340_; 
v___x_1069__boxed_5339_ = lean_unbox(v___x_5337_);
v_res_5340_ = l_Lean_Parser_parserOfStackFn___lam__0(v___x_1069__boxed_5339_, v_ctx_5338_);
return v_res_5340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* v_offset_5348_, lean_object* v_ctx_5349_, lean_object* v_s_5350_){
_start:
{
lean_object* v_stxStack_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; uint8_t v___x_5355_; 
v_stxStack_5351_ = lean_ctor_get(v_s_5350_, 0);
v___x_5352_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5351_);
v___x_5353_ = lean_unsigned_to_nat(1u);
v___x_5354_ = lean_nat_add(v_offset_5348_, v___x_5353_);
v___x_5355_ = lean_nat_dec_lt(v___x_5352_, v___x_5354_);
lean_dec(v___x_5354_);
if (v___x_5355_ == 0)
{
lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; 
v___x_5356_ = lean_nat_sub(v___x_5352_, v_offset_5348_);
lean_dec(v___x_5352_);
v___x_5357_ = lean_nat_sub(v___x_5356_, v___x_5353_);
lean_dec(v___x_5356_);
v___x_5358_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5351_, v___x_5357_);
lean_dec(v___x_5357_);
if (lean_obj_tag(v___x_5358_) == 3)
{
uint8_t v___x_5370_; lean_object* v___x_5371_; 
v___x_5370_ = 1;
lean_inc_ref(v___x_5358_);
lean_inc_ref(v_ctx_5349_);
v___x_5371_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5349_, v___x_5358_, v___x_5370_);
if (lean_obj_tag(v___x_5371_) == 0)
{
lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; 
lean_dec_ref(v_ctx_5349_);
v___x_5372_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__1));
v___x_5373_ = lean_box(0);
v___x_5374_ = l_Lean_Syntax_formatStx(v___x_5358_, v___x_5373_, v___x_5355_);
v___x_5375_ = l_Std_Format_defWidth;
v___x_5376_ = lean_unsigned_to_nat(0u);
v___x_5377_ = l_Std_Format_pretty(v___x_5374_, v___x_5375_, v___x_5376_, v___x_5376_);
v___x_5378_ = lean_string_append(v___x_5372_, v___x_5377_);
lean_dec_ref(v___x_5377_);
v___x_5379_ = lean_box(0);
v___x_5380_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5350_, v___x_5378_, v___x_5379_, v___x_5370_);
return v___x_5380_;
}
else
{
lean_object* v_head_5381_; lean_object* v_tail_5382_; lean_object* v_iniSz_5383_; lean_object* v_s_5385_; 
v_head_5381_ = lean_ctor_get(v___x_5371_, 0);
lean_inc(v_head_5381_);
v_tail_5382_ = lean_ctor_get(v___x_5371_, 1);
lean_inc(v_tail_5382_);
lean_dec_ref_known(v___x_5371_, 2);
v_iniSz_5383_ = l_Lean_Parser_ParserState_stackSize(v_s_5350_);
switch(lean_obj_tag(v_head_5381_))
{
case 0:
{
if (lean_obj_tag(v_tail_5382_) == 0)
{
lean_object* v_cat_5395_; lean_object* v___x_5396_; 
lean_dec_ref_known(v___x_5358_, 4);
v_cat_5395_ = lean_ctor_get(v_head_5381_, 0);
lean_inc(v_cat_5395_);
lean_dec_ref_known(v_head_5381_, 1);
v___x_5396_ = l_Lean_Parser_categoryParserFn(v_cat_5395_, v_ctx_5349_, v_s_5350_);
v_s_5385_ = v___x_5396_;
goto v___jp_5384_;
}
else
{
lean_dec_ref_known(v_tail_5382_, 2);
lean_dec_ref_known(v_head_5381_, 1);
lean_dec(v_iniSz_5383_);
lean_dec_ref(v_ctx_5349_);
goto v___jp_5359_;
}
}
case 1:
{
if (lean_obj_tag(v_tail_5382_) == 0)
{
lean_object* v_decl_5397_; lean_object* v___x_5398_; lean_object* v___f_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
lean_dec_ref_known(v___x_5358_, 4);
v_decl_5397_ = lean_ctor_get(v_head_5381_, 0);
lean_inc(v_decl_5397_);
lean_dec_ref_known(v_head_5381_, 1);
v___x_5398_ = lean_box(v___x_5355_);
v___f_5399_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5399_, 0, v___x_5398_);
v___x_5400_ = lean_box(0);
v___x_5401_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_5401_, 0, v_decl_5397_);
lean_closure_set(v___x_5401_, 1, v___x_5400_);
v___x_5402_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5399_, v___x_5401_, v_ctx_5349_, v_s_5350_);
v_s_5385_ = v___x_5402_;
goto v___jp_5384_;
}
else
{
lean_dec_ref_known(v_tail_5382_, 2);
lean_dec_ref_known(v_head_5381_, 1);
lean_dec(v_iniSz_5383_);
lean_dec_ref(v_ctx_5349_);
goto v___jp_5359_;
}
}
default: 
{
if (lean_obj_tag(v_tail_5382_) == 0)
{
lean_object* v_p_5403_; 
v_p_5403_ = lean_ctor_get(v_head_5381_, 0);
lean_inc_ref(v_p_5403_);
lean_dec_ref_known(v_head_5381_, 1);
if (lean_obj_tag(v_p_5403_) == 0)
{
lean_object* v_p_5404_; lean_object* v_fn_5405_; lean_object* v___x_5406_; 
lean_dec_ref_known(v___x_5358_, 4);
v_p_5404_ = lean_ctor_get(v_p_5403_, 0);
lean_inc(v_p_5404_);
lean_dec_ref_known(v_p_5403_, 1);
v_fn_5405_ = lean_ctor_get(v_p_5404_, 1);
lean_inc_ref(v_fn_5405_);
lean_dec(v_p_5404_);
v___x_5406_ = lean_apply_2(v_fn_5405_, v_ctx_5349_, v_s_5350_);
v_s_5385_ = v___x_5406_;
goto v___jp_5384_;
}
else
{
lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; 
lean_dec_ref(v_p_5403_);
lean_dec(v_iniSz_5383_);
lean_dec_ref(v_ctx_5349_);
v___x_5407_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__3));
v___x_5408_ = lean_box(0);
v___x_5409_ = l_Lean_Syntax_formatStx(v___x_5358_, v___x_5408_, v___x_5355_);
v___x_5410_ = l_Std_Format_defWidth;
v___x_5411_ = lean_unsigned_to_nat(0u);
v___x_5412_ = l_Std_Format_pretty(v___x_5409_, v___x_5410_, v___x_5411_, v___x_5411_);
v___x_5413_ = lean_string_append(v___x_5407_, v___x_5412_);
lean_dec_ref(v___x_5412_);
v___x_5414_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__4));
v___x_5415_ = lean_string_append(v___x_5413_, v___x_5414_);
v___x_5416_ = lean_box(0);
v___x_5417_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5350_, v___x_5415_, v___x_5416_, v___x_5370_);
return v___x_5417_;
}
}
else
{
lean_dec_ref_known(v_tail_5382_, 2);
lean_dec_ref_known(v_head_5381_, 1);
lean_dec(v_iniSz_5383_);
lean_dec_ref(v_ctx_5349_);
goto v___jp_5359_;
}
}
}
v___jp_5384_:
{
lean_object* v_errorMsg_5386_; lean_object* v___x_5387_; uint8_t v___x_5388_; 
v_errorMsg_5386_ = lean_ctor_get(v_s_5385_, 4);
v___x_5387_ = lean_box(0);
v___x_5388_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_errorMsg_5386_, v___x_5387_);
if (v___x_5388_ == 0)
{
lean_dec(v_iniSz_5383_);
return v_s_5385_;
}
else
{
lean_object* v___x_5389_; lean_object* v___x_5390_; uint8_t v___x_5391_; 
v___x_5389_ = l_Lean_Parser_ParserState_stackSize(v_s_5385_);
v___x_5390_ = lean_nat_add(v_iniSz_5383_, v___x_5353_);
lean_dec(v_iniSz_5383_);
v___x_5391_ = lean_nat_dec_eq(v___x_5389_, v___x_5390_);
lean_dec(v___x_5390_);
lean_dec(v___x_5389_);
if (v___x_5391_ == 0)
{
lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; 
v___x_5392_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__2));
v___x_5393_ = lean_box(0);
v___x_5394_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5385_, v___x_5392_, v___x_5393_, v___x_5388_);
return v___x_5394_;
}
else
{
return v_s_5385_;
}
}
}
}
}
else
{
lean_object* v___x_5418_; lean_object* v___x_5419_; uint8_t v___x_5420_; lean_object* v___x_5421_; 
lean_dec(v___x_5358_);
lean_dec_ref(v_ctx_5349_);
v___x_5418_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__5));
v___x_5419_ = lean_box(0);
v___x_5420_ = 1;
v___x_5421_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5350_, v___x_5418_, v___x_5419_, v___x_5420_);
return v___x_5421_;
}
v___jp_5359_:
{
lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; uint8_t v___x_5368_; lean_object* v___x_5369_; 
v___x_5360_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__0));
v___x_5361_ = lean_box(0);
v___x_5362_ = l_Lean_Syntax_formatStx(v___x_5358_, v___x_5361_, v___x_5355_);
v___x_5363_ = l_Std_Format_defWidth;
v___x_5364_ = lean_unsigned_to_nat(0u);
v___x_5365_ = l_Std_Format_pretty(v___x_5362_, v___x_5363_, v___x_5364_, v___x_5364_);
v___x_5366_ = lean_string_append(v___x_5360_, v___x_5365_);
lean_dec_ref(v___x_5365_);
v___x_5367_ = lean_box(0);
v___x_5368_ = 1;
v___x_5369_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5350_, v___x_5366_, v___x_5367_, v___x_5368_);
return v___x_5369_;
}
}
else
{
lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; 
lean_dec(v___x_5352_);
lean_dec_ref(v_ctx_5349_);
v___x_5422_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__6));
v___x_5423_ = lean_box(0);
v___x_5424_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5350_, v___x_5422_, v___x_5423_, v___x_5355_);
return v___x_5424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* v_offset_5425_, lean_object* v_ctx_5426_, lean_object* v_s_5427_){
_start:
{
lean_object* v_res_5428_; 
v_res_5428_ = l_Lean_Parser_parserOfStackFn(v_offset_5425_, v_ctx_5426_, v_s_5427_);
lean_dec(v_offset_5425_);
return v_res_5428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object* v_prec_5429_, lean_object* v_x_5430_){
_start:
{
lean_object* v_quotDepth_5431_; uint8_t v_suppressInsideQuot_5432_; lean_object* v_savedPos_x3f_5433_; lean_object* v_forbiddenTks_5434_; lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5441_; 
v_quotDepth_5431_ = lean_ctor_get(v_x_5430_, 1);
v_suppressInsideQuot_5432_ = lean_ctor_get_uint8(v_x_5430_, sizeof(void*)*4);
v_savedPos_x3f_5433_ = lean_ctor_get(v_x_5430_, 2);
v_forbiddenTks_5434_ = lean_ctor_get(v_x_5430_, 3);
v_isSharedCheck_5441_ = !lean_is_exclusive(v_x_5430_);
if (v_isSharedCheck_5441_ == 0)
{
lean_object* v_unused_5442_; 
v_unused_5442_ = lean_ctor_get(v_x_5430_, 0);
lean_dec(v_unused_5442_);
v___x_5436_ = v_x_5430_;
v_isShared_5437_ = v_isSharedCheck_5441_;
goto v_resetjp_5435_;
}
else
{
lean_inc(v_forbiddenTks_5434_);
lean_inc(v_savedPos_x3f_5433_);
lean_inc(v_quotDepth_5431_);
lean_dec(v_x_5430_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5441_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v___x_5439_; 
if (v_isShared_5437_ == 0)
{
lean_ctor_set(v___x_5436_, 0, v_prec_5429_);
v___x_5439_ = v___x_5436_;
goto v_reusejp_5438_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v_prec_5429_);
lean_ctor_set(v_reuseFailAlloc_5440_, 1, v_quotDepth_5431_);
lean_ctor_set(v_reuseFailAlloc_5440_, 2, v_savedPos_x3f_5433_);
lean_ctor_set(v_reuseFailAlloc_5440_, 3, v_forbiddenTks_5434_);
lean_ctor_set_uint8(v_reuseFailAlloc_5440_, sizeof(void*)*4, v_suppressInsideQuot_5432_);
v___x_5439_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5438_;
}
v_reusejp_5438_:
{
return v___x_5439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object* v___y_5443_){
_start:
{
lean_inc(v___y_5443_);
return v___y_5443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object* v___y_5444_){
_start:
{
lean_object* v_res_5445_; 
v_res_5445_ = l_Lean_Parser_parserOfStack___lam__1(v___y_5444_);
lean_dec(v___y_5444_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object* v___y_5446_){
_start:
{
lean_inc_ref(v___y_5446_);
return v___y_5446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object* v___y_5447_){
_start:
{
lean_object* v_res_5448_; 
v_res_5448_ = l_Lean_Parser_parserOfStack___lam__2(v___y_5447_);
lean_dec_ref(v___y_5447_);
return v_res_5448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* v_offset_5455_, lean_object* v_prec_5456_){
_start:
{
lean_object* v___f_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; 
v___f_5457_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___lam__0), 2, 1);
lean_closure_set(v___f_5457_, 0, v_prec_5456_);
v___x_5458_ = ((lean_object*)(l_Lean_Parser_parserOfStack___closed__2));
v___x_5459_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___boxed), 3, 1);
lean_closure_set(v___x_5459_, 0, v_offset_5455_);
v___x_5460_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5460_, 0, v___f_5457_);
lean_closure_set(v___x_5460_, 1, v___x_5459_);
v___x_5461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5461_, 0, v___x_5458_);
lean_ctor_set(v___x_5461_, 1, v___x_5460_);
return v___x_5461_;
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
