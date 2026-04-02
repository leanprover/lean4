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
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Data_Trie_find_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_initializing();
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_activateScoped___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
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
static lean_once_cell_t l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_builtinTokenTable;
static lean_once_cell_t l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2____boxed(lean_object*);
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
static lean_once_cell_t l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_builtinParserCategoriesRef;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "parser category `"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` has already been defined"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserAliasesRef;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserAlias2kindRef;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "parserExtension"};
static const lean_object* l_Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 242, 71, 245, 68, 132, 173, 111)}};
static const lean_object* l_Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ParserExtension_Entry_toOLeanEntry, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_ParserExtension_addEntryImpl, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "internal"};
static const lean_object* l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "parseQuotWithCurrentStage"};
static const lean_object* l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(177, 49, 45, 44, 152, 148, 209, 41)}};
static const lean_ctor_object l_Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 253, 75, 217, 201, 67, 21, 43)}};
static const lean_object* l_Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "(Lean bootstrapping) use parsers from the current stage inside quotations"};
static const lean_object* l_Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(197, 200, 93, 246, 219, 188, 139, 219)}};
static const lean_ctor_object l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(180, 175, 65, 251, 248, 238, 117, 156)}};
static const lean_object* l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object*);
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
static lean_object* _init_l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_Data_Trie_empty(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_obj_once(&l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_4_ = lean_st_mk_ref(v___x_3_);
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2____boxed(lean_object* v_a_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_();
return v_res_7_;
}
}
static lean_object* _init_l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_obj_once(&l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_13_ = lean_st_mk_ref(v___x_12_);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2____boxed(lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_();
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
v___x_22_ = lean_st_ref_set(v___x_19_, v___x_21_);
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
static lean_object* _init_l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_obj_once(&l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_obj_once(&l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_);
v___x_70_ = lean_st_mk_ref(v___x_69_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2____boxed(lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
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
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_122_; uint64_t v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(1723u);
v___x_123_ = lean_uint64_of_nat(v___x_122_);
return v___x_123_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_124_; size_t v___x_125_; size_t v___x_126_; 
v___x_124_ = ((size_t)5ULL);
v___x_125_ = ((size_t)1ULL);
v___x_126_ = lean_usize_shift_left(v___x_125_, v___x_124_);
return v___x_126_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; 
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0);
v___x_129_ = lean_usize_sub(v___x_128_, v___x_127_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(lean_object* v_x_131_, size_t v_x_132_, size_t v_x_133_, lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
lean_object* v_es_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; size_t v___x_140_; lean_object* v_j_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_es_136_ = lean_ctor_get(v_x_131_, 0);
v___x_137_ = ((size_t)5ULL);
v___x_138_ = ((size_t)1ULL);
v___x_139_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__1);
v___x_140_ = lean_usize_land(v_x_132_, v___x_139_);
v_j_141_ = lean_usize_to_nat(v___x_140_);
v___x_142_ = lean_array_get_size(v_es_136_);
v___x_143_ = lean_nat_dec_lt(v_j_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_dec(v_j_141_);
lean_dec(v_x_135_);
lean_dec(v_x_134_);
return v_x_131_;
}
else
{
lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_180_; 
lean_inc_ref(v_es_136_);
v_isSharedCheck_180_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; 
v_unused_181_ = lean_ctor_get(v_x_131_, 0);
lean_dec(v_unused_181_);
v___x_145_ = v_x_131_;
v_isShared_146_ = v_isSharedCheck_180_;
goto v_resetjp_144_;
}
else
{
lean_dec(v_x_131_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_180_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v_v_147_; lean_object* v___x_148_; lean_object* v_xs_x27_149_; lean_object* v___y_151_; 
v_v_147_ = lean_array_fget(v_es_136_, v_j_141_);
v___x_148_ = lean_box(0);
v_xs_x27_149_ = lean_array_fset(v_es_136_, v_j_141_, v___x_148_);
switch(lean_obj_tag(v_v_147_))
{
case 0:
{
lean_object* v_key_156_; lean_object* v_val_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_167_; 
v_key_156_ = lean_ctor_get(v_v_147_, 0);
v_val_157_ = lean_ctor_get(v_v_147_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_v_147_);
if (v_isSharedCheck_167_ == 0)
{
v___x_159_ = v_v_147_;
v_isShared_160_ = v_isSharedCheck_167_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_val_157_);
lean_inc(v_key_156_);
lean_dec(v_v_147_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_167_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
uint8_t v___x_161_; 
v___x_161_ = lean_name_eq(v_x_134_, v_key_156_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_del_object(v___x_159_);
v___x_162_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_156_, v_val_157_, v_x_134_, v_x_135_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
v___y_151_ = v___x_163_;
goto v___jp_150_;
}
else
{
lean_object* v___x_165_; 
lean_dec(v_val_157_);
lean_dec(v_key_156_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v_x_135_);
lean_ctor_set(v___x_159_, 0, v_x_134_);
v___x_165_ = v___x_159_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_x_134_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_x_135_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
v___y_151_ = v___x_165_;
goto v___jp_150_;
}
}
}
}
case 1:
{
lean_object* v_node_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_178_; 
v_node_168_ = lean_ctor_get(v_v_147_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_v_147_);
if (v_isSharedCheck_178_ == 0)
{
v___x_170_ = v_v_147_;
v_isShared_171_ = v_isSharedCheck_178_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_node_168_);
lean_dec(v_v_147_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_178_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
size_t v___x_172_; size_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_172_ = lean_usize_shift_right(v_x_132_, v___x_137_);
v___x_173_ = lean_usize_add(v_x_133_, v___x_138_);
v___x_174_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_node_168_, v___x_172_, v___x_173_, v_x_134_, v_x_135_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_174_);
v___x_176_ = v___x_170_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
v___y_151_ = v___x_176_;
goto v___jp_150_;
}
}
}
default: 
{
lean_object* v___x_179_; 
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_x_134_);
lean_ctor_set(v___x_179_, 1, v_x_135_);
v___y_151_ = v___x_179_;
goto v___jp_150_;
}
}
v___jp_150_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = lean_array_fset(v_xs_x27_149_, v_j_141_, v___y_151_);
lean_dec(v_j_141_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_152_);
v___x_154_ = v___x_145_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
else
{
lean_object* v_ks_182_; lean_object* v_vs_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_203_; 
v_ks_182_ = lean_ctor_get(v_x_131_, 0);
v_vs_183_ = lean_ctor_get(v_x_131_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_203_ == 0)
{
v___x_185_ = v_x_131_;
v_isShared_186_ = v_isSharedCheck_203_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_vs_183_);
lean_inc(v_ks_182_);
lean_dec(v_x_131_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_203_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_ks_182_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_vs_183_);
v___x_188_ = v_reuseFailAlloc_202_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v_newNode_189_; uint8_t v___y_191_; size_t v___x_197_; uint8_t v___x_198_; 
v_newNode_189_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v___x_188_, v_x_134_, v_x_135_);
v___x_197_ = ((size_t)7ULL);
v___x_198_ = lean_usize_dec_le(v___x_197_, v_x_133_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_199_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_189_);
v___x_200_ = lean_unsigned_to_nat(4u);
v___x_201_ = lean_nat_dec_lt(v___x_199_, v___x_200_);
lean_dec(v___x_199_);
v___y_191_ = v___x_201_;
goto v___jp_190_;
}
else
{
v___y_191_ = v___x_198_;
goto v___jp_190_;
}
v___jp_190_:
{
if (v___y_191_ == 0)
{
lean_object* v_ks_192_; lean_object* v_vs_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_ks_192_ = lean_ctor_get(v_newNode_189_, 0);
lean_inc_ref(v_ks_192_);
v_vs_193_ = lean_ctor_get(v_newNode_189_, 1);
lean_inc_ref(v_vs_193_);
lean_dec_ref(v_newNode_189_);
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__2);
v___x_196_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_x_133_, v_ks_192_, v_vs_193_, v___x_194_, v___x_195_);
lean_dec_ref(v_vs_193_);
lean_dec_ref(v_ks_192_);
return v___x_196_;
}
else
{
return v_newNode_189_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(size_t v_depth_204_, lean_object* v_keys_205_, lean_object* v_vals_206_, lean_object* v_i_207_, lean_object* v_entries_208_){
_start:
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = lean_array_get_size(v_keys_205_);
v___x_210_ = lean_nat_dec_lt(v_i_207_, v___x_209_);
if (v___x_210_ == 0)
{
lean_dec(v_i_207_);
return v_entries_208_;
}
else
{
lean_object* v_k_211_; lean_object* v_v_212_; uint64_t v___y_214_; 
v_k_211_ = lean_array_fget_borrowed(v_keys_205_, v_i_207_);
v_v_212_ = lean_array_fget_borrowed(v_vals_206_, v_i_207_);
if (lean_obj_tag(v_k_211_) == 0)
{
uint64_t v___x_225_; 
v___x_225_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_214_ = v___x_225_;
goto v___jp_213_;
}
else
{
uint64_t v_hash_226_; 
v_hash_226_ = lean_ctor_get_uint64(v_k_211_, sizeof(void*)*2);
v___y_214_ = v_hash_226_;
goto v___jp_213_;
}
v___jp_213_:
{
size_t v_h_215_; size_t v___x_216_; lean_object* v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v_h_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_h_215_ = lean_uint64_to_usize(v___y_214_);
v___x_216_ = ((size_t)5ULL);
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = ((size_t)1ULL);
v___x_219_ = lean_usize_sub(v_depth_204_, v___x_218_);
v___x_220_ = lean_usize_mul(v___x_216_, v___x_219_);
v_h_221_ = lean_usize_shift_right(v_h_215_, v___x_220_);
v___x_222_ = lean_nat_add(v_i_207_, v___x_217_);
lean_dec(v_i_207_);
lean_inc(v_v_212_);
lean_inc(v_k_211_);
v___x_223_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_entries_208_, v_h_221_, v_depth_204_, v_k_211_, v_v_212_);
v_i_207_ = v___x_222_;
v_entries_208_ = v___x_223_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_227_, lean_object* v_keys_228_, lean_object* v_vals_229_, lean_object* v_i_230_, lean_object* v_entries_231_){
_start:
{
size_t v_depth_boxed_232_; lean_object* v_res_233_; 
v_depth_boxed_232_ = lean_unbox_usize(v_depth_227_);
lean_dec(v_depth_227_);
v_res_233_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_boxed_232_, v_keys_228_, v_vals_229_, v_i_230_, v_entries_231_);
lean_dec_ref(v_vals_229_);
lean_dec_ref(v_keys_228_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
size_t v_x_558__boxed_239_; size_t v_x_559__boxed_240_; lean_object* v_res_241_; 
v_x_558__boxed_239_ = lean_unbox_usize(v_x_235_);
lean_dec(v_x_235_);
v_x_559__boxed_240_ = lean_unbox_usize(v_x_236_);
lean_dec(v_x_236_);
v_res_241_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_234_, v_x_558__boxed_239_, v_x_559__boxed_240_, v_x_237_, v_x_238_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
uint64_t v___y_246_; 
if (lean_obj_tag(v_x_243_) == 0)
{
uint64_t v___x_250_; 
v___x_250_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_246_ = v___x_250_;
goto v___jp_245_;
}
else
{
uint64_t v_hash_251_; 
v_hash_251_ = lean_ctor_get_uint64(v_x_243_, sizeof(void*)*2);
v___y_246_ = v_hash_251_;
goto v___jp_245_;
}
v___jp_245_:
{
size_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_uint64_to_usize(v___y_246_);
v___x_248_ = ((size_t)1ULL);
v___x_249_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_242_, v___x_247_, v___x_248_, v_x_243_, v_x_244_);
return v___x_249_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_252_, lean_object* v_i_253_, lean_object* v_k_254_){
_start:
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_array_get_size(v_keys_252_);
v___x_256_ = lean_nat_dec_lt(v_i_253_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec(v_i_253_);
return v___x_256_;
}
else
{
lean_object* v_k_x27_257_; uint8_t v___x_258_; 
v_k_x27_257_ = lean_array_fget_borrowed(v_keys_252_, v_i_253_);
v___x_258_ = lean_name_eq(v_k_254_, v_k_x27_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(1u);
v___x_260_ = lean_nat_add(v_i_253_, v___x_259_);
lean_dec(v_i_253_);
v_i_253_ = v___x_260_;
goto _start;
}
else
{
lean_dec(v_i_253_);
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_262_, lean_object* v_i_263_, lean_object* v_k_264_){
_start:
{
uint8_t v_res_265_; lean_object* v_r_266_; 
v_res_265_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_262_, v_i_263_, v_k_264_);
lean_dec(v_k_264_);
lean_dec_ref(v_keys_262_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(lean_object* v_x_267_, size_t v_x_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_267_) == 0)
{
lean_object* v_es_270_; lean_object* v___x_271_; size_t v___x_272_; size_t v___x_273_; size_t v___x_274_; lean_object* v_j_275_; lean_object* v___x_276_; 
v_es_270_ = lean_ctor_get(v_x_267_, 0);
v___x_271_ = lean_box(2);
v___x_272_ = ((size_t)5ULL);
v___x_273_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__1);
v___x_274_ = lean_usize_land(v_x_268_, v___x_273_);
v_j_275_ = lean_usize_to_nat(v___x_274_);
v___x_276_ = lean_array_get_borrowed(v___x_271_, v_es_270_, v_j_275_);
lean_dec(v_j_275_);
switch(lean_obj_tag(v___x_276_))
{
case 0:
{
lean_object* v_key_277_; uint8_t v___x_278_; 
v_key_277_ = lean_ctor_get(v___x_276_, 0);
v___x_278_ = lean_name_eq(v_x_269_, v_key_277_);
return v___x_278_;
}
case 1:
{
lean_object* v_node_279_; size_t v___x_280_; 
v_node_279_ = lean_ctor_get(v___x_276_, 0);
v___x_280_ = lean_usize_shift_right(v_x_268_, v___x_272_);
v_x_267_ = v_node_279_;
v_x_268_ = v___x_280_;
goto _start;
}
default: 
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
}
}
else
{
lean_object* v_ks_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_ks_283_ = lean_ctor_get(v_x_267_, 0);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_ks_283_, v___x_284_, v_x_269_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
size_t v_x_763__boxed_289_; uint8_t v_res_290_; lean_object* v_r_291_; 
v_x_763__boxed_289_ = lean_unbox_usize(v_x_287_);
lean_dec(v_x_287_);
v_res_290_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_286_, v_x_763__boxed_289_, v_x_288_);
lean_dec(v_x_288_);
lean_dec_ref(v_x_286_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
uint64_t v___y_295_; 
if (lean_obj_tag(v_x_293_) == 0)
{
uint64_t v___x_298_; 
v___x_298_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_295_ = v___x_298_;
goto v___jp_294_;
}
else
{
uint64_t v_hash_299_; 
v_hash_299_ = lean_ctor_get_uint64(v_x_293_, sizeof(void*)*2);
v___y_295_ = v_hash_299_;
goto v___jp_294_;
}
v___jp_294_:
{
size_t v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_uint64_to_usize(v___y_295_);
v___x_297_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_292_, v___x_296_, v_x_293_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg___boxed(lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_300_, v_x_301_);
lean_dec(v_x_301_);
lean_dec_ref(v_x_300_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object* v_categories_304_, lean_object* v_catName_305_, lean_object* v_initial_306_){
_start:
{
uint8_t v___x_307_; 
v___x_307_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_304_, v_catName_305_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_304_, v_catName_305_, v_initial_306_);
v___x_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; 
lean_dec_ref(v_initial_306_);
lean_dec_ref(v_categories_304_);
v___x_310_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_305_);
return v___x_310_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(lean_object* v_00_u03b2_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_312_, v_x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___boxed(lean_object* v_00_u03b2_315_, lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(v_00_u03b2_315_, v_x_316_, v_x_317_);
lean_dec(v_x_317_);
lean_dec_ref(v_x_316_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1(lean_object* v_00_u03b2_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_x_321_, v_x_322_, v_x_323_);
return v___x_324_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(lean_object* v_00_u03b2_325_, lean_object* v_x_326_, size_t v_x_327_, lean_object* v_x_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_326_, v_x_327_, v_x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_330_, lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
size_t v_x_849__boxed_334_; uint8_t v_res_335_; lean_object* v_r_336_; 
v_x_849__boxed_334_ = lean_unbox_usize(v_x_332_);
lean_dec(v_x_332_);
v_res_335_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(v_00_u03b2_330_, v_x_331_, v_x_849__boxed_334_, v_x_333_);
lean_dec(v_x_333_);
lean_dec_ref(v_x_331_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(lean_object* v_00_u03b2_337_, lean_object* v_x_338_, size_t v_x_339_, size_t v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_338_, v_x_339_, v_x_340_, v_x_341_, v_x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
size_t v_x_860__boxed_350_; size_t v_x_861__boxed_351_; lean_object* v_res_352_; 
v_x_860__boxed_350_ = lean_unbox_usize(v_x_346_);
lean_dec(v_x_346_);
v_x_861__boxed_351_ = lean_unbox_usize(v_x_347_);
lean_dec(v_x_347_);
v_res_352_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(v_00_u03b2_344_, v_x_345_, v_x_860__boxed_350_, v_x_861__boxed_351_, v_x_348_, v_x_349_);
return v_res_352_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_353_, lean_object* v_keys_354_, lean_object* v_vals_355_, lean_object* v_heq_356_, lean_object* v_i_357_, lean_object* v_k_358_){
_start:
{
uint8_t v___x_359_; 
v___x_359_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_354_, v_i_357_, v_k_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_360_, lean_object* v_keys_361_, lean_object* v_vals_362_, lean_object* v_heq_363_, lean_object* v_i_364_, lean_object* v_k_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(v_00_u03b2_360_, v_keys_361_, v_vals_362_, v_heq_363_, v_i_364_, v_k_365_);
lean_dec(v_k_365_);
lean_dec_ref(v_vals_362_);
lean_dec_ref(v_keys_361_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_368_, lean_object* v_n_369_, lean_object* v_k_370_, lean_object* v_v_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v_n_369_, v_k_370_, v_v_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_373_, size_t v_depth_374_, lean_object* v_keys_375_, lean_object* v_vals_376_, lean_object* v_heq_377_, lean_object* v_i_378_, lean_object* v_entries_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_374_, v_keys_375_, v_vals_376_, v_i_378_, v_entries_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_381_, lean_object* v_depth_382_, lean_object* v_keys_383_, lean_object* v_vals_384_, lean_object* v_heq_385_, lean_object* v_i_386_, lean_object* v_entries_387_){
_start:
{
size_t v_depth_boxed_388_; lean_object* v_res_389_; 
v_depth_boxed_388_ = lean_unbox_usize(v_depth_382_);
lean_dec(v_depth_382_);
v_res_389_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(v_00_u03b2_381_, v_depth_boxed_388_, v_keys_383_, v_vals_384_, v_heq_385_, v_i_386_, v_entries_387_);
lean_dec_ref(v_vals_384_);
lean_dec_ref(v_keys_383_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_390_, lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_x_391_, v_x_392_, v_x_393_, v_x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(lean_object* v_e_396_){
_start:
{
if (lean_obj_tag(v_e_396_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_a_398_ = lean_ctor_get(v_e_396_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_e_396_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v_e_396_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v_e_396_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = lean_mk_io_user_error(v_a_398_);
if (v_isShared_401_ == 0)
{
lean_ctor_set_tag(v___x_400_, 1);
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v_e_396_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_e_396_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v_e_396_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v_e_396_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 0);
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg___boxed(lean_object* v_e_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(lean_object* v_00_u03b1_418_, lean_object* v_e_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___boxed(lean_object* v_00_u03b1_422_, lean_object* v_e_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(v_00_u03b1_422_, v_e_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object* v_catName_429_, lean_object* v_declName_430_, uint8_t v_behavior_431_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_433_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_434_ = lean_st_ref_get(v___x_433_);
v___x_435_ = lean_obj_once(&l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_436_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_437_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_437_, 0, v_declName_430_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_436_);
lean_ctor_set_uint8(v___x_437_, sizeof(void*)*3, v_behavior_431_);
v___x_438_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(v___x_434_, v_catName_429_, v___x_437_);
v___x_439_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_438_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_448_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_st_ref_set(v___x_433_, v_a_440_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_449_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_439_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_439_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object* v_catName_457_, lean_object* v_declName_458_, lean_object* v_behavior_459_, lean_object* v_a_460_){
_start:
{
uint8_t v_behavior_boxed_461_; lean_object* v_res_462_; 
v_behavior_boxed_461_ = lean_unbox(v_behavior_459_);
v_res_462_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_457_, v_declName_458_, v_behavior_boxed_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(lean_object* v_x_463_){
_start:
{
switch(lean_obj_tag(v_x_463_))
{
case 0:
{
lean_object* v___x_464_; 
v___x_464_ = lean_unsigned_to_nat(0u);
return v___x_464_;
}
case 1:
{
lean_object* v___x_465_; 
v___x_465_ = lean_unsigned_to_nat(1u);
return v___x_465_;
}
case 2:
{
lean_object* v___x_466_; 
v___x_466_ = lean_unsigned_to_nat(2u);
return v___x_466_;
}
default: 
{
lean_object* v___x_467_; 
v___x_467_ = lean_unsigned_to_nat(3u);
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___boxed(lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(v_x_468_);
lean_dec_ref(v_x_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(lean_object* v_t_470_, lean_object* v_k_471_){
_start:
{
switch(lean_obj_tag(v_t_470_))
{
case 0:
{
lean_object* v_val_472_; lean_object* v___x_473_; 
v_val_472_ = lean_ctor_get(v_t_470_, 0);
lean_inc_ref(v_val_472_);
lean_dec_ref(v_t_470_);
v___x_473_ = lean_apply_1(v_k_471_, v_val_472_);
return v___x_473_;
}
case 1:
{
lean_object* v_val_474_; lean_object* v___x_475_; 
v_val_474_ = lean_ctor_get(v_t_470_, 0);
lean_inc(v_val_474_);
lean_dec_ref(v_t_470_);
v___x_475_ = lean_apply_1(v_k_471_, v_val_474_);
return v___x_475_;
}
case 2:
{
lean_object* v_catName_476_; lean_object* v_declName_477_; uint8_t v_behavior_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_catName_476_ = lean_ctor_get(v_t_470_, 0);
lean_inc(v_catName_476_);
v_declName_477_ = lean_ctor_get(v_t_470_, 1);
lean_inc(v_declName_477_);
v_behavior_478_ = lean_ctor_get_uint8(v_t_470_, sizeof(void*)*2);
lean_dec_ref(v_t_470_);
v___x_479_ = lean_box(v_behavior_478_);
v___x_480_ = lean_apply_3(v_k_471_, v_catName_476_, v_declName_477_, v___x_479_);
return v___x_480_;
}
default: 
{
lean_object* v_catName_481_; lean_object* v_declName_482_; lean_object* v_prio_483_; lean_object* v___x_484_; 
v_catName_481_ = lean_ctor_get(v_t_470_, 0);
lean_inc(v_catName_481_);
v_declName_482_ = lean_ctor_get(v_t_470_, 1);
lean_inc(v_declName_482_);
v_prio_483_ = lean_ctor_get(v_t_470_, 2);
lean_inc(v_prio_483_);
lean_dec_ref(v_t_470_);
v___x_484_ = lean_apply_3(v_k_471_, v_catName_481_, v_declName_482_, v_prio_483_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(lean_object* v_motive_485_, lean_object* v_ctorIdx_486_, lean_object* v_t_487_, lean_object* v_h_488_, lean_object* v_k_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_487_, v_k_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___boxed(lean_object* v_motive_491_, lean_object* v_ctorIdx_492_, lean_object* v_t_493_, lean_object* v_h_494_, lean_object* v_k_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(v_motive_491_, v_ctorIdx_492_, v_t_493_, v_h_494_, v_k_495_);
lean_dec(v_ctorIdx_492_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim___redArg(lean_object* v_t_497_, lean_object* v_token_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_497_, v_token_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim(lean_object* v_motive_500_, lean_object* v_t_501_, lean_object* v_h_502_, lean_object* v_token_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_501_, v_token_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim___redArg(lean_object* v_t_505_, lean_object* v_kind_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_505_, v_kind_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim(lean_object* v_motive_508_, lean_object* v_t_509_, lean_object* v_h_510_, lean_object* v_kind_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_509_, v_kind_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim___redArg(lean_object* v_t_513_, lean_object* v_category_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_513_, v_category_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim(lean_object* v_motive_516_, lean_object* v_t_517_, lean_object* v_h_518_, lean_object* v_category_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_517_, v_category_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim___redArg(lean_object* v_t_521_, lean_object* v_parser_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_521_, v_parser_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim(lean_object* v_motive_524_, lean_object* v_t_525_, lean_object* v_h_526_, lean_object* v_parser_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_525_, v_parser_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx(lean_object* v_x_534_){
_start:
{
switch(lean_obj_tag(v_x_534_))
{
case 0:
{
lean_object* v___x_535_; 
v___x_535_ = lean_unsigned_to_nat(0u);
return v___x_535_;
}
case 1:
{
lean_object* v___x_536_; 
v___x_536_ = lean_unsigned_to_nat(1u);
return v___x_536_;
}
case 2:
{
lean_object* v___x_537_; 
v___x_537_ = lean_unsigned_to_nat(2u);
return v___x_537_;
}
default: 
{
lean_object* v___x_538_; 
v___x_538_ = lean_unsigned_to_nat(3u);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___boxed(lean_object* v_x_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Parser_ParserExtension_Entry_ctorIdx(v_x_539_);
lean_dec_ref(v_x_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(lean_object* v_t_541_, lean_object* v_k_542_){
_start:
{
switch(lean_obj_tag(v_t_541_))
{
case 0:
{
lean_object* v_val_543_; lean_object* v___x_544_; 
v_val_543_ = lean_ctor_get(v_t_541_, 0);
lean_inc_ref(v_val_543_);
lean_dec_ref(v_t_541_);
v___x_544_ = lean_apply_1(v_k_542_, v_val_543_);
return v___x_544_;
}
case 1:
{
lean_object* v_val_545_; lean_object* v___x_546_; 
v_val_545_ = lean_ctor_get(v_t_541_, 0);
lean_inc(v_val_545_);
lean_dec_ref(v_t_541_);
v___x_546_ = lean_apply_1(v_k_542_, v_val_545_);
return v___x_546_;
}
case 2:
{
lean_object* v_catName_547_; lean_object* v_declName_548_; uint8_t v_behavior_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_catName_547_ = lean_ctor_get(v_t_541_, 0);
lean_inc(v_catName_547_);
v_declName_548_ = lean_ctor_get(v_t_541_, 1);
lean_inc(v_declName_548_);
v_behavior_549_ = lean_ctor_get_uint8(v_t_541_, sizeof(void*)*2);
lean_dec_ref(v_t_541_);
v___x_550_ = lean_box(v_behavior_549_);
v___x_551_ = lean_apply_3(v_k_542_, v_catName_547_, v_declName_548_, v___x_550_);
return v___x_551_;
}
default: 
{
lean_object* v_catName_552_; lean_object* v_declName_553_; uint8_t v_leading_554_; lean_object* v_p_555_; lean_object* v_prio_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_catName_552_ = lean_ctor_get(v_t_541_, 0);
lean_inc(v_catName_552_);
v_declName_553_ = lean_ctor_get(v_t_541_, 1);
lean_inc(v_declName_553_);
v_leading_554_ = lean_ctor_get_uint8(v_t_541_, sizeof(void*)*4);
v_p_555_ = lean_ctor_get(v_t_541_, 2);
lean_inc_ref(v_p_555_);
v_prio_556_ = lean_ctor_get(v_t_541_, 3);
lean_inc(v_prio_556_);
lean_dec_ref(v_t_541_);
v___x_557_ = lean_box(v_leading_554_);
v___x_558_ = lean_apply_5(v_k_542_, v_catName_552_, v_declName_553_, v___x_557_, v_p_555_, v_prio_556_);
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim(lean_object* v_motive_559_, lean_object* v_ctorIdx_560_, lean_object* v_t_561_, lean_object* v_h_562_, lean_object* v_k_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_561_, v_k_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___boxed(lean_object* v_motive_565_, lean_object* v_ctorIdx_566_, lean_object* v_t_567_, lean_object* v_h_568_, lean_object* v_k_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Parser_ParserExtension_Entry_ctorElim(v_motive_565_, v_ctorIdx_566_, v_t_567_, v_h_568_, v_k_569_);
lean_dec(v_ctorIdx_566_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim___redArg(lean_object* v_t_571_, lean_object* v_token_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_571_, v_token_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim(lean_object* v_motive_574_, lean_object* v_t_575_, lean_object* v_h_576_, lean_object* v_token_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_575_, v_token_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim___redArg(lean_object* v_t_579_, lean_object* v_kind_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_579_, v_kind_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim(lean_object* v_motive_582_, lean_object* v_t_583_, lean_object* v_h_584_, lean_object* v_kind_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_583_, v_kind_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim___redArg(lean_object* v_t_587_, lean_object* v_category_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_587_, v_category_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim(lean_object* v_motive_590_, lean_object* v_t_591_, lean_object* v_h_592_, lean_object* v_category_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_591_, v_category_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim___redArg(lean_object* v_t_595_, lean_object* v_parser_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_595_, v_parser_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim(lean_object* v_motive_598_, lean_object* v_t_599_, lean_object* v_h_600_, lean_object* v_parser_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_599_, v_parser_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object* v_x_607_){
_start:
{
switch(lean_obj_tag(v_x_607_))
{
case 0:
{
lean_object* v_val_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_val_608_ = lean_ctor_get(v_x_607_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v_x_607_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v_x_607_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_val_608_);
lean_dec(v_x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_val_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
case 1:
{
lean_object* v_val_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_val_616_ = lean_ctor_get(v_x_607_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_x_607_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v_x_607_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_val_616_);
lean_dec(v_x_607_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_val_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
case 2:
{
lean_object* v_catName_624_; lean_object* v_declName_625_; uint8_t v_behavior_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
v_catName_624_ = lean_ctor_get(v_x_607_, 0);
v_declName_625_ = lean_ctor_get(v_x_607_, 1);
v_behavior_626_ = lean_ctor_get_uint8(v_x_607_, sizeof(void*)*2);
v_isSharedCheck_633_ = !lean_is_exclusive(v_x_607_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v_x_607_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_declName_625_);
lean_inc(v_catName_624_);
lean_dec(v_x_607_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_catName_624_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_declName_625_);
lean_ctor_set_uint8(v_reuseFailAlloc_632_, sizeof(void*)*2, v_behavior_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
default: 
{
lean_object* v_catName_634_; lean_object* v_declName_635_; lean_object* v_prio_636_; lean_object* v___x_637_; 
v_catName_634_ = lean_ctor_get(v_x_607_, 0);
lean_inc(v_catName_634_);
v_declName_635_ = lean_ctor_get(v_x_607_, 1);
lean_inc(v_declName_635_);
v_prio_636_ = lean_ctor_get(v_x_607_, 3);
lean_inc(v_prio_636_);
lean_dec_ref(v_x_607_);
v___x_637_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_637_, 0, v_catName_634_);
lean_ctor_set(v___x_637_, 1, v_declName_635_);
lean_ctor_set(v___x_637_, 2, v_prio_636_);
return v___x_637_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_obj_once(&l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_639_ = lean_obj_once(&l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___x_638_);
lean_ctor_set(v___x_640_, 2, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_once(&l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0, &l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0_once, _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState(void){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_644_ = l_Lean_Parser_builtinTokenTable;
v___x_645_ = lean_st_ref_get(v___x_644_);
v___x_646_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_647_ = lean_st_ref_get(v___x_646_);
v___x_648_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_649_ = lean_st_ref_get(v___x_648_);
v___x_650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_650_, 0, v___x_645_);
lean_ctor_set(v___x_650_, 1, v___x_647_);
lean_ctor_set(v___x_650_, 2, v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object* v_tokens_657_, lean_object* v_tk_658_){
_start:
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = ((lean_object*)(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0));
v___x_660_ = lean_string_dec_eq(v_tk_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Data_Trie_find_x3f___redArg(v_tokens_657_, v_tk_658_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_inc_ref(v_tk_658_);
v___x_662_ = l_Lean_Data_Trie_insert___redArg(v_tokens_657_, v_tk_658_, v_tk_658_);
lean_dec_ref(v_tk_658_);
v___x_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
else
{
lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v_tk_658_);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v___x_661_, 0);
lean_dec(v_unused_671_);
v___x_665_ = v___x_661_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_dec(v___x_661_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v_tokens_657_);
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_tokens_657_);
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
else
{
lean_object* v___x_672_; 
lean_dec_ref(v_tk_658_);
lean_dec_ref(v_tokens_657_);
v___x_672_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1));
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg(lean_object* v_catName_675_){
_start:
{
lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_676_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0));
v___x_677_ = 1;
v___x_678_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_675_, v___x_677_);
v___x_679_ = lean_string_append(v___x_676_, v___x_678_);
lean_dec_ref(v___x_678_);
v___x_680_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_681_ = lean_string_append(v___x_679_, v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object* v_00_u03b1_683_, lean_object* v_catName_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object* v_categories_688_, lean_object* v_catName_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__0));
v___x_691_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__1));
v___x_692_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_690_, v___x_691_, v_categories_688_, v_catName_689_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(lean_object* v_as_694_){
_start:
{
lean_object* v___f_695_; lean_object* v___x_696_; 
v___f_695_ = ((lean_object*)(l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0));
v___x_696_ = l_List_eraseDupsBy___redArg(v___f_695_, v_as_694_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(lean_object* v_p_697_, lean_object* v_prio_698_, lean_object* v_x_699_, lean_object* v_x_700_){
_start:
{
if (lean_obj_tag(v_x_700_) == 0)
{
lean_dec(v_prio_698_);
lean_dec_ref(v_p_697_);
return v_x_699_;
}
else
{
lean_object* v_head_701_; lean_object* v_tail_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_722_; 
v_head_701_ = lean_ctor_get(v_x_700_, 0);
v_tail_702_ = lean_ctor_get(v_x_700_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_x_700_);
if (v_isSharedCheck_722_ == 0)
{
v___x_704_ = v_x_700_;
v_isShared_705_ = v_isSharedCheck_722_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_tail_702_);
lean_inc(v_head_701_);
lean_dec(v_x_700_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_722_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_leadingTable_706_; lean_object* v_leadingParsers_707_; lean_object* v_trailingTable_708_; lean_object* v_trailingParsers_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_721_; 
v_leadingTable_706_ = lean_ctor_get(v_x_699_, 0);
v_leadingParsers_707_ = lean_ctor_get(v_x_699_, 1);
v_trailingTable_708_ = lean_ctor_get(v_x_699_, 2);
v_trailingParsers_709_ = lean_ctor_get(v_x_699_, 3);
v_isSharedCheck_721_ = !lean_is_exclusive(v_x_699_);
if (v_isSharedCheck_721_ == 0)
{
v___x_711_ = v_x_699_;
v_isShared_712_ = v_isSharedCheck_721_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_trailingParsers_709_);
lean_inc(v_trailingTable_708_);
lean_inc(v_leadingParsers_707_);
lean_inc(v_leadingTable_706_);
lean_dec(v_x_699_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_721_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
lean_inc(v_prio_698_);
lean_inc_ref(v_p_697_);
if (v_isShared_705_ == 0)
{
lean_ctor_set_tag(v___x_704_, 0);
lean_ctor_set(v___x_704_, 1, v_prio_698_);
lean_ctor_set(v___x_704_, 0, v_p_697_);
v___x_714_ = v___x_704_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_p_697_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_prio_698_);
v___x_714_ = v_reuseFailAlloc_720_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = l_Lean_Parser_TokenMap_insert___redArg(v_leadingTable_706_, v_head_701_, v___x_714_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_715_);
v___x_717_ = v___x_711_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_leadingParsers_707_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_trailingTable_708_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_trailingParsers_709_);
v___x_717_ = v_reuseFailAlloc_719_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
v_x_699_ = v___x_717_;
v_x_700_ = v_tail_702_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_723_, lean_object* v_vals_724_, lean_object* v_i_725_, lean_object* v_k_726_){
_start:
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = lean_array_get_size(v_keys_723_);
v___x_728_ = lean_nat_dec_lt(v_i_725_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec(v_i_725_);
v___x_729_ = lean_box(0);
return v___x_729_;
}
else
{
lean_object* v_k_x27_730_; uint8_t v___x_731_; 
v_k_x27_730_ = lean_array_fget_borrowed(v_keys_723_, v_i_725_);
v___x_731_ = lean_name_eq(v_k_726_, v_k_x27_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_add(v_i_725_, v___x_732_);
lean_dec(v_i_725_);
v_i_725_ = v___x_733_;
goto _start;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_array_fget_borrowed(v_vals_724_, v_i_725_);
lean_dec(v_i_725_);
lean_inc(v___x_735_);
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_737_, lean_object* v_vals_738_, lean_object* v_i_739_, lean_object* v_k_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_737_, v_vals_738_, v_i_739_, v_k_740_);
lean_dec(v_k_740_);
lean_dec_ref(v_vals_738_);
lean_dec_ref(v_keys_737_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(lean_object* v_x_742_, size_t v_x_743_, lean_object* v_x_744_){
_start:
{
if (lean_obj_tag(v_x_742_) == 0)
{
lean_object* v_es_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_766_; 
v_es_745_ = lean_ctor_get(v_x_742_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v_x_742_);
if (v_isSharedCheck_766_ == 0)
{
v___x_747_ = v_x_742_;
v_isShared_748_ = v_isSharedCheck_766_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_es_745_);
lean_dec(v_x_742_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_766_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; size_t v___x_750_; size_t v___x_751_; size_t v___x_752_; lean_object* v_j_753_; lean_object* v___x_754_; 
v___x_749_ = lean_box(2);
v___x_750_ = ((size_t)5ULL);
v___x_751_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__1);
v___x_752_ = lean_usize_land(v_x_743_, v___x_751_);
v_j_753_ = lean_usize_to_nat(v___x_752_);
v___x_754_ = lean_array_get(v___x_749_, v_es_745_, v_j_753_);
lean_dec(v_j_753_);
lean_dec_ref(v_es_745_);
switch(lean_obj_tag(v___x_754_))
{
case 0:
{
lean_object* v_key_755_; lean_object* v_val_756_; uint8_t v___x_757_; 
v_key_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_key_755_);
v_val_756_ = lean_ctor_get(v___x_754_, 1);
lean_inc(v_val_756_);
lean_dec_ref(v___x_754_);
v___x_757_ = lean_name_eq(v_x_744_, v_key_755_);
lean_dec(v_key_755_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_dec(v_val_756_);
lean_del_object(v___x_747_);
v___x_758_ = lean_box(0);
return v___x_758_;
}
else
{
lean_object* v___x_760_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 1);
lean_ctor_set(v___x_747_, 0, v_val_756_);
v___x_760_ = v___x_747_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_val_756_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
case 1:
{
lean_object* v_node_762_; size_t v___x_763_; 
lean_del_object(v___x_747_);
v_node_762_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_node_762_);
lean_dec_ref(v___x_754_);
v___x_763_ = lean_usize_shift_right(v_x_743_, v___x_750_);
v_x_742_ = v_node_762_;
v_x_743_ = v___x_763_;
goto _start;
}
default: 
{
lean_object* v___x_765_; 
lean_del_object(v___x_747_);
v___x_765_ = lean_box(0);
return v___x_765_;
}
}
}
}
else
{
lean_object* v_ks_767_; lean_object* v_vs_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_ks_767_ = lean_ctor_get(v_x_742_, 0);
lean_inc_ref(v_ks_767_);
v_vs_768_ = lean_ctor_get(v_x_742_, 1);
lean_inc_ref(v_vs_768_);
lean_dec_ref(v_x_742_);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_ks_767_, v_vs_768_, v___x_769_, v_x_744_);
lean_dec_ref(v_vs_768_);
lean_dec_ref(v_ks_767_);
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg___boxed(lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
size_t v_x_503__boxed_774_; lean_object* v_res_775_; 
v_x_503__boxed_774_ = lean_unbox_usize(v_x_772_);
lean_dec(v_x_772_);
v_res_775_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_771_, v_x_503__boxed_774_, v_x_773_);
lean_dec(v_x_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
uint64_t v___y_779_; 
if (lean_obj_tag(v_x_777_) == 0)
{
uint64_t v___x_782_; 
v___x_782_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_779_ = v___x_782_;
goto v___jp_778_;
}
else
{
uint64_t v_hash_783_; 
v_hash_783_ = lean_ctor_get_uint64(v_x_777_, sizeof(void*)*2);
v___y_779_ = v_hash_783_;
goto v___jp_778_;
}
v___jp_778_:
{
size_t v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_uint64_to_usize(v___y_779_);
v___x_781_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_776_, v___x_780_, v_x_777_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg___boxed(lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_784_, v_x_785_);
lean_dec(v_x_785_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
if (lean_obj_tag(v_a_787_) == 0)
{
lean_object* v___x_789_; 
v___x_789_ = l_List_reverse___redArg(v_a_788_);
return v___x_789_;
}
else
{
lean_object* v_head_790_; lean_object* v_tail_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_801_; 
v_head_790_ = lean_ctor_get(v_a_787_, 0);
v_tail_791_ = lean_ctor_get(v_a_787_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_a_787_);
if (v_isSharedCheck_801_ == 0)
{
v___x_793_ = v_a_787_;
v_isShared_794_ = v_isSharedCheck_801_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_tail_791_);
lean_inc(v_head_790_);
lean_dec(v_a_787_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_801_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_795_ = lean_box(0);
v___x_796_ = l_Lean_Name_str___override(v___x_795_, v_head_790_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 1, v_a_788_);
lean_ctor_set(v___x_793_, 0, v___x_796_);
v___x_798_ = v___x_793_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_a_788_);
v___x_798_ = v_reuseFailAlloc_800_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
v_a_787_ = v_tail_791_;
v_a_788_ = v___x_798_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object* v_categories_802_, lean_object* v_catName_803_, lean_object* v_declName_804_, lean_object* v_p_805_, lean_object* v_prio_806_){
_start:
{
lean_object* v___x_807_; 
lean_inc_ref(v_categories_802_);
v___x_807_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_802_, v_catName_803_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v___x_808_; 
lean_dec(v_prio_806_);
lean_dec_ref(v_p_805_);
lean_dec(v_declName_804_);
lean_dec_ref(v_categories_802_);
v___x_808_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_803_);
return v___x_808_;
}
else
{
lean_object* v_val_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_855_; 
v_val_809_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_855_ == 0)
{
v___x_811_ = v___x_807_;
v_isShared_812_ = v_isSharedCheck_855_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_val_809_);
lean_dec(v___x_807_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_855_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_info_813_; lean_object* v_declName_814_; lean_object* v_kinds_815_; lean_object* v_tables_816_; uint8_t v_behavior_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_854_; 
v_info_813_ = lean_ctor_get(v_p_805_, 0);
v_declName_814_ = lean_ctor_get(v_val_809_, 0);
v_kinds_815_ = lean_ctor_get(v_val_809_, 1);
v_tables_816_ = lean_ctor_get(v_val_809_, 2);
v_behavior_817_ = lean_ctor_get_uint8(v_val_809_, sizeof(void*)*3);
v_isSharedCheck_854_ = !lean_is_exclusive(v_val_809_);
if (v_isSharedCheck_854_ == 0)
{
v___x_819_ = v_val_809_;
v_isShared_820_ = v_isSharedCheck_854_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_tables_816_);
lean_inc(v_kinds_815_);
lean_inc(v_declName_814_);
lean_dec(v_val_809_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_854_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v_firstTokens_821_; lean_object* v_kinds_822_; lean_object* v_tks_824_; 
v_firstTokens_821_ = lean_ctor_get(v_info_813_, 2);
v_kinds_822_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_815_, v_declName_804_);
switch(lean_obj_tag(v_firstTokens_821_))
{
case 2:
{
lean_object* v_a_836_; 
v_a_836_ = lean_ctor_get(v_firstTokens_821_, 0);
lean_inc(v_a_836_);
v_tks_824_ = v_a_836_;
goto v___jp_823_;
}
case 3:
{
lean_object* v_a_837_; 
v_a_837_ = lean_ctor_get(v_firstTokens_821_, 0);
lean_inc(v_a_837_);
v_tks_824_ = v_a_837_;
goto v___jp_823_;
}
default: 
{
lean_object* v_leadingTable_838_; lean_object* v_leadingParsers_839_; lean_object* v_trailingTable_840_; lean_object* v_trailingParsers_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_853_; 
lean_del_object(v___x_819_);
lean_del_object(v___x_811_);
v_leadingTable_838_ = lean_ctor_get(v_tables_816_, 0);
v_leadingParsers_839_ = lean_ctor_get(v_tables_816_, 1);
v_trailingTable_840_ = lean_ctor_get(v_tables_816_, 2);
v_trailingParsers_841_ = lean_ctor_get(v_tables_816_, 3);
v_isSharedCheck_853_ = !lean_is_exclusive(v_tables_816_);
if (v_isSharedCheck_853_ == 0)
{
v___x_843_ = v_tables_816_;
v_isShared_844_ = v_isSharedCheck_853_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_trailingParsers_841_);
lean_inc(v_trailingTable_840_);
lean_inc(v_leadingParsers_839_);
lean_inc(v_leadingTable_838_);
lean_dec(v_tables_816_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_853_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v_tables_848_; 
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_p_805_);
lean_ctor_set(v___x_845_, 1, v_prio_806_);
v___x_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v_leadingParsers_839_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v___x_846_);
v_tables_848_ = v___x_843_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_leadingTable_838_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_trailingTable_840_);
lean_ctor_set(v_reuseFailAlloc_852_, 3, v_trailingParsers_841_);
v_tables_848_ = v_reuseFailAlloc_852_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_849_, 0, v_declName_814_);
lean_ctor_set(v___x_849_, 1, v_kinds_822_);
lean_ctor_set(v___x_849_, 2, v_tables_848_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*3, v_behavior_817_);
v___x_850_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_802_, v_catName_803_, v___x_849_);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
}
}
v___jp_823_:
{
lean_object* v___x_825_; lean_object* v_tks_826_; lean_object* v___x_827_; lean_object* v_tables_828_; lean_object* v___x_830_; 
v___x_825_ = lean_box(0);
v_tks_826_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_824_, v___x_825_);
v___x_827_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_826_);
v_tables_828_ = l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(v_p_805_, v_prio_806_, v_tables_816_, v___x_827_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 2, v_tables_828_);
lean_ctor_set(v___x_819_, 1, v_kinds_822_);
v___x_830_ = v___x_819_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_declName_814_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_kinds_822_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_tables_828_);
lean_ctor_set_uint8(v_reuseFailAlloc_835_, sizeof(void*)*3, v_behavior_817_);
v___x_830_ = v_reuseFailAlloc_835_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_831_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_802_, v_catName_803_, v___x_830_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_831_);
v___x_833_ = v___x_811_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(lean_object* v_00_u03b2_856_, lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_857_, v_x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___boxed(lean_object* v_00_u03b2_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(v_00_u03b2_860_, v_x_861_, v_x_862_);
lean_dec(v_x_862_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_object* v_00_u03b2_864_, lean_object* v_x_865_, size_t v_x_866_, lean_object* v_x_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_865_, v_x_866_, v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___boxed(lean_object* v_00_u03b2_869_, lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
size_t v_x_689__boxed_873_; lean_object* v_res_874_; 
v_x_689__boxed_873_ = lean_unbox_usize(v_x_871_);
lean_dec(v_x_871_);
v_res_874_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(v_00_u03b2_869_, v_x_870_, v_x_689__boxed_873_, v_x_872_);
lean_dec(v_x_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_875_, lean_object* v_keys_876_, lean_object* v_vals_877_, lean_object* v_heq_878_, lean_object* v_i_879_, lean_object* v_k_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_876_, v_vals_877_, v_i_879_, v_k_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_882_, lean_object* v_keys_883_, lean_object* v_vals_884_, lean_object* v_heq_885_, lean_object* v_i_886_, lean_object* v_k_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(v_00_u03b2_882_, v_keys_883_, v_vals_884_, v_heq_885_, v_i_886_, v_k_887_);
lean_dec(v_k_887_);
lean_dec_ref(v_vals_884_);
lean_dec_ref(v_keys_883_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(lean_object* v_p_889_, lean_object* v_prio_890_, lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
if (lean_obj_tag(v_x_892_) == 0)
{
lean_dec(v_prio_890_);
lean_dec_ref(v_p_889_);
return v_x_891_;
}
else
{
lean_object* v_head_893_; lean_object* v_tail_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_914_; 
v_head_893_ = lean_ctor_get(v_x_892_, 0);
v_tail_894_ = lean_ctor_get(v_x_892_, 1);
v_isSharedCheck_914_ = !lean_is_exclusive(v_x_892_);
if (v_isSharedCheck_914_ == 0)
{
v___x_896_ = v_x_892_;
v_isShared_897_ = v_isSharedCheck_914_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_tail_894_);
lean_inc(v_head_893_);
lean_dec(v_x_892_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_914_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_leadingTable_898_; lean_object* v_leadingParsers_899_; lean_object* v_trailingTable_900_; lean_object* v_trailingParsers_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_913_; 
v_leadingTable_898_ = lean_ctor_get(v_x_891_, 0);
v_leadingParsers_899_ = lean_ctor_get(v_x_891_, 1);
v_trailingTable_900_ = lean_ctor_get(v_x_891_, 2);
v_trailingParsers_901_ = lean_ctor_get(v_x_891_, 3);
v_isSharedCheck_913_ = !lean_is_exclusive(v_x_891_);
if (v_isSharedCheck_913_ == 0)
{
v___x_903_ = v_x_891_;
v_isShared_904_ = v_isSharedCheck_913_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_trailingParsers_901_);
lean_inc(v_trailingTable_900_);
lean_inc(v_leadingParsers_899_);
lean_inc(v_leadingTable_898_);
lean_dec(v_x_891_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_913_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
lean_inc(v_prio_890_);
lean_inc_ref(v_p_889_);
if (v_isShared_897_ == 0)
{
lean_ctor_set_tag(v___x_896_, 0);
lean_ctor_set(v___x_896_, 1, v_prio_890_);
lean_ctor_set(v___x_896_, 0, v_p_889_);
v___x_906_ = v___x_896_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_p_889_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_prio_890_);
v___x_906_ = v_reuseFailAlloc_912_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = l_Lean_Parser_TokenMap_insert___redArg(v_trailingTable_900_, v_head_893_, v___x_906_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 2, v___x_907_);
v___x_909_ = v___x_903_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_leadingTable_898_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_leadingParsers_899_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v_trailingParsers_901_);
v___x_909_ = v_reuseFailAlloc_911_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
v_x_891_ = v___x_909_;
v_x_892_ = v_tail_894_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object* v_tables_915_, lean_object* v_p_916_, lean_object* v_prio_917_){
_start:
{
lean_object* v_tks_919_; lean_object* v_info_924_; lean_object* v_firstTokens_925_; 
v_info_924_ = lean_ctor_get(v_p_916_, 0);
v_firstTokens_925_ = lean_ctor_get(v_info_924_, 2);
switch(lean_obj_tag(v_firstTokens_925_))
{
case 2:
{
lean_object* v_a_926_; 
v_a_926_ = lean_ctor_get(v_firstTokens_925_, 0);
lean_inc(v_a_926_);
v_tks_919_ = v_a_926_;
goto v___jp_918_;
}
case 3:
{
lean_object* v_a_927_; 
v_a_927_ = lean_ctor_get(v_firstTokens_925_, 0);
lean_inc(v_a_927_);
v_tks_919_ = v_a_927_;
goto v___jp_918_;
}
default: 
{
lean_object* v_leadingTable_928_; lean_object* v_leadingParsers_929_; lean_object* v_trailingTable_930_; lean_object* v_trailingParsers_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_940_; 
v_leadingTable_928_ = lean_ctor_get(v_tables_915_, 0);
v_leadingParsers_929_ = lean_ctor_get(v_tables_915_, 1);
v_trailingTable_930_ = lean_ctor_get(v_tables_915_, 2);
v_trailingParsers_931_ = lean_ctor_get(v_tables_915_, 3);
v_isSharedCheck_940_ = !lean_is_exclusive(v_tables_915_);
if (v_isSharedCheck_940_ == 0)
{
v___x_933_ = v_tables_915_;
v_isShared_934_ = v_isSharedCheck_940_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_trailingParsers_931_);
lean_inc(v_trailingTable_930_);
lean_inc(v_leadingParsers_929_);
lean_inc(v_leadingTable_928_);
lean_dec(v_tables_915_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_940_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v_p_916_);
lean_ctor_set(v___x_935_, 1, v_prio_917_);
v___x_936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v_trailingParsers_931_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 3, v___x_936_);
v___x_938_ = v___x_933_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_leadingTable_928_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_leadingParsers_929_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_trailingTable_930_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v___x_936_);
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
v___jp_918_:
{
lean_object* v___x_920_; lean_object* v_tks_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_920_ = lean_box(0);
v_tks_921_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_919_, v___x_920_);
v___x_922_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_921_);
v___x_923_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(v_p_916_, v_prio_917_, v_tables_915_, v___x_922_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object* v_categories_941_, lean_object* v_catName_942_, lean_object* v_declName_943_, lean_object* v_p_944_, lean_object* v_prio_945_){
_start:
{
lean_object* v___x_946_; 
lean_inc_ref(v_categories_941_);
v___x_946_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_941_, v_catName_942_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v___x_947_; 
lean_dec(v_prio_945_);
lean_dec_ref(v_p_944_);
lean_dec(v_declName_943_);
lean_dec_ref(v_categories_941_);
v___x_947_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_942_);
return v___x_947_;
}
else
{
lean_object* v_val_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_969_; 
v_val_948_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_969_ == 0)
{
v___x_950_ = v___x_946_;
v_isShared_951_ = v_isSharedCheck_969_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_val_948_);
lean_dec(v___x_946_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_969_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_declName_952_; lean_object* v_kinds_953_; lean_object* v_tables_954_; uint8_t v_behavior_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_968_; 
v_declName_952_ = lean_ctor_get(v_val_948_, 0);
v_kinds_953_ = lean_ctor_get(v_val_948_, 1);
v_tables_954_ = lean_ctor_get(v_val_948_, 2);
v_behavior_955_ = lean_ctor_get_uint8(v_val_948_, sizeof(void*)*3);
v_isSharedCheck_968_ = !lean_is_exclusive(v_val_948_);
if (v_isSharedCheck_968_ == 0)
{
v___x_957_ = v_val_948_;
v_isShared_958_ = v_isSharedCheck_968_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_tables_954_);
lean_inc(v_kinds_953_);
lean_inc(v_declName_952_);
lean_dec(v_val_948_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_968_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_kinds_959_; lean_object* v_tables_960_; lean_object* v___x_962_; 
v_kinds_959_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_953_, v_declName_943_);
v_tables_960_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(v_tables_954_, v_p_944_, v_prio_945_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 2, v_tables_960_);
lean_ctor_set(v___x_957_, 1, v_kinds_959_);
v___x_962_ = v___x_957_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_declName_952_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_kinds_959_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_tables_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*3, v_behavior_955_);
v___x_962_ = v_reuseFailAlloc_967_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_941_, v_catName_942_, v___x_962_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_963_);
v___x_965_ = v___x_950_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object* v_categories_970_, lean_object* v_catName_971_, lean_object* v_declName_972_, uint8_t v_leading_973_, lean_object* v_p_974_, lean_object* v_prio_975_){
_start:
{
if (v_leading_973_ == 0)
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_Parser_addTrailingParser(v_categories_970_, v_catName_971_, v_declName_972_, v_p_974_, v_prio_975_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_Parser_addLeadingParser(v_categories_970_, v_catName_971_, v_declName_972_, v_p_974_, v_prio_975_);
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object* v_categories_978_, lean_object* v_catName_979_, lean_object* v_declName_980_, lean_object* v_leading_981_, lean_object* v_p_982_, lean_object* v_prio_983_){
_start:
{
uint8_t v_leading_boxed_984_; lean_object* v_res_985_; 
v_leading_boxed_984_ = lean_unbox(v_leading_981_);
v_res_985_ = l_Lean_Parser_addParser(v_categories_978_, v_catName_979_, v_declName_980_, v_leading_boxed_984_, v_p_982_, v_prio_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
if (lean_obj_tag(v_x_987_) == 0)
{
lean_object* v___x_988_; 
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v_x_986_);
return v___x_988_;
}
else
{
lean_object* v_head_989_; lean_object* v_tail_990_; lean_object* v___x_991_; 
v_head_989_ = lean_ctor_get(v_x_987_, 0);
lean_inc(v_head_989_);
v_tail_990_ = lean_ctor_get(v_x_987_, 1);
lean_inc(v_tail_990_);
lean_dec_ref(v_x_987_);
v___x_991_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_x_986_, v_head_989_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_dec(v_tail_990_);
return v___x_991_;
}
else
{
lean_object* v_a_992_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref(v___x_991_);
v_x_986_ = v_a_992_;
v_x_987_ = v_tail_990_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object* v_tokenTable_994_, lean_object* v_info_995_){
_start:
{
lean_object* v_collectTokens_996_; lean_object* v___x_997_; lean_object* v_newTokens_998_; lean_object* v___x_999_; 
v_collectTokens_996_ = lean_ctor_get(v_info_995_, 0);
lean_inc_ref(v_collectTokens_996_);
lean_dec_ref(v_info_995_);
v___x_997_ = lean_box(0);
v_newTokens_998_ = lean_apply_1(v_collectTokens_996_, v___x_997_);
v___x_999_ = l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(v_tokenTable_994_, v_newTokens_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object* v_info_1002_, lean_object* v_declName_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1005_ = l_Lean_Parser_builtinTokenTable;
v___x_1006_ = lean_obj_once(&l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_1007_ = lean_st_ref_swap(v___x_1005_, v___x_1006_);
v___x_1008_ = l_Lean_Parser_addParserTokens(v___x_1007_, v_info_1002_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1025_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1025_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1025_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1013_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0));
v___x_1014_ = l_Lean_privateToUserName(v_declName_1003_);
v___x_1015_ = 1;
v___x_1016_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1014_, v___x_1015_);
v___x_1017_ = lean_string_append(v___x_1013_, v___x_1016_);
lean_dec_ref(v___x_1016_);
v___x_1018_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_1019_ = lean_string_append(v___x_1017_, v___x_1018_);
v___x_1020_ = lean_string_append(v___x_1019_, v_a_1009_);
lean_dec(v_a_1009_);
v___x_1021_ = lean_mk_io_user_error(v___x_1020_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set_tag(v___x_1011_, 1);
lean_ctor_set(v___x_1011_, 0, v___x_1021_);
v___x_1023_ = v___x_1011_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_declName_1003_);
v_a_1026_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1028_ = v___x_1008_;
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1008_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_st_ref_set(v___x_1005_, v_a_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1030_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___boxed(lean_object* v_info_1035_, lean_object* v_declName_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_1035_, v_declName_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(lean_object* v_msg_1039_){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1041_ = lean_panic_fn_borrowed(v___x_1040_, v_msg_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object* v_s_1045_, lean_object* v_e_1046_){
_start:
{
switch(lean_obj_tag(v_e_1046_))
{
case 0:
{
lean_object* v_val_1047_; lean_object* v_tokens_1048_; lean_object* v_kinds_1049_; lean_object* v_categories_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1068_; 
v_val_1047_ = lean_ctor_get(v_e_1046_, 0);
lean_inc_ref(v_val_1047_);
lean_dec_ref(v_e_1046_);
v_tokens_1048_ = lean_ctor_get(v_s_1045_, 0);
v_kinds_1049_ = lean_ctor_get(v_s_1045_, 1);
v_categories_1050_ = lean_ctor_get(v_s_1045_, 2);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_s_1045_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1052_ = v_s_1045_;
v_isShared_1053_ = v_isSharedCheck_1068_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_categories_1050_);
lean_inc(v_kinds_1049_);
lean_inc(v_tokens_1048_);
lean_dec(v_s_1045_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1068_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; 
v___x_1054_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_1048_, v_val_1047_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_del_object(v___x_1052_);
lean_dec_ref(v_categories_1050_);
lean_dec_ref(v_kinds_1049_);
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref(v___x_1054_);
v___x_1056_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1057_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1058_ = lean_unsigned_to_nat(163u);
v___x_1059_ = lean_unsigned_to_nat(26u);
v___x_1060_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1061_ = lean_string_append(v___x_1060_, v_a_1055_);
lean_dec(v_a_1055_);
v___x_1062_ = l_mkPanicMessageWithDecl(v___x_1056_, v___x_1057_, v___x_1058_, v___x_1059_, v___x_1061_);
lean_dec_ref(v___x_1061_);
v___x_1063_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1062_);
return v___x_1063_;
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; 
v_a_1064_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1064_);
lean_dec_ref(v___x_1054_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v_a_1064_);
v___x_1066_ = v___x_1052_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1064_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_kinds_1049_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_categories_1050_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
case 1:
{
lean_object* v_val_1069_; lean_object* v_tokens_1070_; lean_object* v_kinds_1071_; lean_object* v_categories_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1080_; 
v_val_1069_ = lean_ctor_get(v_e_1046_, 0);
lean_inc(v_val_1069_);
lean_dec_ref(v_e_1046_);
v_tokens_1070_ = lean_ctor_get(v_s_1045_, 0);
v_kinds_1071_ = lean_ctor_get(v_s_1045_, 1);
v_categories_1072_ = lean_ctor_get(v_s_1045_, 2);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_s_1045_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1074_ = v_s_1045_;
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_categories_1072_);
lean_inc(v_kinds_1071_);
lean_inc(v_tokens_1070_);
lean_dec(v_s_1045_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_1071_, v_val_1069_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v___x_1076_);
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_tokens_1070_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_categories_1072_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
case 2:
{
lean_object* v_catName_1081_; lean_object* v_declName_1082_; uint8_t v_behavior_1083_; lean_object* v_tokens_1084_; lean_object* v_kinds_1085_; lean_object* v_categories_1086_; uint8_t v___x_1087_; 
v_catName_1081_ = lean_ctor_get(v_e_1046_, 0);
lean_inc(v_catName_1081_);
v_declName_1082_ = lean_ctor_get(v_e_1046_, 1);
lean_inc(v_declName_1082_);
v_behavior_1083_ = lean_ctor_get_uint8(v_e_1046_, sizeof(void*)*2);
lean_dec_ref(v_e_1046_);
v_tokens_1084_ = lean_ctor_get(v_s_1045_, 0);
v_kinds_1085_ = lean_ctor_get(v_s_1045_, 1);
v_categories_1086_ = lean_ctor_get(v_s_1045_, 2);
v___x_1087_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_1086_, v_catName_1081_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1098_; 
lean_inc_ref(v_categories_1086_);
lean_inc_ref(v_kinds_1085_);
lean_inc_ref(v_tokens_1084_);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_s_1045_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; lean_object* v_unused_1100_; lean_object* v_unused_1101_; 
v_unused_1099_ = lean_ctor_get(v_s_1045_, 2);
lean_dec(v_unused_1099_);
v_unused_1100_ = lean_ctor_get(v_s_1045_, 1);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_s_1045_, 0);
lean_dec(v_unused_1101_);
v___x_1089_ = v_s_1045_;
v_isShared_1090_ = v_isSharedCheck_1098_;
goto v_resetjp_1088_;
}
else
{
lean_dec(v_s_1045_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1098_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1091_ = lean_obj_once(&l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_1092_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_1093_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1093_, 0, v_declName_1082_);
lean_ctor_set(v___x_1093_, 1, v___x_1091_);
lean_ctor_set(v___x_1093_, 2, v___x_1092_);
lean_ctor_set_uint8(v___x_1093_, sizeof(void*)*3, v_behavior_1083_);
v___x_1094_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_1086_, v_catName_1081_, v___x_1093_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 2, v___x_1094_);
v___x_1096_ = v___x_1089_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_tokens_1084_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_kinds_1085_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
lean_dec(v_declName_1082_);
lean_dec(v_catName_1081_);
return v_s_1045_;
}
}
default: 
{
lean_object* v_catName_1102_; lean_object* v_declName_1103_; uint8_t v_leading_1104_; lean_object* v_p_1105_; lean_object* v_prio_1106_; lean_object* v_tokens_1107_; lean_object* v_kinds_1108_; lean_object* v_categories_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1127_; 
v_catName_1102_ = lean_ctor_get(v_e_1046_, 0);
lean_inc(v_catName_1102_);
v_declName_1103_ = lean_ctor_get(v_e_1046_, 1);
lean_inc(v_declName_1103_);
v_leading_1104_ = lean_ctor_get_uint8(v_e_1046_, sizeof(void*)*4);
v_p_1105_ = lean_ctor_get(v_e_1046_, 2);
lean_inc_ref(v_p_1105_);
v_prio_1106_ = lean_ctor_get(v_e_1046_, 3);
lean_inc(v_prio_1106_);
lean_dec_ref(v_e_1046_);
v_tokens_1107_ = lean_ctor_get(v_s_1045_, 0);
v_kinds_1108_ = lean_ctor_get(v_s_1045_, 1);
v_categories_1109_ = lean_ctor_get(v_s_1045_, 2);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_s_1045_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1111_ = v_s_1045_;
v_isShared_1112_ = v_isSharedCheck_1127_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_categories_1109_);
lean_inc(v_kinds_1108_);
lean_inc(v_tokens_1107_);
lean_dec(v_s_1045_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1127_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_Parser_addParser(v_categories_1109_, v_catName_1102_, v_declName_1103_, v_leading_1104_, v_p_1105_, v_prio_1106_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_del_object(v___x_1111_);
lean_dec_ref(v_kinds_1108_);
lean_dec_ref(v_tokens_1107_);
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref(v___x_1113_);
v___x_1115_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1116_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1117_ = lean_unsigned_to_nat(173u);
v___x_1118_ = lean_unsigned_to_nat(30u);
v___x_1119_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1120_ = lean_string_append(v___x_1119_, v_a_1114_);
lean_dec(v_a_1114_);
v___x_1121_ = l_mkPanicMessageWithDecl(v___x_1115_, v___x_1116_, v___x_1117_, v___x_1118_, v___x_1120_);
lean_dec_ref(v___x_1120_);
v___x_1122_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1121_);
return v___x_1122_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; 
v_a_1123_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1123_);
lean_dec_ref(v___x_1113_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 2, v_a_1123_);
v___x_1125_ = v___x_1111_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_tokens_1107_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_kinds_1108_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_a_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg(lean_object* v_x_1128_){
_start:
{
switch(lean_obj_tag(v_x_1128_))
{
case 0:
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_unsigned_to_nat(0u);
return v___x_1129_;
}
case 1:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_unsigned_to_nat(1u);
return v___x_1130_;
}
default: 
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_unsigned_to_nat(2u);
return v___x_1131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___redArg___boxed(lean_object* v_x_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Parser_AliasValue_ctorIdx___redArg(v_x_1132_);
lean_dec_ref(v_x_1132_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx(lean_object* v_00_u03b1_1134_, lean_object* v_x_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Parser_AliasValue_ctorIdx___redArg(v_x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___boxed(lean_object* v_00_u03b1_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_Parser_AliasValue_ctorIdx(v_00_u03b1_1137_, v_x_1138_);
lean_dec_ref(v_x_1138_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___redArg(lean_object* v_t_1140_, lean_object* v_k_1141_){
_start:
{
lean_object* v_p_1142_; lean_object* v___x_1143_; 
v_p_1142_ = lean_ctor_get(v_t_1140_, 0);
lean_inc(v_p_1142_);
lean_dec_ref(v_t_1140_);
v___x_1143_ = lean_apply_1(v_k_1141_, v_p_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim(lean_object* v_00_u03b1_1144_, lean_object* v_motive_1145_, lean_object* v_ctorIdx_1146_, lean_object* v_t_1147_, lean_object* v_h_1148_, lean_object* v_k_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1147_, v_k_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___boxed(lean_object* v_00_u03b1_1151_, lean_object* v_motive_1152_, lean_object* v_ctorIdx_1153_, lean_object* v_t_1154_, lean_object* v_h_1155_, lean_object* v_k_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Parser_AliasValue_ctorElim(v_00_u03b1_1151_, v_motive_1152_, v_ctorIdx_1153_, v_t_1154_, v_h_1155_, v_k_1156_);
lean_dec(v_ctorIdx_1153_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim___redArg(lean_object* v_t_1158_, lean_object* v_const_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1158_, v_const_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim(lean_object* v_00_u03b1_1161_, lean_object* v_motive_1162_, lean_object* v_t_1163_, lean_object* v_h_1164_, lean_object* v_const_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1163_, v_const_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim___redArg(lean_object* v_t_1167_, lean_object* v_unary_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1167_, v_unary_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim(lean_object* v_00_u03b1_1170_, lean_object* v_motive_1171_, lean_object* v_t_1172_, lean_object* v_h_1173_, lean_object* v_unary_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1172_, v_unary_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim___redArg(lean_object* v_t_1176_, lean_object* v_binary_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1176_, v_binary_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim(lean_object* v_00_u03b1_1179_, lean_object* v_motive_1180_, lean_object* v_t_1181_, lean_object* v_h_1182_, lean_object* v_binary_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1181_, v_binary_1183_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_Parser_registerAliasCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__0));
v___x_1187_ = lean_mk_io_user_error(v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg(lean_object* v_mapRef_1190_, lean_object* v_aliasName_1191_, lean_object* v_value_1192_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1221_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1221_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1221_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
uint8_t v___x_1199_; 
v___x_1199_ = lean_unbox(v_a_1195_);
lean_dec(v_a_1195_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
lean_dec_ref(v_value_1192_);
lean_dec(v_aliasName_1191_);
v___x_1200_ = lean_obj_once(&l_Lean_Parser_registerAliasCore___redArg___closed__1, &l_Lean_Parser_registerAliasCore___redArg___closed__1_once, _init_l_Lean_Parser_registerAliasCore___redArg___closed__1);
if (v_isShared_1198_ == 0)
{
lean_ctor_set_tag(v___x_1197_, 1);
lean_ctor_set(v___x_1197_, 0, v___x_1200_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
else
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_st_ref_get(v_mapRef_1190_);
v___x_1205_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_aliasName_1191_, v___x_1204_);
lean_dec(v___x_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1206_ = lean_st_ref_take(v_mapRef_1190_);
v___x_1207_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1191_, v_value_1192_, v___x_1206_);
v___x_1208_ = lean_st_ref_set(v_mapRef_1190_, v___x_1207_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1208_);
v___x_1210_ = v___x_1197_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
lean_dec_ref(v_value_1192_);
v___x_1212_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__2));
v___x_1213_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1191_, v___x_1205_);
v___x_1214_ = lean_string_append(v___x_1212_, v___x_1213_);
lean_dec_ref(v___x_1213_);
v___x_1215_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__3));
v___x_1216_ = lean_string_append(v___x_1214_, v___x_1215_);
v___x_1217_ = lean_mk_io_user_error(v___x_1216_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set_tag(v___x_1197_, 1);
lean_ctor_set(v___x_1197_, 0, v___x_1217_);
v___x_1219_ = v___x_1197_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec_ref(v_value_1192_);
lean_dec(v_aliasName_1191_);
v_a_1222_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1194_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1194_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg___boxed(lean_object* v_mapRef_1230_, lean_object* v_aliasName_1231_, lean_object* v_value_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1230_, v_aliasName_1231_, v_value_1232_);
lean_dec(v_mapRef_1230_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore(lean_object* v_00_u03b1_1235_, lean_object* v_mapRef_1236_, lean_object* v_aliasName_1237_, lean_object* v_value_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1236_, v_aliasName_1237_, v_value_1238_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___boxed(lean_object* v_00_u03b1_1241_, lean_object* v_mapRef_1242_, lean_object* v_aliasName_1243_, lean_object* v_value_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Parser_registerAliasCore(v_00_u03b1_1241_, v_mapRef_1242_, v_aliasName_1243_, v_value_1244_);
lean_dec(v_mapRef_1242_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg(lean_object* v_mapRef_1247_, lean_object* v_aliasName_1248_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_st_ref_get(v_mapRef_1247_);
v___x_1251_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1250_, v_aliasName_1248_);
lean_dec(v___x_1250_);
v___x_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg___boxed(lean_object* v_mapRef_1253_, lean_object* v_aliasName_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1253_, v_aliasName_1254_);
lean_dec(v_aliasName_1254_);
lean_dec(v_mapRef_1253_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias(lean_object* v_00_u03b1_1257_, lean_object* v_mapRef_1258_, lean_object* v_aliasName_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1258_, v_aliasName_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___boxed(lean_object* v_00_u03b1_1262_, lean_object* v_mapRef_1263_, lean_object* v_aliasName_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Parser_getAlias(v_00_u03b1_1262_, v_mapRef_1263_, v_aliasName_1264_);
lean_dec(v_aliasName_1264_);
lean_dec(v_mapRef_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object* v_mapRef_1271_, lean_object* v_aliasName_1272_){
_start:
{
lean_object* v___x_1274_; lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1314_; 
v___x_1274_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1271_, v_aliasName_1272_);
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1314_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1314_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
if (lean_obj_tag(v_a_1275_) == 0)
{
lean_object* v___x_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1279_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1280_ = 1;
v___x_1281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1272_, v___x_1280_);
v___x_1282_ = lean_string_append(v___x_1279_, v___x_1281_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1284_ = lean_string_append(v___x_1282_, v___x_1283_);
v___x_1285_ = lean_mk_io_user_error(v___x_1284_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 1);
lean_ctor_set(v___x_1277_, 0, v___x_1285_);
v___x_1287_ = v___x_1277_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
else
{
lean_object* v_val_1289_; 
v_val_1289_ = lean_ctor_get(v_a_1275_, 0);
lean_inc(v_val_1289_);
lean_dec_ref(v_a_1275_);
switch(lean_obj_tag(v_val_1289_))
{
case 0:
{
lean_object* v_p_1290_; lean_object* v___x_1292_; 
lean_dec(v_aliasName_1272_);
v_p_1290_ = lean_ctor_get(v_val_1289_, 0);
lean_inc(v_p_1290_);
lean_dec_ref(v_val_1289_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v_p_1290_);
v___x_1292_ = v___x_1277_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_p_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
case 1:
{
lean_object* v___x_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_dec_ref(v_val_1289_);
v___x_1294_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1295_ = 1;
v___x_1296_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1272_, v___x_1295_);
v___x_1297_ = lean_string_append(v___x_1294_, v___x_1296_);
lean_dec_ref(v___x_1296_);
v___x_1298_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__2));
v___x_1299_ = lean_string_append(v___x_1297_, v___x_1298_);
v___x_1300_ = lean_mk_io_user_error(v___x_1299_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 1);
lean_ctor_set(v___x_1277_, 0, v___x_1300_);
v___x_1302_ = v___x_1277_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
default: 
{
lean_object* v___x_1304_; uint8_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
lean_dec_ref(v_val_1289_);
v___x_1304_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1305_ = 1;
v___x_1306_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1272_, v___x_1305_);
v___x_1307_ = lean_string_append(v___x_1304_, v___x_1306_);
lean_dec_ref(v___x_1306_);
v___x_1308_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__3));
v___x_1309_ = lean_string_append(v___x_1307_, v___x_1308_);
v___x_1310_ = lean_mk_io_user_error(v___x_1309_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 1);
lean_ctor_set(v___x_1277_, 0, v___x_1310_);
v___x_1312_ = v___x_1277_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object* v_mapRef_1315_, lean_object* v_aliasName_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1315_, v_aliasName_1316_);
lean_dec(v_mapRef_1315_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object* v_00_u03b1_1319_, lean_object* v_mapRef_1320_, lean_object* v_aliasName_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1320_, v_aliasName_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object* v_00_u03b1_1324_, lean_object* v_mapRef_1325_, lean_object* v_aliasName_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Parser_getConstAlias(v_00_u03b1_1324_, v_mapRef_1325_, v_aliasName_1326_);
lean_dec(v_mapRef_1325_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object* v_mapRef_1330_, lean_object* v_aliasName_1331_){
_start:
{
lean_object* v___x_1333_; lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1363_; 
v___x_1333_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1330_, v_aliasName_1331_);
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1363_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1363_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
if (lean_obj_tag(v_a_1334_) == 0)
{
lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1338_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1339_ = 1;
v___x_1340_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1331_, v___x_1339_);
v___x_1341_ = lean_string_append(v___x_1338_, v___x_1340_);
lean_dec_ref(v___x_1340_);
v___x_1342_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1343_ = lean_string_append(v___x_1341_, v___x_1342_);
v___x_1344_ = lean_mk_io_user_error(v___x_1343_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 1);
lean_ctor_set(v___x_1336_, 0, v___x_1344_);
v___x_1346_ = v___x_1336_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
else
{
lean_object* v_val_1348_; 
v_val_1348_ = lean_ctor_get(v_a_1334_, 0);
lean_inc(v_val_1348_);
lean_dec_ref(v_a_1334_);
if (lean_obj_tag(v_val_1348_) == 1)
{
lean_object* v_p_1349_; lean_object* v___x_1351_; 
lean_dec(v_aliasName_1331_);
v_p_1349_ = lean_ctor_get(v_val_1348_, 0);
lean_inc(v_p_1349_);
lean_dec_ref(v_val_1348_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v_p_1349_);
v___x_1351_ = v___x_1336_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_p_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
else
{
lean_object* v___x_1353_; uint8_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
lean_dec(v_val_1348_);
v___x_1353_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1354_ = 1;
v___x_1355_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1331_, v___x_1354_);
v___x_1356_ = lean_string_append(v___x_1353_, v___x_1355_);
lean_dec_ref(v___x_1355_);
v___x_1357_ = ((lean_object*)(l_Lean_Parser_getUnaryAlias___redArg___closed__0));
v___x_1358_ = lean_string_append(v___x_1356_, v___x_1357_);
v___x_1359_ = lean_mk_io_user_error(v___x_1358_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 1);
lean_ctor_set(v___x_1336_, 0, v___x_1359_);
v___x_1361_ = v___x_1336_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object* v_mapRef_1364_, lean_object* v_aliasName_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1364_, v_aliasName_1365_);
lean_dec(v_mapRef_1364_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object* v_00_u03b1_1368_, lean_object* v_mapRef_1369_, lean_object* v_aliasName_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1369_, v_aliasName_1370_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object* v_00_u03b1_1373_, lean_object* v_mapRef_1374_, lean_object* v_aliasName_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_Parser_getUnaryAlias(v_00_u03b1_1373_, v_mapRef_1374_, v_aliasName_1375_);
lean_dec(v_mapRef_1374_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object* v_mapRef_1379_, lean_object* v_aliasName_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1412_; 
v___x_1382_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1379_, v_aliasName_1380_);
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1412_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1412_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
if (lean_obj_tag(v_a_1383_) == 0)
{
lean_object* v___x_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1387_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1388_ = 1;
v___x_1389_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1380_, v___x_1388_);
v___x_1390_ = lean_string_append(v___x_1387_, v___x_1389_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1392_ = lean_string_append(v___x_1390_, v___x_1391_);
v___x_1393_ = lean_mk_io_user_error(v___x_1392_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set_tag(v___x_1385_, 1);
lean_ctor_set(v___x_1385_, 0, v___x_1393_);
v___x_1395_ = v___x_1385_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
else
{
lean_object* v_val_1397_; 
v_val_1397_ = lean_ctor_get(v_a_1383_, 0);
lean_inc(v_val_1397_);
lean_dec_ref(v_a_1383_);
if (lean_obj_tag(v_val_1397_) == 2)
{
lean_object* v_p_1398_; lean_object* v___x_1400_; 
lean_dec(v_aliasName_1380_);
v_p_1398_ = lean_ctor_get(v_val_1397_, 0);
lean_inc(v_p_1398_);
lean_dec_ref(v_val_1397_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v_p_1398_);
v___x_1400_ = v___x_1385_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_p_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
else
{
lean_object* v___x_1402_; uint8_t v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_dec(v_val_1397_);
v___x_1402_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1403_ = 1;
v___x_1404_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1380_, v___x_1403_);
v___x_1405_ = lean_string_append(v___x_1402_, v___x_1404_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Lean_Parser_getBinaryAlias___redArg___closed__0));
v___x_1407_ = lean_string_append(v___x_1405_, v___x_1406_);
v___x_1408_ = lean_mk_io_user_error(v___x_1407_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set_tag(v___x_1385_, 1);
lean_ctor_set(v___x_1385_, 0, v___x_1408_);
v___x_1410_ = v___x_1385_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg___boxed(lean_object* v_mapRef_1413_, lean_object* v_aliasName_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1413_, v_aliasName_1414_);
lean_dec(v_mapRef_1413_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object* v_00_u03b1_1417_, lean_object* v_mapRef_1418_, lean_object* v_aliasName_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1418_, v_aliasName_1419_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___boxed(lean_object* v_00_u03b1_1422_, lean_object* v_mapRef_1423_, lean_object* v_aliasName_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_Parser_getBinaryAlias(v_00_u03b1_1422_, v_mapRef_1423_, v_aliasName_1424_);
lean_dec(v_mapRef_1423_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = lean_box(1);
v___x_1429_ = lean_st_mk_ref(v___x_1428_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_box(1);
v___x_1435_ = lean_st_mk_ref(v___x_1434_);
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = lean_box(1);
v___x_1441_ = lean_st_mk_ref(v___x_1440_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object* v_a_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(lean_object* v_t_1445_, lean_object* v_k_1446_, lean_object* v_fallback_1447_){
_start:
{
if (lean_obj_tag(v_t_1445_) == 0)
{
lean_object* v_k_1448_; lean_object* v_v_1449_; lean_object* v_l_1450_; lean_object* v_r_1451_; uint8_t v___x_1452_; 
v_k_1448_ = lean_ctor_get(v_t_1445_, 1);
v_v_1449_ = lean_ctor_get(v_t_1445_, 2);
v_l_1450_ = lean_ctor_get(v_t_1445_, 3);
v_r_1451_ = lean_ctor_get(v_t_1445_, 4);
v___x_1452_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1446_, v_k_1448_);
switch(v___x_1452_)
{
case 0:
{
v_t_1445_ = v_l_1450_;
goto _start;
}
case 1:
{
lean_inc(v_v_1449_);
return v_v_1449_;
}
default: 
{
v_t_1445_ = v_r_1451_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_1447_);
return v_fallback_1447_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg___boxed(lean_object* v_t_1455_, lean_object* v_k_1456_, lean_object* v_fallback_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1455_, v_k_1456_, v_fallback_1457_);
lean_dec(v_fallback_1457_);
lean_dec(v_k_1456_);
lean_dec(v_t_1455_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo(lean_object* v_aliasName_1465_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1467_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1468_ = lean_st_ref_get(v___x_1467_);
v___x_1469_ = ((lean_object*)(l_Lean_Parser_getParserAliasInfo___closed__1));
v___x_1470_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v___x_1468_, v_aliasName_1465_, v___x_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo___boxed(lean_object* v_aliasName_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Parser_getParserAliasInfo(v_aliasName_1472_);
lean_dec(v_aliasName_1472_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(lean_object* v_00_u03b4_1475_, lean_object* v_t_1476_, lean_object* v_k_1477_, lean_object* v_fallback_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1476_, v_k_1477_, v_fallback_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___boxed(lean_object* v_00_u03b4_1480_, lean_object* v_t_1481_, lean_object* v_k_1482_, lean_object* v_fallback_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(v_00_u03b4_1480_, v_t_1481_, v_k_1482_, v_fallback_1483_);
lean_dec(v_fallback_1483_);
lean_dec(v_k_1482_);
lean_dec(v_t_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object* v_aliasName_1485_, lean_object* v_declName_1486_, lean_object* v_p_1487_, lean_object* v_kind_x3f_1488_, lean_object* v_info_1489_){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = l_Lean_Parser_parserAliasesRef;
lean_inc(v_aliasName_1485_);
v___x_1508_ = l_Lean_Parser_registerAliasCore___redArg(v___x_1507_, v_aliasName_1485_, v_p_1487_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_dec_ref(v___x_1508_);
if (lean_obj_tag(v_kind_x3f_1488_) == 1)
{
lean_object* v_val_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v_val_1509_ = lean_ctor_get(v_kind_x3f_1488_, 0);
lean_inc(v_val_1509_);
lean_dec_ref(v_kind_x3f_1488_);
v___x_1510_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1511_ = lean_st_ref_take(v___x_1510_);
lean_inc(v_aliasName_1485_);
v___x_1512_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1485_, v_val_1509_, v___x_1511_);
v___x_1513_ = lean_st_ref_set(v___x_1510_, v___x_1512_);
goto v___jp_1491_;
}
else
{
lean_dec(v_kind_x3f_1488_);
goto v___jp_1491_;
}
}
else
{
lean_dec_ref(v_info_1489_);
lean_dec(v_kind_x3f_1488_);
lean_dec(v_declName_1486_);
lean_dec(v_aliasName_1485_);
return v___x_1508_;
}
v___jp_1491_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v_stackSz_x3f_1494_; uint8_t v_autoGroupArgs_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1505_; 
v___x_1492_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1493_ = lean_st_ref_take(v___x_1492_);
v_stackSz_x3f_1494_ = lean_ctor_get(v_info_1489_, 1);
v_autoGroupArgs_1495_ = lean_ctor_get_uint8(v_info_1489_, sizeof(void*)*2);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_info_1489_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_info_1489_, 0);
lean_dec(v_unused_1506_);
v___x_1497_ = v_info_1489_;
v_isShared_1498_ = v_isSharedCheck_1505_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_stackSz_x3f_1494_);
lean_dec(v_info_1489_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1505_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v_declName_1486_);
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_declName_1486_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_stackSz_x3f_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1504_, sizeof(void*)*2, v_autoGroupArgs_1495_);
v___x_1500_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1485_, v___x_1500_, v___x_1493_);
v___x_1502_ = lean_st_ref_set(v___x_1492_, v___x_1501_);
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias___boxed(lean_object* v_aliasName_1514_, lean_object* v_declName_1515_, lean_object* v_p_1516_, lean_object* v_kind_x3f_1517_, lean_object* v_info_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_Parser_registerAlias(v_aliasName_1514_, v_declName_1515_, v_p_1516_, v_kind_x3f_1517_, v_info_1518_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue___lam__0(lean_object* v_p_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v_p_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0(lean_object* v_p_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1526_, 0, v_p_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0(lean_object* v_p_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_p_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object* v_aliasName_1533_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1551_; 
v___x_1535_ = l_Lean_Parser_parserAliasesRef;
v___x_1536_ = l_Lean_Parser_getAlias___redArg(v___x_1535_, v_aliasName_1533_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1551_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1551_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
if (lean_obj_tag(v_a_1537_) == 1)
{
uint8_t v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
lean_dec_ref(v_a_1537_);
v___x_1541_ = 1;
v___x_1542_ = lean_box(v___x_1541_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1542_);
v___x_1544_ = v___x_1539_;
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
else
{
uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
lean_dec(v_a_1537_);
v___x_1546_ = 0;
v___x_1547_ = lean_box(v___x_1546_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1547_);
v___x_1549_ = v___x_1539_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object* v_aliasName_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Parser_isParserAlias(v_aliasName_1552_);
lean_dec(v_aliasName_1552_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object* v_aliasName_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1557_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1558_ = lean_st_ref_get(v___x_1557_);
v___x_1559_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1558_, v_aliasName_1555_);
lean_dec(v___x_1558_);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f___boxed(lean_object* v_aliasName_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v_aliasName_1561_);
lean_dec(v_aliasName_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object* v_aliasName_1564_){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = l_Lean_Parser_parserAliasesRef;
v___x_1567_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1566_, v_aliasName_1564_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1575_; 
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v___x_1567_, 0);
lean_dec(v_unused_1576_);
v___x_1569_ = v___x_1567_;
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
else
{
lean_dec(v___x_1567_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = lean_box(0);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1571_);
v___x_1573_ = v___x_1569_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
v_a_1577_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1567_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1567_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias___boxed(lean_object* v_aliasName_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Parser_ensureUnaryParserAlias(v_aliasName_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object* v_aliasName_1588_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = l_Lean_Parser_parserAliasesRef;
v___x_1591_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1590_, v_aliasName_1588_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1599_; 
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; 
v_unused_1600_ = lean_ctor_get(v___x_1591_, 0);
lean_dec(v_unused_1600_);
v___x_1593_ = v___x_1591_;
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
else
{
lean_dec(v___x_1591_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1595_ = lean_box(0);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1595_);
v___x_1597_ = v___x_1593_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1591_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1591_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias___boxed(lean_object* v_aliasName_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Parser_ensureBinaryParserAlias(v_aliasName_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object* v_aliasName_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = l_Lean_Parser_parserAliasesRef;
v___x_1615_ = l_Lean_Parser_getConstAlias___redArg(v___x_1614_, v_aliasName_1612_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1623_; 
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v___x_1615_, 0);
lean_dec(v_unused_1624_);
v___x_1617_ = v___x_1615_;
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
else
{
lean_dec(v___x_1615_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = lean_box(0);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1619_);
v___x_1621_ = v___x_1617_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
v_a_1625_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1615_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1615_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias___boxed(lean_object* v_aliasName_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Parser_ensureConstantParserAlias(v_aliasName_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* v_constName_1644_, lean_object* v_compileParserDescr_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_env_1657_; lean_object* v_opts_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; 
v_env_1657_ = lean_ctor_get(v_a_1646_, 0);
v_opts_1658_ = lean_ctor_get(v_a_1646_, 1);
v___x_1659_ = 0;
lean_inc(v_constName_1644_);
lean_inc_ref(v_env_1657_);
v___x_1660_ = l_Lean_Environment_find_x3f(v_env_1657_, v_constName_1644_, v___x_1659_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec_ref(v_compileParserDescr_1645_);
v___x_1661_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_1662_ = 1;
v___x_1663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1644_, v___x_1662_);
v___x_1664_ = lean_string_append(v___x_1661_, v___x_1663_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_1666_ = lean_string_append(v___x_1664_, v___x_1665_);
v___x_1667_ = lean_mk_io_user_error(v___x_1666_);
v___x_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
return v___x_1668_;
}
else
{
lean_object* v_val_1669_; lean_object* v___x_1670_; 
v_val_1669_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_val_1669_);
lean_dec_ref(v___x_1660_);
v___x_1670_ = l_Lean_ConstantInfo_type(v_val_1669_);
lean_dec(v_val_1669_);
if (lean_obj_tag(v___x_1670_) == 4)
{
lean_object* v_declName_1671_; 
v_declName_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_declName_1671_);
lean_dec_ref(v___x_1670_);
if (lean_obj_tag(v_declName_1671_) == 1)
{
lean_object* v_pre_1672_; 
v_pre_1672_ = lean_ctor_get(v_declName_1671_, 0);
lean_inc(v_pre_1672_);
if (lean_obj_tag(v_pre_1672_) == 1)
{
lean_object* v_pre_1673_; 
v_pre_1673_ = lean_ctor_get(v_pre_1672_, 0);
switch(lean_obj_tag(v_pre_1673_))
{
case 1:
{
lean_object* v_pre_1674_; 
lean_inc_ref(v_pre_1673_);
lean_dec_ref(v_compileParserDescr_1645_);
v_pre_1674_ = lean_ctor_get(v_pre_1673_, 0);
if (lean_obj_tag(v_pre_1674_) == 0)
{
lean_object* v_str_1675_; lean_object* v_str_1676_; lean_object* v_str_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v_str_1675_ = lean_ctor_get(v_declName_1671_, 1);
lean_inc_ref(v_str_1675_);
lean_dec_ref(v_declName_1671_);
v_str_1676_ = lean_ctor_get(v_pre_1672_, 1);
lean_inc_ref(v_str_1676_);
lean_dec_ref(v_pre_1672_);
v_str_1677_ = lean_ctor_get(v_pre_1673_, 1);
lean_inc_ref(v_str_1677_);
lean_dec_ref(v_pre_1673_);
v___x_1678_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1679_ = lean_string_dec_eq(v_str_1677_, v___x_1678_);
lean_dec_ref(v_str_1677_);
if (v___x_1679_ == 0)
{
lean_dec_ref(v_str_1676_);
lean_dec_ref(v_str_1675_);
goto v___jp_1648_;
}
else
{
lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1680_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_1681_ = lean_string_dec_eq(v_str_1676_, v___x_1680_);
lean_dec_ref(v_str_1676_);
if (v___x_1681_ == 0)
{
lean_dec_ref(v_str_1675_);
goto v___jp_1648_;
}
else
{
lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_1683_ = lean_string_dec_eq(v_str_1675_, v___x_1682_);
if (v___x_1683_ == 0)
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_string_dec_eq(v_str_1675_, v___x_1680_);
lean_dec_ref(v_str_1675_);
if (v___x_1684_ == 0)
{
goto v___jp_1648_;
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = l_Lean_Environment_evalConst___redArg(v_env_1657_, v_opts_1658_, v_constName_1644_, v___x_1684_);
lean_dec(v_constName_1644_);
v___x_1686_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1685_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1696_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1689_ = v___x_1686_;
v_isShared_1690_ = v_isSharedCheck_1696_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1696_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1691_ = lean_box(v___x_1684_);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v_a_1687_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1692_);
v___x_1694_ = v___x_1689_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
v_a_1697_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1686_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1686_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec_ref(v_str_1675_);
v___x_1705_ = l_Lean_Environment_evalConst___redArg(v_env_1657_, v_opts_1658_, v_constName_1644_, v___x_1683_);
lean_dec(v_constName_1644_);
v___x_1706_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1705_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1716_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1716_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1716_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1711_ = lean_box(v___x_1659_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
lean_ctor_set(v___x_1712_, 1, v_a_1707_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1712_);
v___x_1714_ = v___x_1709_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
v_a_1717_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1706_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1706_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_1673_);
lean_dec_ref(v_pre_1672_);
lean_dec_ref(v_declName_1671_);
goto v___jp_1648_;
}
}
case 0:
{
lean_object* v_str_1725_; lean_object* v_str_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_str_1725_ = lean_ctor_get(v_declName_1671_, 1);
lean_inc_ref(v_str_1725_);
lean_dec_ref(v_declName_1671_);
v_str_1726_ = lean_ctor_get(v_pre_1672_, 1);
lean_inc_ref(v_str_1726_);
lean_dec_ref(v_pre_1672_);
v___x_1727_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1728_ = lean_string_dec_eq(v_str_1726_, v___x_1727_);
lean_dec_ref(v_str_1726_);
if (v___x_1728_ == 0)
{
lean_dec_ref(v_str_1725_);
lean_dec_ref(v_compileParserDescr_1645_);
goto v___jp_1648_;
}
else
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_1730_ = lean_string_dec_eq(v_str_1725_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_1732_ = lean_string_dec_eq(v_str_1725_, v___x_1731_);
lean_dec_ref(v_str_1725_);
if (v___x_1732_ == 0)
{
lean_dec_ref(v_compileParserDescr_1645_);
goto v___jp_1648_;
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = l_Lean_Environment_evalConst___redArg(v_env_1657_, v_opts_1658_, v_constName_1644_, v___x_1732_);
lean_dec(v_constName_1644_);
v___x_1734_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1733_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1736_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref(v___x_1734_);
lean_inc_ref(v_a_1646_);
v___x_1736_ = lean_apply_3(v_compileParserDescr_1645_, v_a_1735_, v_a_1646_, lean_box(0));
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1746_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1746_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1746_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1741_ = lean_box(v___x_1659_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v_a_1737_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1742_);
v___x_1744_ = v___x_1739_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
v_a_1747_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1736_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1736_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref(v_compileParserDescr_1645_);
v_a_1755_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1734_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1734_);
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
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_dec_ref(v_str_1725_);
v___x_1763_ = l_Lean_Environment_evalConst___redArg(v_env_1657_, v_opts_1658_, v_constName_1644_, v___x_1730_);
lean_dec(v_constName_1644_);
v___x_1764_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1763_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref(v___x_1764_);
lean_inc_ref(v_a_1646_);
v___x_1766_ = lean_apply_3(v_compileParserDescr_1645_, v_a_1765_, v_a_1646_, lean_box(0));
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1776_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1776_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1776_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1771_ = lean_box(v___x_1730_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v_a_1767_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1772_);
v___x_1774_ = v___x_1769_;
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
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
v_a_1777_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1766_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1766_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
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
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref(v_compileParserDescr_1645_);
v_a_1785_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1764_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1764_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_pre_1672_);
lean_dec_ref(v_declName_1671_);
lean_dec_ref(v_compileParserDescr_1645_);
goto v___jp_1648_;
}
}
}
else
{
lean_dec_ref(v_declName_1671_);
lean_dec(v_pre_1672_);
lean_dec_ref(v_compileParserDescr_1645_);
goto v___jp_1648_;
}
}
else
{
lean_dec(v_declName_1671_);
lean_dec_ref(v_compileParserDescr_1645_);
goto v___jp_1648_;
}
}
else
{
lean_dec_ref(v___x_1670_);
lean_dec_ref(v_compileParserDescr_1645_);
goto v___jp_1648_;
}
}
v___jp_1648_:
{
lean_object* v___x_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1649_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__0));
v___x_1650_ = 1;
v___x_1651_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1644_, v___x_1650_);
v___x_1652_ = lean_string_append(v___x_1649_, v___x_1651_);
lean_dec_ref(v___x_1651_);
v___x_1653_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1));
v___x_1654_ = lean_string_append(v___x_1652_, v___x_1653_);
v___x_1655_ = lean_mk_io_user_error(v___x_1654_);
v___x_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object* v_constName_1793_, lean_object* v_compileParserDescr_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1793_, v_compileParserDescr_1794_, v_a_1795_);
lean_dec_ref(v_a_1795_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed(lean_object* v_categories_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1798_, v_a_1799_, v_a_1800_);
lean_dec_ref(v_a_1800_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(lean_object* v_categories_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
switch(lean_obj_tag(v_a_1804_))
{
case 0:
{
lean_object* v_name_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec_ref(v_categories_1803_);
v_name_1807_ = lean_ctor_get(v_a_1804_, 0);
lean_inc(v_name_1807_);
lean_dec_ref(v_a_1804_);
v___x_1808_ = l_Lean_Parser_parserAliasesRef;
v___x_1809_ = l_Lean_Parser_getConstAlias___redArg(v___x_1808_, v_name_1807_);
return v___x_1809_;
}
case 1:
{
lean_object* v_name_1810_; lean_object* v_p_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_name_1810_ = lean_ctor_get(v_a_1804_, 0);
lean_inc(v_name_1810_);
v_p_1811_ = lean_ctor_get(v_a_1804_, 1);
lean_inc_ref(v_p_1811_);
lean_dec_ref(v_a_1804_);
v___x_1812_ = l_Lean_Parser_parserAliasesRef;
v___x_1813_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1812_, v_name_1810_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1815_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref(v___x_1813_);
v___x_1815_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1803_, v_p_1811_, v_a_1805_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1824_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = lean_apply_1(v_a_1814_, v_a_1816_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1820_);
v___x_1822_ = v___x_1818_;
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
else
{
lean_dec(v_a_1814_);
return v___x_1815_;
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec_ref(v_p_1811_);
lean_dec_ref(v_categories_1803_);
v_a_1825_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1813_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1813_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
case 2:
{
lean_object* v_name_1833_; lean_object* v_p_u2081_1834_; lean_object* v_p_u2082_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_name_1833_ = lean_ctor_get(v_a_1804_, 0);
lean_inc(v_name_1833_);
v_p_u2081_1834_ = lean_ctor_get(v_a_1804_, 1);
lean_inc_ref(v_p_u2081_1834_);
v_p_u2082_1835_ = lean_ctor_get(v_a_1804_, 2);
lean_inc_ref(v_p_u2082_1835_);
lean_dec_ref(v_a_1804_);
v___x_1836_ = l_Lean_Parser_parserAliasesRef;
v___x_1837_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1836_, v_name_1833_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
lean_inc_ref(v_categories_1803_);
v___x_1839_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1803_, v_p_u2081_1834_, v_a_1805_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1841_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref(v___x_1839_);
v___x_1841_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1803_, v_p_u2082_1835_, v_a_1805_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1850_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = lean_apply_2(v_a_1838_, v_a_1840_, v_a_1842_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1846_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
lean_dec(v_a_1840_);
lean_dec(v_a_1838_);
return v___x_1841_;
}
}
else
{
lean_dec(v_a_1838_);
lean_dec_ref(v_p_u2082_1835_);
lean_dec_ref(v_categories_1803_);
return v___x_1839_;
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref(v_p_u2082_1835_);
lean_dec_ref(v_p_u2081_1834_);
lean_dec_ref(v_categories_1803_);
v_a_1851_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1837_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1837_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
case 3:
{
lean_object* v_kind_1859_; lean_object* v_prec_1860_; lean_object* v_p_1861_; lean_object* v___x_1862_; 
v_kind_1859_ = lean_ctor_get(v_a_1804_, 0);
lean_inc(v_kind_1859_);
v_prec_1860_ = lean_ctor_get(v_a_1804_, 1);
lean_inc(v_prec_1860_);
v_p_1861_ = lean_ctor_get(v_a_1804_, 2);
lean_inc_ref(v_p_1861_);
lean_dec_ref(v_a_1804_);
v___x_1862_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1803_, v_p_1861_, v_a_1805_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1871_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1867_ = l_Lean_Parser_leadingNode(v_kind_1859_, v_prec_1860_, v_a_1863_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1867_);
v___x_1869_ = v___x_1865_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
else
{
lean_dec(v_prec_1860_);
lean_dec(v_kind_1859_);
return v___x_1862_;
}
}
case 4:
{
lean_object* v_kind_1872_; lean_object* v_prec_1873_; lean_object* v_lhsPrec_1874_; lean_object* v_p_1875_; lean_object* v___x_1876_; 
v_kind_1872_ = lean_ctor_get(v_a_1804_, 0);
lean_inc(v_kind_1872_);
v_prec_1873_ = lean_ctor_get(v_a_1804_, 1);
lean_inc(v_prec_1873_);
v_lhsPrec_1874_ = lean_ctor_get(v_a_1804_, 2);
lean_inc(v_lhsPrec_1874_);
v_p_1875_ = lean_ctor_get(v_a_1804_, 3);
lean_inc_ref(v_p_1875_);
lean_dec_ref(v_a_1804_);
v___x_1876_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1803_, v_p_1875_, v_a_1805_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1885_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1881_ = l_Lean_Parser_trailingNode(v_kind_1872_, v_prec_1873_, v_lhsPrec_1874_, v_a_1877_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1881_);
v___x_1883_ = v___x_1879_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
else
{
lean_dec(v_lhsPrec_1874_);
lean_dec(v_prec_1873_);
lean_dec(v_kind_1872_);
return v___x_1876_;
}
}
case 5:
{
lean_object* v_val_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1894_; 
lean_dec_ref(v_categories_1803_);
v_val_1886_ = lean_ctor_get(v_a_1804_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_a_1804_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1888_ = v_a_1804_;
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_val_1886_);
lean_dec(v_a_1804_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = l_Lean_Parser_symbol(v_val_1886_);
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
case 6:
{
lean_object* v_val_1895_; uint8_t v_includeIdent_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec_ref(v_categories_1803_);
v_val_1895_ = lean_ctor_get(v_a_1804_, 0);
lean_inc_ref(v_val_1895_);
v_includeIdent_1896_ = lean_ctor_get_uint8(v_a_1804_, sizeof(void*)*1);
lean_dec_ref(v_a_1804_);
v___x_1897_ = l_Lean_Parser_nonReservedSymbol(v_val_1895_, v_includeIdent_1896_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
case 7:
{
lean_object* v_catName_1899_; lean_object* v_rbp_1900_; lean_object* v___x_1901_; 
v_catName_1899_ = lean_ctor_get(v_a_1804_, 0);
lean_inc(v_catName_1899_);
v_rbp_1900_ = lean_ctor_get(v_a_1804_, 1);
lean_inc(v_rbp_1900_);
lean_dec_ref(v_a_1804_);
v___x_1901_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_1803_, v_catName_1899_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec(v_rbp_1900_);
v___x_1902_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_1899_);
v___x_1903_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1902_);
return v___x_1903_;
}
else
{
lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1911_; 
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v___x_1901_, 0);
lean_dec(v_unused_1912_);
v___x_1905_ = v___x_1901_;
v_isShared_1906_ = v_isSharedCheck_1911_;
goto v_resetjp_1904_;
}
else
{
lean_dec(v___x_1901_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1911_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = l_Lean_Parser_categoryParser(v_catName_1899_, v_rbp_1900_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set_tag(v___x_1905_, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1907_);
v___x_1909_ = v___x_1905_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
case 8:
{
lean_object* v_declName_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_declName_1913_ = lean_ctor_get(v_a_1804_, 0);
lean_inc(v_declName_1913_);
lean_dec_ref(v_a_1804_);
v___x_1914_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed), 4, 1);
lean_closure_set(v___x_1914_, 0, v_categories_1803_);
v___x_1915_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_declName_1913_, v___x_1914_, v_a_1805_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1924_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_snd_1920_; lean_object* v___x_1922_; 
v_snd_1920_ = lean_ctor_get(v_a_1916_, 1);
lean_inc(v_snd_1920_);
lean_dec(v_a_1916_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v_snd_1920_);
v___x_1922_ = v___x_1918_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_snd_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
v_a_1925_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1915_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1915_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
case 9:
{
lean_object* v_name_1933_; lean_object* v_kind_1934_; lean_object* v_p_1935_; lean_object* v___x_1936_; 
v_name_1933_ = lean_ctor_get(v_a_1804_, 0);
lean_inc_ref(v_name_1933_);
v_kind_1934_ = lean_ctor_get(v_a_1804_, 1);
lean_inc(v_kind_1934_);
v_p_1935_ = lean_ctor_get(v_a_1804_, 2);
lean_inc_ref(v_p_1935_);
lean_dec_ref(v_a_1804_);
v___x_1936_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1803_, v_p_1935_, v_a_1805_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1947_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1947_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1947_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
uint8_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1941_ = 1;
lean_inc(v_kind_1934_);
v___x_1942_ = l_Lean_Parser_nodeWithAntiquot(v_name_1933_, v_kind_1934_, v_a_1937_, v___x_1941_);
v___x_1943_ = l_Lean_Parser_withCache(v_kind_1934_, v___x_1942_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1943_);
v___x_1945_ = v___x_1939_;
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
lean_dec(v_kind_1934_);
lean_dec_ref(v_name_1933_);
return v___x_1936_;
}
}
case 10:
{
lean_object* v_p_1948_; lean_object* v_sep_1949_; lean_object* v_psep_1950_; uint8_t v_allowTrailingSep_1951_; lean_object* v___x_1952_; 
v_p_1948_ = lean_ctor_get(v_a_1804_, 0);
lean_inc_ref(v_p_1948_);
v_sep_1949_ = lean_ctor_get(v_a_1804_, 1);
lean_inc_ref(v_sep_1949_);
v_psep_1950_ = lean_ctor_get(v_a_1804_, 2);
lean_inc_ref(v_psep_1950_);
v_allowTrailingSep_1951_ = lean_ctor_get_uint8(v_a_1804_, sizeof(void*)*3);
lean_dec_ref(v_a_1804_);
lean_inc_ref(v_categories_1803_);
v___x_1952_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1803_, v_p_1948_, v_a_1805_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1803_, v_psep_1950_, v_a_1805_);
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
v___x_1959_ = l_Lean_Parser_sepBy(v_a_1953_, v_sep_1949_, v_a_1955_, v_allowTrailingSep_1951_);
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
lean_dec_ref(v_categories_1803_);
return v___x_1952_;
}
}
case 11:
{
lean_object* v_p_1964_; lean_object* v_sep_1965_; lean_object* v_psep_1966_; uint8_t v_allowTrailingSep_1967_; lean_object* v___x_1968_; 
v_p_1964_ = lean_ctor_get(v_a_1804_, 0);
lean_inc_ref(v_p_1964_);
v_sep_1965_ = lean_ctor_get(v_a_1804_, 1);
lean_inc_ref(v_sep_1965_);
v_psep_1966_ = lean_ctor_get(v_a_1804_, 2);
lean_inc_ref(v_psep_1966_);
v_allowTrailingSep_1967_ = lean_ctor_get_uint8(v_a_1804_, sizeof(void*)*3);
lean_dec_ref(v_a_1804_);
lean_inc_ref(v_categories_1803_);
v___x_1968_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1803_, v_p_1964_, v_a_1805_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___x_1968_);
v___x_1970_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1803_, v_psep_1966_, v_a_1805_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1979_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1975_ = l_Lean_Parser_sepBy1(v_a_1969_, v_sep_1965_, v_a_1971_, v_allowTrailingSep_1967_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1975_);
v___x_1977_ = v___x_1973_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
lean_dec(v_a_1969_);
lean_dec_ref(v_sep_1965_);
return v___x_1970_;
}
}
else
{
lean_dec_ref(v_psep_1966_);
lean_dec_ref(v_sep_1965_);
lean_dec_ref(v_categories_1803_);
return v___x_1968_;
}
}
default: 
{
lean_object* v_val_1980_; lean_object* v_asciiVal_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_dec_ref(v_categories_1803_);
v_val_1980_ = lean_ctor_get(v_a_1804_, 0);
lean_inc_ref(v_val_1980_);
v_asciiVal_1981_ = lean_ctor_get(v_a_1804_, 1);
lean_inc_ref(v_asciiVal_1981_);
lean_dec_ref(v_a_1804_);
v___x_1982_ = l_Lean_Parser_unicodeSymbol___redArg(v_val_1980_, v_asciiVal_1981_);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object* v_categories_1984_, lean_object* v_d_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1984_, v_d_1985_, v_a_1986_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object* v_categories_1989_, lean_object* v_d_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Parser_compileParserDescr(v_categories_1989_, v_d_1990_, v_a_1991_);
lean_dec_ref(v_a_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0(lean_object* v_categories_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1994_, v___y_1995_, v___y_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0___boxed(lean_object* v_categories_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_Parser_mkParserOfConstant___lam__0(v_categories_1999_, v___y_2000_, v___y_2001_);
lean_dec_ref(v___y_2001_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* v_categories_2004_, lean_object* v_constName_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___f_2008_; lean_object* v___x_2009_; 
v___f_2008_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserOfConstant___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2008_, 0, v_categories_2004_);
v___x_2009_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_2005_, v___f_2008_, v_a_2006_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___boxed(lean_object* v_categories_2010_, lean_object* v_constName_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Parser_mkParserOfConstant(v_categories_2010_, v_constName_2011_, v_a_2012_);
lean_dec_ref(v_a_2012_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2016_ = lean_box(0);
v___x_2017_ = lean_st_mk_ref(v___x_2016_);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object* v_hook_2021_){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2023_ = l_Lean_Parser_parserAttributeHooks;
v___x_2024_ = lean_st_ref_take(v___x_2023_);
v___x_2025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2025_, 0, v_hook_2021_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_st_ref_set(v___x_2023_, v___x_2025_);
v___x_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook___boxed(lean_object* v_hook_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_Parser_registerParserAttributeHook(v_hook_2028_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(lean_object* v_catName_2031_, lean_object* v_declName_2032_, uint8_t v_builtin_2033_, lean_object* v_as_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
if (lean_obj_tag(v_as_2034_) == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec(v_declName_2032_);
lean_dec(v_catName_2031_);
v___x_2038_ = lean_box(0);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
else
{
lean_object* v_head_2040_; lean_object* v_tail_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_head_2040_ = lean_ctor_get(v_as_2034_, 0);
lean_inc(v_head_2040_);
v_tail_2041_ = lean_ctor_get(v_as_2034_, 1);
lean_inc(v_tail_2041_);
lean_dec_ref(v_as_2034_);
v___x_2042_ = lean_box(v_builtin_2033_);
lean_inc(v___y_2036_);
lean_inc_ref(v___y_2035_);
lean_inc(v_declName_2032_);
lean_inc(v_catName_2031_);
v___x_2043_ = lean_apply_6(v_head_2040_, v_catName_2031_, v_declName_2032_, v___x_2042_, v___y_2035_, v___y_2036_, lean_box(0));
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_dec_ref(v___x_2043_);
v_as_2034_ = v_tail_2041_;
goto _start;
}
else
{
lean_dec(v_tail_2041_);
lean_dec(v_declName_2032_);
lean_dec(v_catName_2031_);
return v___x_2043_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0___boxed(lean_object* v_catName_2045_, lean_object* v_declName_2046_, lean_object* v_builtin_2047_, lean_object* v_as_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
uint8_t v_builtin_boxed_2052_; lean_object* v_res_2053_; 
v_builtin_boxed_2052_ = lean_unbox(v_builtin_2047_);
v_res_2053_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2045_, v_declName_2046_, v_builtin_boxed_2052_, v_as_2048_, v___y_2049_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object* v_catName_2054_, lean_object* v_declName_2055_, uint8_t v_builtin_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = l_Lean_Parser_parserAttributeHooks;
v___x_2061_ = lean_st_ref_get(v___x_2060_);
v___x_2062_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2054_, v_declName_2055_, v_builtin_2056_, v___x_2061_, v_a_2057_, v_a_2058_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object* v_catName_2063_, lean_object* v_declName_2064_, lean_object* v_builtin_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
uint8_t v_builtin_boxed_2069_; lean_object* v_res_2070_; 
v_builtin_boxed_2069_ = lean_unbox(v_builtin_2065_);
v_res_2070_ = l_Lean_Parser_runParserAttributeHooks(v_catName_2063_, v_declName_2064_, v_builtin_boxed_2069_, v_a_2066_, v_a_2067_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2071_, lean_object* v_decl_2072_, lean_object* v_stx_2073_, uint8_t v_x_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2073_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2078_) == 0)
{
uint8_t v___x_2079_; lean_object* v___x_2080_; 
lean_dec_ref(v___x_2078_);
v___x_2079_ = 1;
v___x_2080_ = l_Lean_Parser_runParserAttributeHooks(v___x_2071_, v_decl_2072_, v___x_2079_, v___y_2075_, v___y_2076_);
return v___x_2080_;
}
else
{
lean_dec(v_decl_2072_);
lean_dec(v___x_2071_);
return v___x_2078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2081_, lean_object* v_decl_2082_, lean_object* v_stx_2083_, lean_object* v_x_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
uint8_t v_x_1064__boxed_2088_; lean_object* v_res_2089_; 
v_x_1064__boxed_2088_ = lean_unbox(v_x_2084_);
v_res_2089_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2081_, v_decl_2082_, v_stx_2083_, v_x_1064__boxed_2088_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2089_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2090_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
lean_ctor_set(v___x_2095_, 2, v___x_2094_);
lean_ctor_set(v___x_2095_, 3, v___x_2094_);
lean_ctor_set(v___x_2095_, 4, v___x_2093_);
lean_ctor_set(v___x_2095_, 5, v___x_2093_);
lean_ctor_set(v___x_2095_, 6, v___x_2093_);
lean_ctor_set(v___x_2095_, 7, v___x_2093_);
lean_ctor_set(v___x_2095_, 8, v___x_2093_);
lean_ctor_set(v___x_2095_, 9, v___x_2093_);
return v___x_2095_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_unsigned_to_nat(32u);
v___x_2097_ = lean_mk_empty_array_with_capacity(v___x_2096_);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
return v___x_2098_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2099_ = ((size_t)5ULL);
v___x_2100_ = lean_unsigned_to_nat(0u);
v___x_2101_ = lean_unsigned_to_nat(32u);
v___x_2102_ = lean_mk_empty_array_with_capacity(v___x_2101_);
v___x_2103_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2104_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v___x_2102_);
lean_ctor_set(v___x_2104_, 2, v___x_2100_);
lean_ctor_set(v___x_2104_, 3, v___x_2100_);
lean_ctor_set_usize(v___x_2104_, 4, v___x_2099_);
return v___x_2104_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2105_ = lean_box(1);
v___x_2106_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2107_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v___x_2106_);
lean_ctor_set(v___x_2108_, 2, v___x_2105_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; lean_object* v_env_2114_; lean_object* v_options_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2113_ = lean_st_ref_get(v___y_2111_);
v_env_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc_ref(v_env_2114_);
lean_dec(v___x_2113_);
v_options_2115_ = lean_ctor_get(v___y_2110_, 2);
v___x_2116_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_2117_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2115_);
v___x_2118_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2118_, 0, v_env_2114_);
lean_ctor_set(v___x_2118_, 1, v___x_2116_);
lean_ctor_set(v___x_2118_, 2, v___x_2117_);
lean_ctor_set(v___x_2118_, 3, v_options_2115_);
v___x_2119_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v_msgData_2109_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_ref_2130_; lean_object* v___x_2131_; lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2140_; 
v_ref_2130_ = lean_ctor_get(v___y_2127_, 5);
v___x_2131_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msg_2126_, v___y_2127_, v___y_2128_);
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2140_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2140_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
lean_inc(v_ref_2130_);
v___x_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2136_, 0, v_ref_2130_);
lean_ctor_set(v___x_2136_, 1, v_a_2132_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set_tag(v___x_2134_, 1);
lean_ctor_set(v___x_2134_, 0, v___x_2136_);
v___x_2138_ = v___x_2134_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
return v_res_2145_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2148_ = l_Lean_stringToMessageData(v___x_2147_);
return v___x_2148_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2151_ = l_Lean_stringToMessageData(v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2152_, lean_object* v_decl_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2157_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2158_ = l_Lean_MessageData_ofName(v___x_2152_);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2159_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2161_, v___y_2154_, v___y_2155_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2163_, lean_object* v_decl_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2163_, v_decl_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v_decl_2164_);
return v_res_2168_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = lean_unsigned_to_nat(3646333153u);
v___x_2212_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2213_ = l_Lean_Name_num___override(v___x_2212_, v___x_2211_);
return v___x_2213_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2216_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2217_ = l_Lean_Name_str___override(v___x_2216_, v___x_2215_);
return v___x_2217_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2220_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2221_ = l_Lean_Name_str___override(v___x_2220_, v___x_2219_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = lean_unsigned_to_nat(2u);
v___x_2223_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2224_ = l_Lean_Name_num___override(v___x_2223_, v___x_2222_);
return v___x_2224_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2231_ = 0;
v___x_2232_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2233_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2234_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2235_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set(v___x_2235_, 1, v___x_2233_);
lean_ctor_set(v___x_2235_, 2, v___x_2232_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*3, v___x_2231_);
return v___x_2235_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2236_; lean_object* v___f_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___f_2236_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___f_2237_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2238_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v___f_2237_);
lean_ctor_set(v___x_2239_, 2, v___f_2236_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2242_ = l_Lean_registerBuiltinAttribute(v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2245_, lean_object* v_msg_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2246_, v___y_2247_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2251_, lean_object* v_msg_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(v_00_u03b1_2251_, v_msg_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2257_, lean_object* v_decl_2258_, lean_object* v_stx_2259_, uint8_t v_x_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2259_, v___y_2261_, v___y_2262_);
if (lean_obj_tag(v___x_2264_) == 0)
{
uint8_t v___x_2265_; lean_object* v___x_2266_; 
lean_dec_ref(v___x_2264_);
v___x_2265_ = 0;
v___x_2266_ = l_Lean_Parser_runParserAttributeHooks(v___x_2257_, v_decl_2258_, v___x_2265_, v___y_2261_, v___y_2262_);
return v___x_2266_;
}
else
{
lean_dec(v_decl_2258_);
lean_dec(v___x_2257_);
return v___x_2264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2267_, lean_object* v_decl_2268_, lean_object* v_stx_2269_, lean_object* v_x_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
uint8_t v_x_211__boxed_2274_; lean_object* v_res_2275_; 
v_x_211__boxed_2274_ = lean_unbox(v_x_2270_);
v_res_2275_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2267_, v_decl_2268_, v_stx_2269_, v_x_211__boxed_2274_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2276_, lean_object* v_decl_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2281_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2282_ = l_Lean_MessageData_ofName(v___x_2276_);
v___x_2283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2281_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2285_, v___y_2278_, v___y_2279_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2287_, lean_object* v_decl_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2287_, v_decl_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v_decl_2288_);
return v_res_2292_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2295_ = lean_unsigned_to_nat(3789407938u);
v___x_2296_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2297_ = l_Lean_Name_num___override(v___x_2296_, v___x_2295_);
return v___x_2297_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2299_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2300_ = l_Lean_Name_str___override(v___x_2299_, v___x_2298_);
return v___x_2300_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2302_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2303_ = l_Lean_Name_str___override(v___x_2302_, v___x_2301_);
return v___x_2303_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = lean_unsigned_to_nat(2u);
v___x_2305_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2306_ = l_Lean_Name_num___override(v___x_2305_, v___x_2304_);
return v___x_2306_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2313_ = 0;
v___x_2314_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2315_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2316_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2317_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v___x_2315_);
lean_ctor_set(v___x_2317_, 2, v___x_2314_);
lean_ctor_set_uint8(v___x_2317_, sizeof(void*)*3, v___x_2313_);
return v___x_2317_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2318_; lean_object* v___f_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___f_2318_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___f_2319_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2320_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
lean_ctor_set(v___x_2321_, 1, v___f_2319_);
lean_ctor_set(v___x_2321_, 2, v___f_2318_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2324_ = l_Lean_registerBuiltinAttribute(v___x_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object* v_s_2327_, lean_object* v_x_2328_, lean_object* v_a_2329_){
_start:
{
switch(lean_obj_tag(v_x_2328_))
{
case 0:
{
lean_object* v_val_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_s_2327_);
v_val_2331_ = lean_ctor_get(v_x_2328_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_x_2328_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2333_ = v_x_2328_;
v_isShared_2334_ = v_isSharedCheck_2339_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_val_2331_);
lean_dec(v_x_2328_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2339_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_val_2331_);
v___x_2336_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; 
v___x_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
return v___x_2337_;
}
}
}
case 1:
{
lean_object* v_val_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2348_; 
lean_dec_ref(v_s_2327_);
v_val_2340_ = lean_ctor_get(v_x_2328_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_x_2328_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2342_ = v_x_2328_;
v_isShared_2343_ = v_isSharedCheck_2348_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_val_2340_);
lean_dec(v_x_2328_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2348_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_val_2340_);
v___x_2345_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
return v___x_2346_;
}
}
}
case 2:
{
lean_object* v_catName_2349_; lean_object* v_declName_2350_; uint8_t v_behavior_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v_s_2327_);
v_catName_2349_ = lean_ctor_get(v_x_2328_, 0);
v_declName_2350_ = lean_ctor_get(v_x_2328_, 1);
v_behavior_2351_ = lean_ctor_get_uint8(v_x_2328_, sizeof(void*)*2);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_x_2328_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2353_ = v_x_2328_;
v_isShared_2354_ = v_isSharedCheck_2359_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_declName_2350_);
lean_inc(v_catName_2349_);
lean_dec(v_x_2328_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2359_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_catName_2349_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_declName_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, sizeof(void*)*2, v_behavior_2351_);
v___x_2356_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
return v___x_2357_;
}
}
}
default: 
{
lean_object* v_catName_2360_; lean_object* v_declName_2361_; lean_object* v_prio_2362_; lean_object* v_categories_2363_; lean_object* v___x_2364_; 
v_catName_2360_ = lean_ctor_get(v_x_2328_, 0);
lean_inc(v_catName_2360_);
v_declName_2361_ = lean_ctor_get(v_x_2328_, 1);
lean_inc_n(v_declName_2361_, 2);
v_prio_2362_ = lean_ctor_get(v_x_2328_, 2);
lean_inc(v_prio_2362_);
lean_dec_ref(v_x_2328_);
v_categories_2363_ = lean_ctor_get(v_s_2327_, 2);
lean_inc_ref(v_categories_2363_);
lean_dec_ref(v_s_2327_);
v___x_2364_ = l_Lean_Parser_mkParserOfConstant(v_categories_2363_, v_declName_2361_, v_a_2329_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2376_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2367_ = v___x_2364_;
v_isShared_2368_ = v_isSharedCheck_2376_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2364_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2376_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v_fst_2369_; lean_object* v_snd_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; lean_object* v___x_2374_; 
v_fst_2369_ = lean_ctor_get(v_a_2365_, 0);
lean_inc(v_fst_2369_);
v_snd_2370_ = lean_ctor_get(v_a_2365_, 1);
lean_inc(v_snd_2370_);
lean_dec(v_a_2365_);
v___x_2371_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_2371_, 0, v_catName_2360_);
lean_ctor_set(v___x_2371_, 1, v_declName_2361_);
lean_ctor_set(v___x_2371_, 2, v_snd_2370_);
lean_ctor_set(v___x_2371_, 3, v_prio_2362_);
v___x_2372_ = lean_unbox(v_fst_2369_);
lean_dec(v_fst_2369_);
lean_ctor_set_uint8(v___x_2371_, sizeof(void*)*4, v___x_2372_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2371_);
v___x_2374_ = v___x_2367_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2371_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_prio_2362_);
lean_dec(v_declName_2361_);
lean_dec(v_catName_2360_);
v_a_2377_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2364_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2364_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object* v_s_2385_, lean_object* v_x_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(v_s_2385_, v_x_2386_, v_a_2387_);
lean_dec_ref(v_a_2387_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(uint8_t v_x_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___y_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_x_2393_, lean_object* v___y_2394_){
_start:
{
uint8_t v_x_27__boxed_2395_; lean_object* v_res_2396_; 
v_x_27__boxed_2395_ = lean_unbox(v_x_2393_);
v_res_2396_ = l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v_x_27__boxed_2395_, v___y_2394_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v___y_2397_){
_start:
{
lean_inc_ref(v___y_2397_);
return v___y_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v___y_2398_);
lean_dec_ref(v___y_2398_);
return v_res_2399_;
}
}
static lean_object* _init_l_Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2410_; lean_object* v___f_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___f_2410_ = ((lean_object*)(l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___f_2411_ = ((lean_object*)(l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2412_ = ((lean_object*)(l_Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2413_ = ((lean_object*)(l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2414_ = ((lean_object*)(l_Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2415_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed), 1, 0);
v___x_2416_ = ((lean_object*)(l_Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2417_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
lean_ctor_set(v___x_2417_, 1, v___x_2415_);
lean_ctor_set(v___x_2417_, 2, v___x_2414_);
lean_ctor_set(v___x_2417_, 3, v___x_2413_);
lean_ctor_set(v___x_2417_, 4, v___x_2412_);
lean_ctor_set(v___x_2417_, 5, v___f_2411_);
lean_ctor_set(v___x_2417_, 6, v___f_2410_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_obj_once(&l_Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_);
v___x_2420_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object* v_env_2423_, lean_object* v_catName_2424_){
_start:
{
lean_object* v___x_2425_; lean_object* v_ext_2426_; lean_object* v_toEnvExtension_2427_; lean_object* v_asyncMode_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v_categories_2431_; lean_object* v___x_2432_; 
v___x_2425_ = l_Lean_Parser_parserExtension;
v_ext_2426_ = lean_ctor_get(v___x_2425_, 1);
v_toEnvExtension_2427_ = lean_ctor_get(v_ext_2426_, 0);
v_asyncMode_2428_ = lean_ctor_get(v_toEnvExtension_2427_, 2);
v___x_2429_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2430_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2429_, v___x_2425_, v_env_2423_, v_asyncMode_2428_);
v_categories_2431_ = lean_ctor_get(v___x_2430_, 2);
lean_inc_ref(v_categories_2431_);
lean_dec(v___x_2430_);
v___x_2432_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2431_, v_catName_2424_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object* v_env_2433_, lean_object* v_catName_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_Parser_getParserCategory_x3f(v_env_2433_, v_catName_2434_);
lean_dec(v_catName_2434_);
return v_res_2435_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object* v_env_2436_, lean_object* v_catName_2437_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Lean_Parser_getParserCategory_x3f(v_env_2436_, v_catName_2437_);
if (lean_obj_tag(v___x_2438_) == 0)
{
uint8_t v___x_2439_; 
v___x_2439_ = 0;
return v___x_2439_;
}
else
{
uint8_t v___x_2440_; 
lean_dec_ref(v___x_2438_);
v___x_2440_ = 1;
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object* v_env_2441_, lean_object* v_catName_2442_){
_start:
{
uint8_t v_res_2443_; lean_object* v_r_2444_; 
v_res_2443_ = l_Lean_Parser_isParserCategory(v_env_2441_, v_catName_2442_);
lean_dec(v_catName_2442_);
v_r_2444_ = lean_box(v_res_2443_);
return v_r_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object* v_env_2445_, lean_object* v_catName_2446_, lean_object* v_declName_2447_, uint8_t v_behavior_2448_){
_start:
{
uint8_t v___x_2449_; 
lean_inc_ref(v_env_2445_);
v___x_2449_ = l_Lean_Parser_isParserCategory(v_env_2445_, v_catName_2446_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2450_ = l_Lean_Parser_parserExtension;
v___x_2451_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2451_, 0, v_catName_2446_);
lean_ctor_set(v___x_2451_, 1, v_declName_2447_);
lean_ctor_set_uint8(v___x_2451_, sizeof(void*)*2, v_behavior_2448_);
v___x_2452_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2450_, v_env_2445_, v___x_2451_);
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
else
{
lean_object* v___x_2454_; 
lean_dec(v_declName_2447_);
lean_dec_ref(v_env_2445_);
v___x_2454_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_2446_);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* v_env_2455_, lean_object* v_catName_2456_, lean_object* v_declName_2457_, lean_object* v_behavior_2458_){
_start:
{
uint8_t v_behavior_boxed_2459_; lean_object* v_res_2460_; 
v_behavior_boxed_2459_ = lean_unbox(v_behavior_2458_);
v_res_2460_ = l_Lean_Parser_addParserCategory(v_env_2455_, v_catName_2456_, v_declName_2457_, v_behavior_boxed_2459_);
return v_res_2460_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object* v_env_2461_, lean_object* v_catName_2462_){
_start:
{
lean_object* v___x_2463_; lean_object* v_ext_2464_; lean_object* v_toEnvExtension_2465_; lean_object* v_asyncMode_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v_categories_2469_; lean_object* v___x_2470_; 
v___x_2463_ = l_Lean_Parser_parserExtension;
v_ext_2464_ = lean_ctor_get(v___x_2463_, 1);
v_toEnvExtension_2465_ = lean_ctor_get(v_ext_2464_, 0);
v_asyncMode_2466_ = lean_ctor_get(v_toEnvExtension_2465_, 2);
v___x_2467_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2468_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2467_, v___x_2463_, v_env_2461_, v_asyncMode_2466_);
v_categories_2469_ = lean_ctor_get(v___x_2468_, 2);
lean_inc_ref(v_categories_2469_);
lean_dec(v___x_2468_);
v___x_2470_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2469_, v_catName_2462_);
if (lean_obj_tag(v___x_2470_) == 0)
{
uint8_t v___x_2471_; 
v___x_2471_ = 0;
return v___x_2471_;
}
else
{
lean_object* v_val_2472_; uint8_t v_behavior_2473_; 
v_val_2472_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_val_2472_);
lean_dec_ref(v___x_2470_);
v_behavior_2473_ = lean_ctor_get_uint8(v_val_2472_, sizeof(void*)*3);
lean_dec(v_val_2472_);
return v_behavior_2473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object* v_env_2474_, lean_object* v_catName_2475_){
_start:
{
uint8_t v_res_2476_; lean_object* v_r_2477_; 
v_res_2476_ = l_Lean_Parser_leadingIdentBehavior(v_env_2474_, v_catName_2475_);
lean_dec(v_catName_2475_);
v_r_2477_ = lean_box(v_res_2476_);
return v_r_2477_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(lean_object* v_x_2478_, lean_object* v_x_2479_){
_start:
{
if (lean_obj_tag(v_x_2479_) == 0)
{
return v_x_2478_;
}
else
{
lean_object* v_head_2480_; lean_object* v_tail_2481_; lean_object* v___x_2482_; 
v_head_2480_ = lean_ctor_get(v_x_2479_, 0);
lean_inc_n(v_head_2480_, 2);
v_tail_2481_ = lean_ctor_get(v_x_2479_, 1);
lean_inc(v_tail_2481_);
lean_dec_ref(v_x_2479_);
v___x_2482_ = l_Lean_Data_Trie_insert___redArg(v_x_2478_, v_head_2480_, v_head_2480_);
lean_dec(v_head_2480_);
v_x_2478_ = v___x_2482_;
v_x_2479_ = v_tail_2481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__0(lean_object* v_info_2484_, lean_object* v_ctx_2485_){
_start:
{
lean_object* v_toInputContext_2486_; lean_object* v_toParserModuleContext_2487_; lean_object* v_toCacheableParserContext_2488_; lean_object* v_tokens_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2500_; 
v_toInputContext_2486_ = lean_ctor_get(v_ctx_2485_, 0);
v_toParserModuleContext_2487_ = lean_ctor_get(v_ctx_2485_, 1);
v_toCacheableParserContext_2488_ = lean_ctor_get(v_ctx_2485_, 2);
v_tokens_2489_ = lean_ctor_get(v_ctx_2485_, 3);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_ctx_2485_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2491_ = v_ctx_2485_;
v_isShared_2492_ = v_isSharedCheck_2500_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_tokens_2489_);
lean_inc(v_toCacheableParserContext_2488_);
lean_inc(v_toParserModuleContext_2487_);
lean_inc(v_toInputContext_2486_);
lean_dec(v_ctx_2485_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2500_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v_collectTokens_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2498_; 
v_collectTokens_2493_ = lean_ctor_get(v_info_2484_, 0);
lean_inc_ref(v_collectTokens_2493_);
lean_dec_ref(v_info_2484_);
v___x_2494_ = lean_box(0);
v___x_2495_ = lean_apply_1(v_collectTokens_2493_, v___x_2494_);
v___x_2496_ = l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(v_tokens_2489_, v___x_2495_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 3, v___x_2496_);
v___x_2498_ = v___x_2491_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_toInputContext_2486_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_toParserModuleContext_2487_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_toCacheableParserContext_2488_);
lean_ctor_set(v_reuseFailAlloc_2499_, 3, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1(lean_object* v_categories_2501_, lean_object* v_declName_2502_, lean_object* v___x_2503_, lean_object* v_ctx_2504_, lean_object* v_s_2505_, lean_object* v_evalFallback_x3f_2506_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_Parser_mkParserOfConstant(v_categories_2501_, v_declName_2502_, v___x_2503_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v_snd_2510_; lean_object* v_info_2511_; lean_object* v_fn_2512_; lean_object* v___f_2513_; lean_object* v___x_2514_; 
lean_dec(v_evalFallback_x3f_2506_);
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref(v___x_2508_);
v_snd_2510_ = lean_ctor_get(v_a_2509_, 1);
lean_inc(v_snd_2510_);
lean_dec(v_a_2509_);
v_info_2511_ = lean_ctor_get(v_snd_2510_, 0);
lean_inc_ref(v_info_2511_);
v_fn_2512_ = lean_ctor_get(v_snd_2510_, 1);
lean_inc_ref(v_fn_2512_);
lean_dec(v_snd_2510_);
v___f_2513_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__0), 2, 1);
lean_closure_set(v___f_2513_, 0, v_info_2511_);
v___x_2514_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2513_, v_fn_2512_, v_ctx_2504_, v_s_2505_);
return v___x_2514_;
}
else
{
if (lean_obj_tag(v_evalFallback_x3f_2506_) == 1)
{
lean_object* v_val_2515_; lean_object* v___x_2516_; 
lean_dec_ref(v___x_2508_);
v_val_2515_ = lean_ctor_get(v_evalFallback_x3f_2506_, 0);
lean_inc(v_val_2515_);
lean_dec_ref(v_evalFallback_x3f_2506_);
v___x_2516_ = lean_apply_2(v_val_2515_, v_ctx_2504_, v_s_2505_);
return v___x_2516_;
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; lean_object* v___x_2521_; 
lean_dec(v_evalFallback_x3f_2506_);
lean_dec_ref(v_ctx_2504_);
v_a_2517_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2517_);
lean_dec_ref(v___x_2508_);
v___x_2518_ = lean_io_error_to_string(v_a_2517_);
v___x_2519_ = lean_box(0);
v___x_2520_ = 1;
v___x_2521_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2505_, v___x_2518_, v___x_2519_, v___x_2520_);
return v___x_2521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed(lean_object* v_categories_2522_, lean_object* v_declName_2523_, lean_object* v___x_2524_, lean_object* v_ctx_2525_, lean_object* v_s_2526_, lean_object* v_evalFallback_x3f_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_Parser_evalParserConstUnsafe___lam__1(v_categories_2522_, v_declName_2523_, v___x_2524_, v_ctx_2525_, v_s_2526_, v_evalFallback_x3f_2527_);
lean_dec_ref(v___x_2524_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* v_declName_2530_, lean_object* v_evalFallback_x3f_2531_, lean_object* v_ctx_2532_, lean_object* v_s_2533_){
_start:
{
lean_object* v_toParserModuleContext_2534_; lean_object* v_env_2535_; lean_object* v_options_2536_; lean_object* v___x_2537_; lean_object* v_ext_2538_; lean_object* v_toEnvExtension_2539_; lean_object* v_asyncMode_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v_categories_2543_; lean_object* v___x_2544_; lean_object* v___f_2545_; lean_object* v___x_2546_; 
v_toParserModuleContext_2534_ = lean_ctor_get(v_ctx_2532_, 1);
v_env_2535_ = lean_ctor_get(v_toParserModuleContext_2534_, 0);
v_options_2536_ = lean_ctor_get(v_toParserModuleContext_2534_, 1);
v___x_2537_ = l_Lean_Parser_parserExtension;
v_ext_2538_ = lean_ctor_get(v___x_2537_, 1);
v_toEnvExtension_2539_ = lean_ctor_get(v_ext_2538_, 0);
v_asyncMode_2540_ = lean_ctor_get(v_toEnvExtension_2539_, 2);
v___x_2541_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref_n(v_env_2535_, 2);
v___x_2542_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2541_, v___x_2537_, v_env_2535_, v_asyncMode_2540_);
v_categories_2543_ = lean_ctor_get(v___x_2542_, 2);
lean_inc_ref(v_categories_2543_);
lean_dec(v___x_2542_);
lean_inc_ref(v_options_2536_);
v___x_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2544_, 0, v_env_2535_);
lean_ctor_set(v___x_2544_, 1, v_options_2536_);
v___f_2545_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2545_, 0, v_categories_2543_);
lean_closure_set(v___f_2545_, 1, v_declName_2530_);
lean_closure_set(v___f_2545_, 2, v___x_2544_);
lean_closure_set(v___f_2545_, 3, v_ctx_2532_);
lean_closure_set(v___f_2545_, 4, v_s_2533_);
lean_closure_set(v___f_2545_, 5, v_evalFallback_x3f_2531_);
v___x_2546_ = l_unsafeBaseIO___redArg(v___f_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object* v_name_2547_, lean_object* v_decl_2548_, lean_object* v_ref_2549_){
_start:
{
lean_object* v_defValue_2551_; lean_object* v_descr_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2579_; 
v_defValue_2551_ = lean_ctor_get(v_decl_2548_, 0);
v_descr_2552_ = lean_ctor_get(v_decl_2548_, 1);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_decl_2548_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2554_ = v_decl_2548_;
v_isShared_2555_ = v_isSharedCheck_2579_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_descr_2552_);
lean_inc(v_defValue_2551_);
lean_dec(v_decl_2548_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2579_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2556_ = lean_alloc_ctor(1, 0, 1);
v___x_2557_ = lean_unbox(v_defValue_2551_);
lean_ctor_set_uint8(v___x_2556_, 0, v___x_2557_);
lean_inc_n(v_name_2547_, 2);
v___x_2558_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2558_, 0, v_name_2547_);
lean_ctor_set(v___x_2558_, 1, v_ref_2549_);
lean_ctor_set(v___x_2558_, 2, v___x_2556_);
lean_ctor_set(v___x_2558_, 3, v_descr_2552_);
v___x_2559_ = lean_register_option(v_name_2547_, v___x_2558_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2569_; 
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; 
v_unused_2570_ = lean_ctor_get(v___x_2559_, 0);
lean_dec(v_unused_2570_);
v___x_2561_ = v___x_2559_;
v_isShared_2562_ = v_isSharedCheck_2569_;
goto v_resetjp_2560_;
}
else
{
lean_dec(v___x_2559_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2569_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 1, v_defValue_2551_);
lean_ctor_set(v___x_2554_, 0, v_name_2547_);
v___x_2564_ = v___x_2554_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_name_2547_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_defValue_2551_);
v___x_2564_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
lean_object* v___x_2566_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2564_);
v___x_2566_ = v___x_2561_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_del_object(v___x_2554_);
lean_dec(v_defValue_2551_);
lean_dec(v_name_2547_);
v_a_2571_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2559_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2559_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2580_, lean_object* v_decl_2581_, lean_object* v_ref_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_Option_register___at___00Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v_name_2580_, v_decl_2581_, v_ref_2582_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2601_ = ((lean_object*)(l_Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2602_ = ((lean_object*)(l_Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2603_ = ((lean_object*)(l_Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2604_ = l_Lean_Option_register___at___00Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v___x_2601_, v___x_2602_, v___x_2603_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object* v_a_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(lean_object* v_o_2610_, lean_object* v_k_2611_, uint8_t v_v_2612_){
_start:
{
lean_object* v_map_2613_; uint8_t v_hasTrace_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2628_; 
v_map_2613_ = lean_ctor_get(v_o_2610_, 0);
v_hasTrace_2614_ = lean_ctor_get_uint8(v_o_2610_, sizeof(void*)*1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_o_2610_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2616_ = v_o_2610_;
v_isShared_2617_ = v_isSharedCheck_2628_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_map_2613_);
lean_dec(v_o_2610_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2628_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2618_, 0, v_v_2612_);
lean_inc(v_k_2611_);
v___x_2619_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2611_, v___x_2618_, v_map_2613_);
if (v_hasTrace_2614_ == 0)
{
lean_object* v___x_2620_; uint8_t v___x_2621_; lean_object* v___x_2623_; 
v___x_2620_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_2621_ = l_Lean_Name_isPrefixOf(v___x_2620_, v_k_2611_);
lean_dec(v_k_2611_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2619_);
v___x_2623_ = v___x_2616_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2619_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_ctor_set_uint8(v___x_2623_, sizeof(void*)*1, v___x_2621_);
return v___x_2623_;
}
}
else
{
lean_object* v___x_2626_; 
lean_dec(v_k_2611_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2619_);
v___x_2626_ = v___x_2616_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2627_, sizeof(void*)*1, v_hasTrace_2614_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___boxed(lean_object* v_o_2629_, lean_object* v_k_2630_, lean_object* v_v_2631_){
_start:
{
uint8_t v_v_boxed_2632_; lean_object* v_res_2633_; 
v_v_boxed_2632_ = lean_unbox(v_v_2631_);
v_res_2633_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_o_2629_, v_k_2630_, v_v_boxed_2632_);
return v_res_2633_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(lean_object* v_opts_2634_, lean_object* v_opt_2635_){
_start:
{
lean_object* v_name_2636_; lean_object* v_defValue_2637_; lean_object* v_map_2638_; lean_object* v___x_2639_; 
v_name_2636_ = lean_ctor_get(v_opt_2635_, 0);
v_defValue_2637_ = lean_ctor_get(v_opt_2635_, 1);
v_map_2638_ = lean_ctor_get(v_opts_2634_, 0);
v___x_2639_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2638_, v_name_2636_);
if (lean_obj_tag(v___x_2639_) == 0)
{
uint8_t v___x_2640_; 
v___x_2640_ = lean_unbox(v_defValue_2637_);
return v___x_2640_;
}
else
{
lean_object* v_val_2641_; 
v_val_2641_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_val_2641_);
lean_dec_ref(v___x_2639_);
if (lean_obj_tag(v_val_2641_) == 1)
{
uint8_t v_v_2642_; 
v_v_2642_ = lean_ctor_get_uint8(v_val_2641_, 0);
lean_dec_ref(v_val_2641_);
return v_v_2642_;
}
else
{
uint8_t v___x_2643_; 
lean_dec(v_val_2641_);
v___x_2643_ = lean_unbox(v_defValue_2637_);
return v___x_2643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1___boxed(lean_object* v_opts_2644_, lean_object* v_opt_2645_){
_start:
{
uint8_t v_res_2646_; lean_object* v_r_2647_; 
v_res_2646_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_opts_2644_, v_opt_2645_);
lean_dec_ref(v_opt_2645_);
lean_dec_ref(v_opts_2644_);
v_r_2647_ = lean_box(v_res_2646_);
return v_r_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0(lean_object* v_ctx_2653_){
_start:
{
lean_object* v_toParserModuleContext_2654_; lean_object* v_toInputContext_2655_; lean_object* v_toCacheableParserContext_2656_; lean_object* v_tokens_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2678_; 
v_toParserModuleContext_2654_ = lean_ctor_get(v_ctx_2653_, 1);
v_toInputContext_2655_ = lean_ctor_get(v_ctx_2653_, 0);
v_toCacheableParserContext_2656_ = lean_ctor_get(v_ctx_2653_, 2);
v_tokens_2657_ = lean_ctor_get(v_ctx_2653_, 3);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_ctx_2653_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2659_ = v_ctx_2653_;
v_isShared_2660_ = v_isSharedCheck_2678_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_tokens_2657_);
lean_inc(v_toCacheableParserContext_2656_);
lean_inc(v_toParserModuleContext_2654_);
lean_inc(v_toInputContext_2655_);
lean_dec(v_ctx_2653_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2678_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v_env_2661_; lean_object* v_options_2662_; lean_object* v_currNamespace_2663_; lean_object* v_openDecls_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2677_; 
v_env_2661_ = lean_ctor_get(v_toParserModuleContext_2654_, 0);
v_options_2662_ = lean_ctor_get(v_toParserModuleContext_2654_, 1);
v_currNamespace_2663_ = lean_ctor_get(v_toParserModuleContext_2654_, 2);
v_openDecls_2664_ = lean_ctor_get(v_toParserModuleContext_2654_, 3);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_toParserModuleContext_2654_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2666_ = v_toParserModuleContext_2654_;
v_isShared_2667_ = v_isSharedCheck_2677_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_openDecls_2664_);
lean_inc(v_currNamespace_2663_);
lean_inc(v_options_2662_);
lean_inc(v_env_2661_);
lean_dec(v_toParserModuleContext_2654_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2677_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; uint8_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2668_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_2669_ = 0;
v___x_2670_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_2662_, v___x_2668_, v___x_2669_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2670_);
v___x_2672_ = v___x_2666_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_env_2661_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v_currNamespace_2663_);
lean_ctor_set(v_reuseFailAlloc_2676_, 3, v_openDecls_2664_);
v___x_2672_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2674_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___x_2672_);
v___x_2674_ = v___x_2659_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_toInputContext_2655_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2675_, 2, v_toCacheableParserContext_2656_);
lean_ctor_set(v_reuseFailAlloc_2675_, 3, v_tokens_2657_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object* v_fn_2679_, lean_object* v_declName_2680_, lean_object* v___f_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v_toParserModuleContext_2684_; lean_object* v_toCacheableParserContext_2685_; uint8_t v___y_2687_; lean_object* v_quotDepth_2699_; uint8_t v_suppressInsideQuot_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v_toParserModuleContext_2684_ = lean_ctor_get(v___y_2682_, 1);
v_toCacheableParserContext_2685_ = lean_ctor_get(v___y_2682_, 2);
v_quotDepth_2699_ = lean_ctor_get(v_toCacheableParserContext_2685_, 1);
v_suppressInsideQuot_2700_ = lean_ctor_get_uint8(v_toCacheableParserContext_2685_, sizeof(void*)*4);
v___x_2701_ = lean_unsigned_to_nat(0u);
v___x_2702_ = lean_nat_dec_lt(v___x_2701_, v_quotDepth_2699_);
if (v___x_2702_ == 0)
{
v___y_2687_ = v___x_2702_;
goto v___jp_2686_;
}
else
{
if (v_suppressInsideQuot_2700_ == 0)
{
v___y_2687_ = v___x_2702_;
goto v___jp_2686_;
}
else
{
lean_object* v___x_2703_; 
lean_dec_ref(v___f_2681_);
lean_dec(v_declName_2680_);
v___x_2703_ = lean_apply_2(v_fn_2679_, v___y_2682_, v___y_2683_);
return v___x_2703_;
}
}
v___jp_2686_:
{
if (v___y_2687_ == 0)
{
lean_object* v___x_2688_; 
lean_dec_ref(v___f_2681_);
lean_dec(v_declName_2680_);
v___x_2688_ = lean_apply_2(v_fn_2679_, v___y_2682_, v___y_2683_);
return v___x_2688_;
}
else
{
lean_object* v_env_2689_; lean_object* v_options_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
v_env_2689_ = lean_ctor_get(v_toParserModuleContext_2684_, 0);
v_options_2690_ = lean_ctor_get(v_toParserModuleContext_2684_, 1);
v___x_2691_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_2692_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_2690_, v___x_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
lean_dec_ref(v___f_2681_);
lean_dec(v_declName_2680_);
v___x_2693_ = lean_apply_2(v_fn_2679_, v___y_2682_, v___y_2683_);
return v___x_2693_;
}
else
{
uint8_t v___x_2694_; 
lean_inc(v_declName_2680_);
lean_inc_ref(v_env_2689_);
v___x_2694_ = l_Lean_Environment_contains(v_env_2689_, v_declName_2680_, v___x_2692_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; 
lean_dec_ref(v___f_2681_);
lean_dec(v_declName_2680_);
v___x_2695_ = lean_apply_2(v_fn_2679_, v___y_2682_, v___y_2683_);
return v___x_2695_;
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_fn_2679_);
v___x_2697_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_2697_, 0, v_declName_2680_);
lean_closure_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2681_, v___x_2697_, v___y_2682_, v___y_2683_);
return v___x_2698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object* v_declName_2705_, lean_object* v_p_2706_){
_start:
{
lean_object* v_info_2707_; lean_object* v_fn_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2717_; 
v_info_2707_ = lean_ctor_get(v_p_2706_, 0);
v_fn_2708_ = lean_ctor_get(v_p_2706_, 1);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_p_2706_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2710_ = v_p_2706_;
v_isShared_2711_ = v_isSharedCheck_2717_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_fn_2708_);
lean_inc(v_info_2707_);
lean_dec(v_p_2706_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2717_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___f_2712_; lean_object* v___f_2713_; lean_object* v___x_2715_; 
v___f_2712_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___closed__0));
v___f_2713_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__1), 5, 3);
lean_closure_set(v___f_2713_, 0, v_fn_2708_);
lean_closure_set(v___f_2713_, 1, v_declName_2705_);
lean_closure_set(v___f_2713_, 2, v___f_2712_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 1, v___f_2713_);
v___x_2715_ = v___x_2710_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_info_2707_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v___f_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object* v_catName_2718_, lean_object* v_declName_2719_, uint8_t v_leading_2720_, lean_object* v_p_2721_, lean_object* v_prio_2722_){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v_p_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2724_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_2725_ = lean_st_ref_get(v___x_2724_);
lean_inc_n(v_declName_2719_, 2);
v_p_2726_ = l_Lean_Parser_evalInsideQuot(v_declName_2719_, v_p_2721_);
lean_inc_ref(v_p_2726_);
v___x_2727_ = l_Lean_Parser_addParser(v___x_2725_, v_catName_2718_, v_declName_2719_, v_leading_2720_, v_p_2726_, v_prio_2722_);
v___x_2728_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_2727_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v_info_2733_; lean_object* v_collectKinds_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref(v___x_2728_);
v___x_2730_ = lean_st_ref_set(v___x_2724_, v_a_2729_);
v___x_2731_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_2732_ = lean_st_ref_take(v___x_2731_);
v_info_2733_ = lean_ctor_get(v_p_2726_, 0);
lean_inc_ref(v_info_2733_);
lean_dec_ref(v_p_2726_);
v_collectKinds_2734_ = lean_ctor_get(v_info_2733_, 1);
lean_inc_ref(v_collectKinds_2734_);
v___x_2735_ = lean_apply_1(v_collectKinds_2734_, v___x_2732_);
v___x_2736_ = lean_st_ref_set(v___x_2731_, v___x_2735_);
v___x_2737_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_2733_, v_declName_2719_);
return v___x_2737_;
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec_ref(v_p_2726_);
lean_dec(v_declName_2719_);
v_a_2738_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2728_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2728_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* v_catName_2746_, lean_object* v_declName_2747_, lean_object* v_leading_2748_, lean_object* v_p_2749_, lean_object* v_prio_2750_, lean_object* v_a_2751_){
_start:
{
uint8_t v_leading_boxed_2752_; lean_object* v_res_2753_; 
v_leading_boxed_2752_ = lean_unbox(v_leading_2748_);
v_res_2753_ = l_Lean_Parser_addBuiltinParser(v_catName_2746_, v_declName_2747_, v_leading_boxed_2752_, v_p_2749_, v_prio_2750_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* v_catName_2754_, lean_object* v_declName_2755_, lean_object* v_p_2756_, lean_object* v_prio_2757_){
_start:
{
uint8_t v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = 1;
v___x_2760_ = l_Lean_Parser_addBuiltinParser(v_catName_2754_, v_declName_2755_, v___x_2759_, v_p_2756_, v_prio_2757_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object* v_catName_2761_, lean_object* v_declName_2762_, lean_object* v_p_2763_, lean_object* v_prio_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_Parser_addBuiltinLeadingParser(v_catName_2761_, v_declName_2762_, v_p_2763_, v_prio_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* v_catName_2767_, lean_object* v_declName_2768_, lean_object* v_p_2769_, lean_object* v_prio_2770_){
_start:
{
uint8_t v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = 0;
v___x_2773_ = l_Lean_Parser_addBuiltinParser(v_catName_2767_, v_declName_2768_, v___x_2772_, v_p_2769_, v_prio_2770_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object* v_catName_2774_, lean_object* v_declName_2775_, lean_object* v_p_2776_, lean_object* v_prio_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Parser_addBuiltinTrailingParser(v_catName_2774_, v_declName_2775_, v_p_2776_, v_prio_2777_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object* v_kind_2780_){
_start:
{
uint8_t v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = 1;
lean_inc(v_kind_2780_);
v___x_2782_ = l_Lean_Name_toString(v_kind_2780_, v___x_2781_);
v___x_2783_ = l_Lean_Parser_mkAntiquot(v___x_2782_, v_kind_2780_, v___x_2781_, v___x_2781_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object* v_kind_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v___x_2787_; lean_object* v_fn_2788_; lean_object* v___x_2789_; 
v___x_2787_ = l_Lean_Parser_mkCategoryAntiquotParser(v_kind_2784_);
v_fn_2788_ = lean_ctor_get(v___x_2787_, 1);
lean_inc_ref(v_fn_2788_);
lean_dec_ref(v___x_2787_);
v___x_2789_ = lean_apply_2(v_fn_2788_, v_a_2785_, v_a_2786_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl___lam__0(lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___x_2793_; lean_object* v_fn_2794_; lean_object* v___x_2795_; 
v___x_2793_ = l_Lean_Parser_mkCategoryAntiquotParser(v___y_2790_);
v_fn_2794_ = lean_ctor_get(v___x_2793_, 1);
lean_inc_ref(v_fn_2794_);
lean_dec_ref(v___x_2793_);
v___x_2795_ = lean_apply_2(v_fn_2794_, v___y_2791_, v___y_2792_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* v_catName_2804_, lean_object* v_ctx_2805_, lean_object* v_s_2806_){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; uint8_t v___x_2810_; lean_object* v___y_2812_; 
v___x_2807_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2808_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__1));
v___x_2809_ = lean_name_eq(v_catName_2804_, v___x_2808_);
v___x_2810_ = 1;
if (v___x_2809_ == 0)
{
v___y_2812_ = v_catName_2804_;
goto v___jp_2811_;
}
else
{
lean_object* v___x_2834_; 
lean_dec(v_catName_2804_);
v___x_2834_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__5));
v___y_2812_ = v___x_2834_;
goto v___jp_2811_;
}
v___jp_2811_:
{
lean_object* v_toParserModuleContext_2813_; lean_object* v_env_2814_; lean_object* v___x_2815_; lean_object* v_ext_2816_; lean_object* v_toEnvExtension_2817_; lean_object* v_asyncMode_2818_; lean_object* v___x_2819_; lean_object* v_categories_2820_; lean_object* v___x_2821_; 
v_toParserModuleContext_2813_ = lean_ctor_get(v_ctx_2805_, 1);
v_env_2814_ = lean_ctor_get(v_toParserModuleContext_2813_, 0);
v___x_2815_ = l_Lean_Parser_parserExtension;
v_ext_2816_ = lean_ctor_get(v___x_2815_, 1);
v_toEnvExtension_2817_ = lean_ctor_get(v_ext_2816_, 0);
v_asyncMode_2818_ = lean_ctor_get(v_toEnvExtension_2817_, 2);
lean_inc_ref(v_env_2814_);
v___x_2819_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2807_, v___x_2815_, v_env_2814_, v_asyncMode_2818_);
v_categories_2820_ = lean_ctor_get(v___x_2819_, 2);
lean_inc_ref(v_categories_2820_);
lean_dec(v___x_2819_);
v___x_2821_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2820_, v___y_2812_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec_ref(v_ctx_2805_);
v___x_2822_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__2));
v___x_2823_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2812_, v___x_2810_);
v___x_2824_ = lean_string_append(v___x_2822_, v___x_2823_);
lean_dec_ref(v___x_2823_);
v___x_2825_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__3));
v___x_2826_ = lean_string_append(v___x_2824_, v___x_2825_);
v___x_2827_ = lean_box(0);
v___x_2828_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2806_, v___x_2826_, v___x_2827_, v___x_2810_);
return v___x_2828_;
}
else
{
lean_object* v_val_2829_; lean_object* v_tables_2830_; uint8_t v_behavior_2831_; lean_object* v___f_2832_; lean_object* v___x_2833_; 
v_val_2829_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_val_2829_);
lean_dec_ref(v___x_2821_);
v_tables_2830_ = lean_ctor_get(v_val_2829_, 2);
lean_inc_ref(v_tables_2830_);
v_behavior_2831_ = lean_ctor_get_uint8(v_val_2829_, sizeof(void*)*3);
lean_dec(v_val_2829_);
lean_inc(v___y_2812_);
v___f_2832_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl___lam__0), 3, 1);
lean_closure_set(v___f_2832_, 0, v___y_2812_);
v___x_2833_ = l_Lean_Parser_prattParser(v___y_2812_, v_tables_2830_, v_behavior_2831_, v___f_2832_, v_ctx_2805_, v_s_2806_);
return v___x_2833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2837_ = l_Lean_Parser_categoryParserFnRef;
v___x_2838_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_));
v___x_2839_ = lean_st_ref_set(v___x_2837_, v___x_2838_);
v___x_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object* v_a_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
return v_res_2842_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2843_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0);
v___x_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
return v___x_2845_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
v___x_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object* v_ext_2848_, lean_object* v_b_2849_, uint8_t v_kind_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_currNamespace_2854_; lean_object* v___x_2855_; lean_object* v_env_2856_; lean_object* v_nextMacroScope_2857_; lean_object* v_ngen_2858_; lean_object* v_auxDeclNGen_2859_; lean_object* v_traceState_2860_; lean_object* v_messages_2861_; lean_object* v_infoState_2862_; lean_object* v_snapshotTasks_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2875_; 
v_currNamespace_2854_ = lean_ctor_get(v___y_2851_, 6);
v___x_2855_ = lean_st_ref_take(v___y_2852_);
v_env_2856_ = lean_ctor_get(v___x_2855_, 0);
v_nextMacroScope_2857_ = lean_ctor_get(v___x_2855_, 1);
v_ngen_2858_ = lean_ctor_get(v___x_2855_, 2);
v_auxDeclNGen_2859_ = lean_ctor_get(v___x_2855_, 3);
v_traceState_2860_ = lean_ctor_get(v___x_2855_, 4);
v_messages_2861_ = lean_ctor_get(v___x_2855_, 6);
v_infoState_2862_ = lean_ctor_get(v___x_2855_, 7);
v_snapshotTasks_2863_ = lean_ctor_get(v___x_2855_, 8);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; 
v_unused_2876_ = lean_ctor_get(v___x_2855_, 5);
lean_dec(v_unused_2876_);
v___x_2865_ = v___x_2855_;
v_isShared_2866_ = v_isSharedCheck_2875_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_snapshotTasks_2863_);
lean_inc(v_infoState_2862_);
lean_inc(v_messages_2861_);
lean_inc(v_traceState_2860_);
lean_inc(v_auxDeclNGen_2859_);
lean_inc(v_ngen_2858_);
lean_inc(v_nextMacroScope_2857_);
lean_inc(v_env_2856_);
lean_dec(v___x_2855_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2875_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2870_; 
lean_inc(v_currNamespace_2854_);
v___x_2867_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2856_, v_ext_2848_, v_b_2849_, v_kind_2850_, v_currNamespace_2854_);
v___x_2868_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 5, v___x_2868_);
lean_ctor_set(v___x_2865_, 0, v___x_2867_);
v___x_2870_ = v___x_2865_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_nextMacroScope_2857_);
lean_ctor_set(v_reuseFailAlloc_2874_, 2, v_ngen_2858_);
lean_ctor_set(v_reuseFailAlloc_2874_, 3, v_auxDeclNGen_2859_);
lean_ctor_set(v_reuseFailAlloc_2874_, 4, v_traceState_2860_);
lean_ctor_set(v_reuseFailAlloc_2874_, 5, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2874_, 6, v_messages_2861_);
lean_ctor_set(v_reuseFailAlloc_2874_, 7, v_infoState_2862_);
lean_ctor_set(v_reuseFailAlloc_2874_, 8, v_snapshotTasks_2863_);
v___x_2870_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = lean_st_ref_set(v___y_2852_, v___x_2870_);
v___x_2872_ = lean_box(0);
v___x_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
return v___x_2873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object* v_ext_2877_, lean_object* v_b_2878_, lean_object* v_kind_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
uint8_t v_kind_boxed_2883_; lean_object* v_res_2884_; 
v_kind_boxed_2883_ = lean_unbox(v_kind_2879_);
v_res_2884_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2877_, v_b_2878_, v_kind_boxed_2883_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object* v_00_u03b1_2885_, lean_object* v_00_u03b2_2886_, lean_object* v_00_u03c3_2887_, lean_object* v_ext_2888_, lean_object* v_b_2889_, uint8_t v_kind_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2888_, v_b_2889_, v_kind_2890_, v___y_2891_, v___y_2892_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object* v_00_u03b1_2895_, lean_object* v_00_u03b2_2896_, lean_object* v_00_u03c3_2897_, lean_object* v_ext_2898_, lean_object* v_b_2899_, lean_object* v_kind_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
uint8_t v_kind_boxed_2904_; lean_object* v_res_2905_; 
v_kind_boxed_2904_ = lean_unbox(v_kind_2900_);
v_res_2905_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(v_00_u03b1_2895_, v_00_u03b2_2896_, v_00_u03c3_2897_, v_ext_2898_, v_b_2899_, v_kind_boxed_2904_, v___y_2901_, v___y_2902_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object* v_x_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
if (lean_obj_tag(v_x_2906_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_a_2910_ = lean_ctor_get(v_x_2906_, 0);
lean_inc(v_a_2910_);
lean_dec_ref(v_x_2906_);
v___x_2911_ = l_Lean_stringToMessageData(v_a_2910_);
v___x_2912_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2911_, v___y_2907_, v___y_2908_);
return v___x_2912_;
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
v_a_2913_ = lean_ctor_get(v_x_2906_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_x_2906_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v_x_2906_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v_x_2906_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set_tag(v___x_2915_, 0);
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object* v_x_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2921_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object* v_tk_2926_, uint8_t v_kind_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v___x_2931_; lean_object* v_env_2932_; lean_object* v___x_2933_; lean_object* v_ext_2934_; lean_object* v_toEnvExtension_2935_; lean_object* v_asyncMode_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v_tokens_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2931_ = lean_st_ref_get(v_a_2929_);
v_env_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc_ref(v_env_2932_);
lean_dec(v___x_2931_);
v___x_2933_ = l_Lean_Parser_parserExtension;
v_ext_2934_ = lean_ctor_get(v___x_2933_, 1);
v_toEnvExtension_2935_ = lean_ctor_get(v_ext_2934_, 0);
v_asyncMode_2936_ = lean_ctor_get(v_toEnvExtension_2935_, 2);
v___x_2937_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2938_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2937_, v___x_2933_, v_env_2932_, v_asyncMode_2936_);
v_tokens_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc_ref(v_tokens_2939_);
lean_dec(v___x_2938_);
lean_inc_ref(v_tk_2926_);
v___x_2940_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_2939_, v_tk_2926_);
v___x_2941_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v___x_2940_, v_a_2928_, v_a_2929_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
lean_dec_ref(v___x_2941_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_tk_2926_);
v___x_2943_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_2933_, v___x_2942_, v_kind_2927_, v_a_2928_, v_a_2929_);
return v___x_2943_;
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_dec_ref(v_tk_2926_);
v_a_2944_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2941_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2941_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object* v_tk_2952_, lean_object* v_kind_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
uint8_t v_kind_boxed_2957_; lean_object* v_res_2958_; 
v_kind_boxed_2957_ = lean_unbox(v_kind_2953_);
v_res_2958_ = l_Lean_Parser_addToken(v_tk_2952_, v_kind_boxed_2957_, v_a_2954_, v_a_2955_);
lean_dec(v_a_2955_);
lean_dec_ref(v_a_2954_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_object* v_00_u03b1_2959_, lean_object* v_x_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2960_, v___y_2961_, v___y_2962_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___boxed(lean_object* v_00_u03b1_2965_, lean_object* v_x_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(v_00_u03b1_2965_, v_x_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object* v_env_2971_, lean_object* v_k_2972_){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = l_Lean_Parser_parserExtension;
v___x_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2974_, 0, v_k_2972_);
v___x_2975_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2973_, v_env_2971_, v___x_2974_);
return v___x_2975_;
}
}
static uint8_t _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0(void){
_start:
{
lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2976_ = lean_box(0);
v___x_2977_ = lean_internal_is_stage0(v___x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object* v_env_2978_, lean_object* v_k_2979_){
_start:
{
lean_object* v___x_2980_; lean_object* v_ext_2981_; lean_object* v_toEnvExtension_2982_; lean_object* v_asyncMode_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v_kinds_2986_; uint8_t v___x_2987_; 
v___x_2980_ = l_Lean_Parser_parserExtension;
v_ext_2981_ = lean_ctor_get(v___x_2980_, 1);
v_toEnvExtension_2982_ = lean_ctor_get(v_ext_2981_, 0);
v_asyncMode_2983_ = lean_ctor_get(v_toEnvExtension_2982_, 2);
v___x_2984_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_2978_);
v___x_2985_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2984_, v___x_2980_, v_env_2978_, v_asyncMode_2983_);
v_kinds_2986_ = lean_ctor_get(v___x_2985_, 1);
lean_inc_ref(v_kinds_2986_);
lean_dec(v___x_2985_);
v___x_2987_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_2986_, v_k_2979_);
lean_dec_ref(v_kinds_2986_);
if (v___x_2987_ == 0)
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_uint8_once(&l_Lean_Parser_isValidSyntaxNodeKind___closed__0, &l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once, _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0);
if (v___x_2988_ == 0)
{
lean_dec(v_k_2979_);
lean_dec_ref(v_env_2978_);
return v___x_2988_;
}
else
{
uint8_t v___x_2989_; 
v___x_2989_ = l_Lean_Environment_contains(v_env_2978_, v_k_2979_, v___x_2988_);
return v___x_2989_;
}
}
else
{
lean_dec(v_k_2979_);
lean_dec_ref(v_env_2978_);
return v___x_2987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* v_env_2990_, lean_object* v_k_2991_){
_start:
{
uint8_t v_res_2992_; lean_object* v_r_2993_; 
v_res_2992_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_2990_, v_k_2991_);
v_r_2993_ = lean_box(v_res_2992_);
return v_r_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds___lam__0(lean_object* v_ks_2994_, lean_object* v_k_2995_, lean_object* v_x_2996_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2997_, 0, v_k_2995_);
lean_ctor_set(v___x_2997_, 1, v_ks_2994_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2998_, lean_object* v_keys_2999_, lean_object* v_vals_3000_, lean_object* v_i_3001_, lean_object* v_acc_3002_){
_start:
{
lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3003_ = lean_array_get_size(v_keys_2999_);
v___x_3004_ = lean_nat_dec_lt(v_i_3001_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_dec(v_i_3001_);
lean_dec(v_f_2998_);
return v_acc_3002_;
}
else
{
lean_object* v_k_3005_; lean_object* v_v_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_k_3005_ = lean_array_fget_borrowed(v_keys_2999_, v_i_3001_);
v_v_3006_ = lean_array_fget_borrowed(v_vals_3000_, v_i_3001_);
lean_inc(v_f_2998_);
lean_inc(v_v_3006_);
lean_inc(v_k_3005_);
v___x_3007_ = lean_apply_3(v_f_2998_, v_acc_3002_, v_k_3005_, v_v_3006_);
v___x_3008_ = lean_unsigned_to_nat(1u);
v___x_3009_ = lean_nat_add(v_i_3001_, v___x_3008_);
lean_dec(v_i_3001_);
v_i_3001_ = v___x_3009_;
v_acc_3002_ = v___x_3007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3011_, lean_object* v_keys_3012_, lean_object* v_vals_3013_, lean_object* v_i_3014_, lean_object* v_acc_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3011_, v_keys_3012_, v_vals_3013_, v_i_3014_, v_acc_3015_);
lean_dec_ref(v_vals_3013_);
lean_dec_ref(v_keys_3012_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3017_, lean_object* v_x_3018_, lean_object* v_x_3019_){
_start:
{
if (lean_obj_tag(v_x_3018_) == 0)
{
lean_object* v_es_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; uint8_t v___x_3023_; 
v_es_3020_ = lean_ctor_get(v_x_3018_, 0);
v___x_3021_ = lean_unsigned_to_nat(0u);
v___x_3022_ = lean_array_get_size(v_es_3020_);
v___x_3023_ = lean_nat_dec_lt(v___x_3021_, v___x_3022_);
if (v___x_3023_ == 0)
{
lean_dec(v_f_3017_);
return v_x_3019_;
}
else
{
uint8_t v___x_3024_; 
v___x_3024_ = lean_nat_dec_le(v___x_3022_, v___x_3022_);
if (v___x_3024_ == 0)
{
if (v___x_3023_ == 0)
{
lean_dec(v_f_3017_);
return v_x_3019_;
}
else
{
size_t v___x_3025_; size_t v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = ((size_t)0ULL);
v___x_3026_ = lean_usize_of_nat(v___x_3022_);
v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3017_, v_es_3020_, v___x_3025_, v___x_3026_, v_x_3019_);
return v___x_3027_;
}
}
else
{
size_t v___x_3028_; size_t v___x_3029_; lean_object* v___x_3030_; 
v___x_3028_ = ((size_t)0ULL);
v___x_3029_ = lean_usize_of_nat(v___x_3022_);
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3017_, v_es_3020_, v___x_3028_, v___x_3029_, v_x_3019_);
return v___x_3030_;
}
}
}
else
{
lean_object* v_ks_3031_; lean_object* v_vs_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v_ks_3031_ = lean_ctor_get(v_x_3018_, 0);
v_vs_3032_ = lean_ctor_get(v_x_3018_, 1);
v___x_3033_ = lean_unsigned_to_nat(0u);
v___x_3034_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3017_, v_ks_3031_, v_vs_3032_, v___x_3033_, v_x_3019_);
return v___x_3034_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3035_, lean_object* v_as_3036_, size_t v_i_3037_, size_t v_stop_3038_, lean_object* v_b_3039_){
_start:
{
lean_object* v___y_3041_; uint8_t v___x_3045_; 
v___x_3045_ = lean_usize_dec_eq(v_i_3037_, v_stop_3038_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; 
v___x_3046_ = lean_array_uget_borrowed(v_as_3036_, v_i_3037_);
switch(lean_obj_tag(v___x_3046_))
{
case 0:
{
lean_object* v_key_3047_; lean_object* v_val_3048_; lean_object* v___x_3049_; 
v_key_3047_ = lean_ctor_get(v___x_3046_, 0);
v_val_3048_ = lean_ctor_get(v___x_3046_, 1);
lean_inc(v_f_3035_);
lean_inc(v_val_3048_);
lean_inc(v_key_3047_);
v___x_3049_ = lean_apply_3(v_f_3035_, v_b_3039_, v_key_3047_, v_val_3048_);
v___y_3041_ = v___x_3049_;
goto v___jp_3040_;
}
case 1:
{
lean_object* v_node_3050_; lean_object* v___x_3051_; 
v_node_3050_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_f_3035_);
v___x_3051_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3035_, v_node_3050_, v_b_3039_);
v___y_3041_ = v___x_3051_;
goto v___jp_3040_;
}
default: 
{
v___y_3041_ = v_b_3039_;
goto v___jp_3040_;
}
}
}
else
{
lean_dec(v_f_3035_);
return v_b_3039_;
}
v___jp_3040_:
{
size_t v___x_3042_; size_t v___x_3043_; 
v___x_3042_ = ((size_t)1ULL);
v___x_3043_ = lean_usize_add(v_i_3037_, v___x_3042_);
v_i_3037_ = v___x_3043_;
v_b_3039_ = v___y_3041_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3052_, lean_object* v_as_3053_, lean_object* v_i_3054_, lean_object* v_stop_3055_, lean_object* v_b_3056_){
_start:
{
size_t v_i_boxed_3057_; size_t v_stop_boxed_3058_; lean_object* v_res_3059_; 
v_i_boxed_3057_ = lean_unbox_usize(v_i_3054_);
lean_dec(v_i_3054_);
v_stop_boxed_3058_ = lean_unbox_usize(v_stop_3055_);
lean_dec(v_stop_3055_);
v_res_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3052_, v_as_3053_, v_i_boxed_3057_, v_stop_boxed_3058_, v_b_3056_);
lean_dec_ref(v_as_3053_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3060_, lean_object* v_x_3061_, lean_object* v_x_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3060_, v_x_3061_, v_x_3062_);
lean_dec_ref(v_x_3061_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object* v_f_3064_, lean_object* v_x1_3065_, lean_object* v_x2_3066_, lean_object* v_x3_3067_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_apply_3(v_f_3064_, v_x1_3065_, v_x2_3066_, v_x3_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object* v_map_3069_, lean_object* v_f_3070_, lean_object* v_init_3071_){
_start:
{
lean_object* v___f_3072_; lean_object* v___x_3073_; 
v___f_3072_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3072_, 0, v_f_3070_);
v___x_3073_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v___f_3072_, v_map_3069_, v_init_3071_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object* v_map_3074_, lean_object* v_f_3075_, lean_object* v_init_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3074_, v_f_3075_, v_init_3076_);
lean_dec_ref(v_map_3074_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* v_env_3079_){
_start:
{
lean_object* v___x_3080_; lean_object* v_ext_3081_; lean_object* v_toEnvExtension_3082_; lean_object* v_asyncMode_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v_kinds_3086_; lean_object* v___f_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3080_ = l_Lean_Parser_parserExtension;
v_ext_3081_ = lean_ctor_get(v___x_3080_, 1);
v_toEnvExtension_3082_ = lean_ctor_get(v_ext_3081_, 0);
v_asyncMode_3083_ = lean_ctor_get(v_toEnvExtension_3082_, 2);
v___x_3084_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3085_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3084_, v___x_3080_, v_env_3079_, v_asyncMode_3083_);
v_kinds_3086_ = lean_ctor_get(v___x_3085_, 1);
lean_inc_ref(v_kinds_3086_);
lean_dec(v___x_3085_);
v___f_3087_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKinds___closed__0));
v___x_3088_ = lean_box(0);
v___x_3089_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_kinds_3086_, v___f_3087_, v___x_3088_);
lean_dec_ref(v_kinds_3086_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object* v_00_u03c3_3090_, lean_object* v_00_u03b2_3091_, lean_object* v_map_3092_, lean_object* v_f_3093_, lean_object* v_init_3094_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3092_, v_f_3093_, v_init_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object* v_00_u03c3_3096_, lean_object* v_00_u03b2_3097_, lean_object* v_map_3098_, lean_object* v_f_3099_, lean_object* v_init_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(v_00_u03c3_3096_, v_00_u03b2_3097_, v_map_3098_, v_f_3099_, v_init_3100_);
lean_dec_ref(v_map_3098_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object* v_map_3102_, lean_object* v_f_3103_, lean_object* v_init_3104_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3103_, v_map_3102_, v_init_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object* v_map_3106_, lean_object* v_f_3107_, lean_object* v_init_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(v_map_3106_, v_f_3107_, v_init_3108_);
lean_dec_ref(v_map_3106_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object* v_00_u03c3_3110_, lean_object* v_00_u03b2_3111_, lean_object* v_map_3112_, lean_object* v_f_3113_, lean_object* v_init_3114_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3113_, v_map_3112_, v_init_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3116_, lean_object* v_00_u03b2_3117_, lean_object* v_map_3118_, lean_object* v_f_3119_, lean_object* v_init_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(v_00_u03c3_3116_, v_00_u03b2_3117_, v_map_3118_, v_f_3119_, v_init_3120_);
lean_dec_ref(v_map_3118_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3122_, lean_object* v_00_u03b1_3123_, lean_object* v_00_u03b2_3124_, lean_object* v_f_3125_, lean_object* v_x_3126_, lean_object* v_x_3127_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3125_, v_x_3126_, v_x_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3129_, lean_object* v_00_u03b1_3130_, lean_object* v_00_u03b2_3131_, lean_object* v_f_3132_, lean_object* v_x_3133_, lean_object* v_x_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(v_00_u03c3_3129_, v_00_u03b1_3130_, v_00_u03b2_3131_, v_f_3132_, v_x_3133_, v_x_3134_);
lean_dec_ref(v_x_3133_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3136_, lean_object* v_00_u03b2_3137_, lean_object* v_00_u03c3_3138_, lean_object* v_f_3139_, lean_object* v_as_3140_, size_t v_i_3141_, size_t v_stop_3142_, lean_object* v_b_3143_){
_start:
{
lean_object* v___x_3144_; 
v___x_3144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3139_, v_as_3140_, v_i_3141_, v_stop_3142_, v_b_3143_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3145_, lean_object* v_00_u03b2_3146_, lean_object* v_00_u03c3_3147_, lean_object* v_f_3148_, lean_object* v_as_3149_, lean_object* v_i_3150_, lean_object* v_stop_3151_, lean_object* v_b_3152_){
_start:
{
size_t v_i_boxed_3153_; size_t v_stop_boxed_3154_; lean_object* v_res_3155_; 
v_i_boxed_3153_ = lean_unbox_usize(v_i_3150_);
lean_dec(v_i_3150_);
v_stop_boxed_3154_ = lean_unbox_usize(v_stop_3151_);
lean_dec(v_stop_3151_);
v_res_3155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3145_, v_00_u03b2_3146_, v_00_u03c3_3147_, v_f_3148_, v_as_3149_, v_i_boxed_3153_, v_stop_boxed_3154_, v_b_3152_);
lean_dec_ref(v_as_3149_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3156_, lean_object* v_00_u03b1_3157_, lean_object* v_00_u03b2_3158_, lean_object* v_f_3159_, lean_object* v_keys_3160_, lean_object* v_vals_3161_, lean_object* v_heq_3162_, lean_object* v_i_3163_, lean_object* v_acc_3164_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3159_, v_keys_3160_, v_vals_3161_, v_i_3163_, v_acc_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3166_, lean_object* v_00_u03b1_3167_, lean_object* v_00_u03b2_3168_, lean_object* v_f_3169_, lean_object* v_keys_3170_, lean_object* v_vals_3171_, lean_object* v_heq_3172_, lean_object* v_i_3173_, lean_object* v_acc_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3166_, v_00_u03b1_3167_, v_00_u03b2_3168_, v_f_3169_, v_keys_3170_, v_vals_3171_, v_heq_3172_, v_i_3173_, v_acc_3174_);
lean_dec_ref(v_vals_3171_);
lean_dec_ref(v_keys_3170_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* v_env_3176_){
_start:
{
lean_object* v___x_3177_; lean_object* v_ext_3178_; lean_object* v_toEnvExtension_3179_; lean_object* v_asyncMode_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v_tokens_3183_; 
v___x_3177_ = l_Lean_Parser_parserExtension;
v_ext_3178_ = lean_ctor_get(v___x_3177_, 1);
v_toEnvExtension_3179_ = lean_ctor_get(v_ext_3178_, 0);
v_asyncMode_3180_ = lean_ctor_get(v_toEnvExtension_3179_, 2);
v___x_3181_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3182_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3181_, v___x_3177_, v_env_3176_, v_asyncMode_3180_);
v_tokens_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc_ref(v_tokens_3183_);
lean_dec(v___x_3182_);
return v_tokens_3183_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__8));
v___x_3209_ = l_Lean_mkAtom(v___x_3208_);
return v___x_3209_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__10, &l_Lean_Parser_mkInputContext___auto__1___closed__10_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__10);
v___x_3211_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3212_ = lean_array_push(v___x_3211_, v___x_3210_);
return v___x_3212_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3224_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3225_ = lean_array_push(v___x_3224_, v___x_3223_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3226_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__15, &l_Lean_Parser_mkInputContext___auto__1___closed__15_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__15);
v___x_3227_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__13));
v___x_3228_ = lean_box(2);
v___x_3229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
lean_ctor_set(v___x_3229_, 1, v___x_3227_);
lean_ctor_set(v___x_3229_, 2, v___x_3226_);
return v___x_3229_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__16, &l_Lean_Parser_mkInputContext___auto__1___closed__16_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__16);
v___x_3231_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__11, &l_Lean_Parser_mkInputContext___auto__1___closed__11_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__11);
v___x_3232_ = lean_array_push(v___x_3231_, v___x_3230_);
return v___x_3232_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3233_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3234_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__17, &l_Lean_Parser_mkInputContext___auto__1___closed__17_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__17);
v___x_3235_ = lean_array_push(v___x_3234_, v___x_3233_);
return v___x_3235_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3236_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3237_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__18, &l_Lean_Parser_mkInputContext___auto__1___closed__18_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__18);
v___x_3238_ = lean_array_push(v___x_3237_, v___x_3236_);
return v___x_3238_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3240_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__19, &l_Lean_Parser_mkInputContext___auto__1___closed__19_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__19);
v___x_3241_ = lean_array_push(v___x_3240_, v___x_3239_);
return v___x_3241_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3243_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__20, &l_Lean_Parser_mkInputContext___auto__1___closed__20_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__20);
v___x_3244_ = lean_array_push(v___x_3243_, v___x_3242_);
return v___x_3244_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3245_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__21, &l_Lean_Parser_mkInputContext___auto__1___closed__21_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__21);
v___x_3246_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__9));
v___x_3247_ = lean_box(2);
v___x_3248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3247_);
lean_ctor_set(v___x_3248_, 1, v___x_3246_);
lean_ctor_set(v___x_3248_, 2, v___x_3245_);
return v___x_3248_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3249_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__22, &l_Lean_Parser_mkInputContext___auto__1___closed__22_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__22);
v___x_3250_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3251_ = lean_array_push(v___x_3250_, v___x_3249_);
return v___x_3251_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3252_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__23, &l_Lean_Parser_mkInputContext___auto__1___closed__23_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__23);
v___x_3253_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3254_ = lean_box(2);
v___x_3255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
lean_ctor_set(v___x_3255_, 1, v___x_3253_);
lean_ctor_set(v___x_3255_, 2, v___x_3252_);
return v___x_3255_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3256_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__24, &l_Lean_Parser_mkInputContext___auto__1___closed__24_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__24);
v___x_3257_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3258_ = lean_array_push(v___x_3257_, v___x_3256_);
return v___x_3258_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3259_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__25, &l_Lean_Parser_mkInputContext___auto__1___closed__25_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__25);
v___x_3260_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3261_ = lean_box(2);
v___x_3262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v___x_3260_);
lean_ctor_set(v___x_3262_, 2, v___x_3259_);
return v___x_3262_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__26, &l_Lean_Parser_mkInputContext___auto__1___closed__26_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__26);
v___x_3264_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3265_ = lean_array_push(v___x_3264_, v___x_3263_);
return v___x_3265_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3266_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__27, &l_Lean_Parser_mkInputContext___auto__1___closed__27_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__27);
v___x_3267_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3268_ = lean_box(2);
v___x_3269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
lean_ctor_set(v___x_3269_, 1, v___x_3267_);
lean_ctor_set(v___x_3269_, 2, v___x_3266_);
return v___x_3269_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1(void){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__28, &l_Lean_Parser_mkInputContext___auto__1___closed__28_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__28);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object* v_input_3271_, lean_object* v_fileName_3272_, uint8_t v_normalizeLineEndings_3273_, lean_object* v_endPos_3274_){
_start:
{
lean_object* v_fst_3276_; lean_object* v_snd_3277_; lean_object* v_text_3283_; 
v_text_3283_ = l_Lean_FileMap_ofString(v_input_3271_);
if (v_normalizeLineEndings_3273_ == 0)
{
v_fst_3276_ = v_text_3283_;
v_snd_3277_ = v_endPos_3274_;
goto v___jp_3275_;
}
else
{
lean_object* v_source_3284_; lean_object* v_endPos_x27_3285_; lean_object* v___x_3286_; lean_object* v_text_3287_; lean_object* v___x_3288_; 
v_source_3284_ = lean_ctor_get(v_text_3283_, 0);
lean_inc_ref(v_source_3284_);
v_endPos_x27_3285_ = l_Lean_FileMap_toPosition(v_text_3283_, v_endPos_3274_);
lean_dec(v_endPos_3274_);
v___x_3286_ = l_String_crlfToLf(v_source_3284_);
lean_dec_ref(v_source_3284_);
v_text_3287_ = l_Lean_FileMap_ofString(v___x_3286_);
v___x_3288_ = l_Lean_FileMap_ofPosition(v_text_3287_, v_endPos_x27_3285_);
v_fst_3276_ = v_text_3287_;
v_snd_3277_ = v___x_3288_;
goto v___jp_3275_;
}
v___jp_3275_:
{
lean_object* v_source_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; 
v_source_3278_ = lean_ctor_get(v_fst_3276_, 0);
lean_inc_ref(v_source_3278_);
v___x_3279_ = lean_string_utf8_byte_size(v_source_3278_);
v___x_3280_ = lean_nat_dec_le(v_snd_3277_, v___x_3279_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; 
lean_dec(v_snd_3277_);
v___x_3281_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3281_, 0, v_source_3278_);
lean_ctor_set(v___x_3281_, 1, v_fileName_3272_);
lean_ctor_set(v___x_3281_, 2, v_fst_3276_);
lean_ctor_set(v___x_3281_, 3, v___x_3279_);
return v___x_3281_;
}
else
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3282_, 0, v_source_3278_);
lean_ctor_set(v___x_3282_, 1, v_fileName_3272_);
lean_ctor_set(v___x_3282_, 2, v_fst_3276_);
lean_ctor_set(v___x_3282_, 3, v_snd_3277_);
return v___x_3282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object* v_input_3289_, lean_object* v_fileName_3290_, lean_object* v_normalizeLineEndings_3291_, lean_object* v_endPos_3292_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3293_; lean_object* v_res_3294_; 
v_normalizeLineEndings_boxed_3293_ = lean_unbox(v_normalizeLineEndings_3291_);
v_res_3294_ = l_Lean_Parser_mkInputContext___redArg(v_input_3289_, v_fileName_3290_, v_normalizeLineEndings_boxed_3293_, v_endPos_3292_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object* v_input_3295_, lean_object* v_fileName_3296_, uint8_t v_normalizeLineEndings_3297_, lean_object* v_endPos_3298_, lean_object* v_endPos__valid_3299_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Lean_Parser_mkInputContext___redArg(v_input_3295_, v_fileName_3296_, v_normalizeLineEndings_3297_, v_endPos_3298_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object* v_input_3301_, lean_object* v_fileName_3302_, lean_object* v_normalizeLineEndings_3303_, lean_object* v_endPos_3304_, lean_object* v_endPos__valid_3305_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3306_; lean_object* v_res_3307_; 
v_normalizeLineEndings_boxed_3306_ = lean_unbox(v_normalizeLineEndings_3303_);
v_res_3307_ = l_Lean_Parser_mkInputContext(v_input_3301_, v_fileName_3302_, v_normalizeLineEndings_boxed_3306_, v_endPos_3304_, v_endPos__valid_3305_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* v_input_3310_){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3311_ = l_Lean_Parser_SyntaxStack_empty;
v___x_3312_ = lean_unsigned_to_nat(0u);
v___x_3313_ = l_Lean_Parser_initCacheForInput(v_input_3310_);
v___x_3314_ = lean_box(0);
v___x_3315_ = ((lean_object*)(l_Lean_Parser_mkParserState___closed__0));
v___x_3316_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3311_);
lean_ctor_set(v___x_3316_, 1, v___x_3312_);
lean_ctor_set(v___x_3316_, 2, v___x_3312_);
lean_ctor_set(v___x_3316_, 3, v___x_3313_);
lean_ctor_set(v___x_3316_, 4, v___x_3314_);
lean_ctor_set(v___x_3316_, 5, v___x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* v_input_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_Parser_mkParserState(v_input_3317_);
lean_dec_ref(v_input_3317_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* v_env_3321_, lean_object* v_catName_3322_, lean_object* v_input_3323_, lean_object* v_fileName_3324_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v_p_3327_; uint8_t v___x_3328_; lean_object* v___x_3329_; lean_object* v_ictx_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v_s_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3325_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__0));
v___x_3326_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 1);
lean_closure_set(v___x_3326_, 0, v_catName_3322_);
v_p_3327_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_3327_, 0, v___x_3325_);
lean_closure_set(v_p_3327_, 1, v___x_3326_);
v___x_3328_ = 1;
v___x_3329_ = lean_string_utf8_byte_size(v_input_3323_);
lean_inc_ref(v_input_3323_);
v_ictx_3330_ = l_Lean_Parser_mkInputContext___redArg(v_input_3323_, v_fileName_3324_, v___x_3328_, v___x_3329_);
v___x_3331_ = l_Lean_Options_empty;
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_box(0);
lean_inc_ref(v_env_3321_);
v___x_3334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3334_, 0, v_env_3321_);
lean_ctor_set(v___x_3334_, 1, v___x_3331_);
lean_ctor_set(v___x_3334_, 2, v___x_3332_);
lean_ctor_set(v___x_3334_, 3, v___x_3333_);
v___x_3335_ = l_Lean_Parser_getTokenTable(v_env_3321_);
v___x_3336_ = l_Lean_Parser_mkParserState(v_input_3323_);
lean_dec_ref(v_input_3323_);
lean_inc_ref(v_ictx_3330_);
v_s_3337_ = l_Lean_Parser_ParserFn_run(v_p_3327_, v_ictx_3330_, v___x_3334_, v___x_3335_, v___x_3336_);
lean_inc_ref(v_s_3337_);
v___x_3338_ = l_Lean_Parser_ParserState_allErrors(v_s_3337_);
v___x_3339_ = lean_array_get_size(v___x_3338_);
lean_dec_ref(v___x_3338_);
v___x_3340_ = lean_unsigned_to_nat(0u);
v___x_3341_ = lean_nat_dec_eq(v___x_3339_, v___x_3340_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3342_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3330_, v_s_3337_);
v___x_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
return v___x_3343_;
}
else
{
lean_object* v_stxStack_3344_; lean_object* v_pos_3345_; uint8_t v___x_3346_; 
v_stxStack_3344_ = lean_ctor_get(v_s_3337_, 0);
lean_inc_ref(v_stxStack_3344_);
v_pos_3345_ = lean_ctor_get(v_s_3337_, 2);
lean_inc(v_pos_3345_);
v___x_3346_ = l_Lean_Parser_InputContext_atEnd(v_ictx_3330_, v_pos_3345_);
lean_dec(v_pos_3345_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
lean_dec_ref(v_stxStack_3344_);
v___x_3347_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__1));
v___x_3348_ = l_Lean_Parser_ParserState_mkError(v_s_3337_, v___x_3347_);
v___x_3349_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3330_, v___x_3348_);
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
return v___x_3350_;
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
lean_dec_ref(v_s_3337_);
lean_dec_ref(v_ictx_3330_);
v___x_3351_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3344_);
lean_dec_ref(v_stxStack_3344_);
v___x_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
return v___x_3352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* v_addFnName_3353_, lean_object* v_catName_3354_, lean_object* v_declName_3355_, lean_object* v_prio_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v_val_3372_; lean_object* v___x_3373_; 
v___x_3360_ = lean_box(0);
v___x_3361_ = l_Lean_mkConst(v_addFnName_3353_, v___x_3360_);
v___x_3362_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_catName_3354_);
lean_inc_n(v_declName_3355_, 2);
v___x_3363_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3355_);
v___x_3364_ = l_Lean_mkConst(v_declName_3355_, v___x_3360_);
v___x_3365_ = l_Lean_mkRawNatLit(v_prio_3356_);
v___x_3366_ = lean_unsigned_to_nat(4u);
v___x_3367_ = lean_mk_empty_array_with_capacity(v___x_3366_);
v___x_3368_ = lean_array_push(v___x_3367_, v___x_3362_);
v___x_3369_ = lean_array_push(v___x_3368_, v___x_3363_);
v___x_3370_ = lean_array_push(v___x_3369_, v___x_3364_);
v___x_3371_ = lean_array_push(v___x_3370_, v___x_3365_);
v_val_3372_ = l_Lean_mkAppN(v___x_3361_, v___x_3371_);
lean_dec_ref(v___x_3371_);
v___x_3373_ = l_Lean_declareBuiltin(v_declName_3355_, v_val_3372_, v_a_3357_, v_a_3358_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object* v_addFnName_3374_, lean_object* v_catName_3375_, lean_object* v_declName_3376_, lean_object* v_prio_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3374_, v_catName_3375_, v_declName_3376_, v_prio_3377_, v_a_3378_, v_a_3379_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* v_catName_3387_, lean_object* v_declName_3388_, lean_object* v_prio_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = ((lean_object*)(l_Lean_Parser_declareLeadingBuiltinParser___closed__1));
v___x_3394_ = l_Lean_Parser_declareBuiltinParser(v___x_3393_, v_catName_3387_, v_declName_3388_, v_prio_3389_, v_a_3390_, v_a_3391_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object* v_catName_3395_, lean_object* v_declName_3396_, lean_object* v_prio_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3395_, v_declName_3396_, v_prio_3397_, v_a_3398_, v_a_3399_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* v_catName_3407_, lean_object* v_declName_3408_, lean_object* v_prio_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = ((lean_object*)(l_Lean_Parser_declareTrailingBuiltinParser___closed__1));
v___x_3414_ = l_Lean_Parser_declareBuiltinParser(v___x_3413_, v_catName_3407_, v_declName_3408_, v_prio_3409_, v_a_3410_, v_a_3411_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object* v_catName_3415_, lean_object* v_declName_3416_, lean_object* v_prio_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3415_, v_declName_3416_, v_prio_3417_, v_a_3418_, v_a_3419_);
lean_dec(v_a_3419_);
lean_dec_ref(v_a_3418_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* v_args_3428_){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; uint8_t v___x_3431_; 
v___x_3429_ = l_Lean_Syntax_getNumArgs(v_args_3428_);
v___x_3430_ = lean_unsigned_to_nat(0u);
v___x_3431_ = lean_nat_dec_eq(v___x_3429_, v___x_3430_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; uint8_t v___x_3433_; 
v___x_3432_ = lean_unsigned_to_nat(1u);
v___x_3433_ = lean_nat_dec_eq(v___x_3429_, v___x_3432_);
lean_dec(v___x_3429_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; 
v___x_3434_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__1));
return v___x_3434_;
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = l_Lean_Syntax_getArg(v_args_3428_, v___x_3430_);
v___x_3436_ = l_Lean_Syntax_isNatLit_x3f(v___x_3435_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3437_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__2));
v___x_3438_ = l_Lean_Syntax_formatStx(v___x_3435_, v___x_3436_, v___x_3431_);
v___x_3439_ = l_Std_Format_defWidth;
v___x_3440_ = l_Std_Format_pretty(v___x_3438_, v___x_3439_, v___x_3430_, v___x_3430_);
v___x_3441_ = lean_string_append(v___x_3437_, v___x_3440_);
lean_dec_ref(v___x_3440_);
v___x_3442_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3443_ = lean_string_append(v___x_3441_, v___x_3442_);
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
return v___x_3444_;
}
else
{
lean_object* v_val_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec(v___x_3435_);
v_val_3445_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3436_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_val_3445_);
lean_dec(v___x_3436_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_val_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
else
{
lean_object* v___x_3453_; 
lean_dec(v___x_3429_);
v___x_3453_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__3));
return v___x_3453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* v_args_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_Parser_getParserPriority(v_args_3454_);
lean_dec(v_args_3454_);
return v_res_3455_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0));
v___x_3458_ = l_Lean_stringToMessageData(v___x_3457_);
return v___x_3458_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2));
v___x_3461_ = l_Lean_stringToMessageData(v___x_3460_);
return v___x_3461_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3462_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3463_ = l_Lean_stringToMessageData(v___x_3462_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object* v_name_3467_, uint8_t v_kind_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___y_3478_; 
v___x_3472_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1);
v___x_3473_ = l_Lean_MessageData_ofName(v_name_3467_);
v___x_3474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3472_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3474_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
switch(v_kind_3468_)
{
case 0:
{
lean_object* v___x_3485_; 
v___x_3485_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5));
v___y_3478_ = v___x_3485_;
goto v___jp_3477_;
}
case 1:
{
lean_object* v___x_3486_; 
v___x_3486_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6));
v___y_3478_ = v___x_3486_;
goto v___jp_3477_;
}
default: 
{
lean_object* v___x_3487_; 
v___x_3487_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7));
v___y_3478_ = v___x_3487_;
goto v___jp_3477_;
}
}
v___jp_3477_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
lean_inc_ref(v___y_3478_);
v___x_3479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3479_, 0, v___y_3478_);
v___x_3480_ = l_Lean_MessageData_ofFormat(v___x_3479_);
v___x_3481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3476_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3483_, v___y_3469_, v___y_3470_);
return v___x_3484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object* v_name_3488_, lean_object* v_kind_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
uint8_t v_kind_boxed_3493_; lean_object* v_res_3494_; 
v_kind_boxed_3493_ = lean_unbox(v_kind_3489_);
v_res_3494_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3488_, v_kind_boxed_3493_, v___y_3490_, v___y_3491_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3495_, lean_object* v_msg_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_fileName_3500_; lean_object* v_fileMap_3501_; lean_object* v_options_3502_; lean_object* v_currRecDepth_3503_; lean_object* v_maxRecDepth_3504_; lean_object* v_ref_3505_; lean_object* v_currNamespace_3506_; lean_object* v_openDecls_3507_; lean_object* v_initHeartbeats_3508_; lean_object* v_maxHeartbeats_3509_; lean_object* v_quotContext_3510_; lean_object* v_currMacroScope_3511_; uint8_t v_diag_3512_; lean_object* v_cancelTk_x3f_3513_; uint8_t v_suppressElabErrors_3514_; lean_object* v_inheritedTraceOptions_3515_; lean_object* v_ref_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v_fileName_3500_ = lean_ctor_get(v___y_3497_, 0);
v_fileMap_3501_ = lean_ctor_get(v___y_3497_, 1);
v_options_3502_ = lean_ctor_get(v___y_3497_, 2);
v_currRecDepth_3503_ = lean_ctor_get(v___y_3497_, 3);
v_maxRecDepth_3504_ = lean_ctor_get(v___y_3497_, 4);
v_ref_3505_ = lean_ctor_get(v___y_3497_, 5);
v_currNamespace_3506_ = lean_ctor_get(v___y_3497_, 6);
v_openDecls_3507_ = lean_ctor_get(v___y_3497_, 7);
v_initHeartbeats_3508_ = lean_ctor_get(v___y_3497_, 8);
v_maxHeartbeats_3509_ = lean_ctor_get(v___y_3497_, 9);
v_quotContext_3510_ = lean_ctor_get(v___y_3497_, 10);
v_currMacroScope_3511_ = lean_ctor_get(v___y_3497_, 11);
v_diag_3512_ = lean_ctor_get_uint8(v___y_3497_, sizeof(void*)*14);
v_cancelTk_x3f_3513_ = lean_ctor_get(v___y_3497_, 12);
v_suppressElabErrors_3514_ = lean_ctor_get_uint8(v___y_3497_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3515_ = lean_ctor_get(v___y_3497_, 13);
v_ref_3516_ = l_Lean_replaceRef(v_ref_3495_, v_ref_3505_);
lean_inc_ref(v_inheritedTraceOptions_3515_);
lean_inc(v_cancelTk_x3f_3513_);
lean_inc(v_currMacroScope_3511_);
lean_inc(v_quotContext_3510_);
lean_inc(v_maxHeartbeats_3509_);
lean_inc(v_initHeartbeats_3508_);
lean_inc(v_openDecls_3507_);
lean_inc(v_currNamespace_3506_);
lean_inc(v_maxRecDepth_3504_);
lean_inc(v_currRecDepth_3503_);
lean_inc_ref(v_options_3502_);
lean_inc_ref(v_fileMap_3501_);
lean_inc_ref(v_fileName_3500_);
v___x_3517_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3517_, 0, v_fileName_3500_);
lean_ctor_set(v___x_3517_, 1, v_fileMap_3501_);
lean_ctor_set(v___x_3517_, 2, v_options_3502_);
lean_ctor_set(v___x_3517_, 3, v_currRecDepth_3503_);
lean_ctor_set(v___x_3517_, 4, v_maxRecDepth_3504_);
lean_ctor_set(v___x_3517_, 5, v_ref_3516_);
lean_ctor_set(v___x_3517_, 6, v_currNamespace_3506_);
lean_ctor_set(v___x_3517_, 7, v_openDecls_3507_);
lean_ctor_set(v___x_3517_, 8, v_initHeartbeats_3508_);
lean_ctor_set(v___x_3517_, 9, v_maxHeartbeats_3509_);
lean_ctor_set(v___x_3517_, 10, v_quotContext_3510_);
lean_ctor_set(v___x_3517_, 11, v_currMacroScope_3511_);
lean_ctor_set(v___x_3517_, 12, v_cancelTk_x3f_3513_);
lean_ctor_set(v___x_3517_, 13, v_inheritedTraceOptions_3515_);
lean_ctor_set_uint8(v___x_3517_, sizeof(void*)*14, v_diag_3512_);
lean_ctor_set_uint8(v___x_3517_, sizeof(void*)*14 + 1, v_suppressElabErrors_3514_);
v___x_3518_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_3496_, v___x_3517_, v___y_3498_);
lean_dec_ref(v___x_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3519_, lean_object* v_msg_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3519_, v_msg_3520_, v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v_ref_3519_);
return v_res_3524_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_3527_ = l_Lean_stringToMessageData(v___x_3526_);
return v___x_3527_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_3530_ = l_Lean_stringToMessageData(v___x_3529_);
return v___x_3530_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_3533_ = l_Lean_stringToMessageData(v___x_3532_);
return v___x_3533_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_3536_ = l_Lean_stringToMessageData(v___x_3535_);
return v___x_3536_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_3539_ = l_Lean_stringToMessageData(v___x_3538_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_3542_ = l_Lean_stringToMessageData(v___x_3541_);
return v___x_3542_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_3545_ = l_Lean_stringToMessageData(v___x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_3546_, lean_object* v_declHint_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; lean_object* v_env_3551_; uint8_t v___x_3552_; 
v___x_3550_ = lean_st_ref_get(v___y_3548_);
v_env_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc_ref(v_env_3551_);
lean_dec(v___x_3550_);
v___x_3552_ = l_Lean_Name_isAnonymous(v_declHint_3547_);
if (v___x_3552_ == 0)
{
uint8_t v_isExporting_3553_; 
v_isExporting_3553_ = lean_ctor_get_uint8(v_env_3551_, sizeof(void*)*8);
if (v_isExporting_3553_ == 0)
{
lean_object* v___x_3554_; 
lean_dec_ref(v_env_3551_);
lean_dec(v_declHint_3547_);
v___x_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3554_, 0, v_msg_3546_);
return v___x_3554_;
}
else
{
lean_object* v___x_3555_; uint8_t v___x_3556_; 
lean_inc_ref(v_env_3551_);
v___x_3555_ = l_Lean_Environment_setExporting(v_env_3551_, v___x_3552_);
lean_inc(v_declHint_3547_);
lean_inc_ref(v___x_3555_);
v___x_3556_ = l_Lean_Environment_contains(v___x_3555_, v_declHint_3547_, v_isExporting_3553_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; 
lean_dec_ref(v___x_3555_);
lean_dec_ref(v_env_3551_);
lean_dec(v_declHint_3547_);
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v_msg_3546_);
return v___x_3557_;
}
else
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v_c_3563_; lean_object* v___x_3564_; 
v___x_3558_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_3559_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_3560_ = l_Lean_Options_empty;
v___x_3561_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3555_);
lean_ctor_set(v___x_3561_, 1, v___x_3558_);
lean_ctor_set(v___x_3561_, 2, v___x_3559_);
lean_ctor_set(v___x_3561_, 3, v___x_3560_);
lean_inc(v_declHint_3547_);
v___x_3562_ = l_Lean_MessageData_ofConstName(v_declHint_3547_, v___x_3552_);
v_c_3563_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3563_, 0, v___x_3561_);
lean_ctor_set(v_c_3563_, 1, v___x_3562_);
v___x_3564_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3551_, v_declHint_3547_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
lean_dec_ref(v_env_3551_);
lean_dec(v_declHint_3547_);
v___x_3565_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
lean_ctor_set(v___x_3566_, 1, v_c_3563_);
v___x_3567_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = l_Lean_MessageData_note(v___x_3568_);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_msg_3546_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
return v___x_3571_;
}
else
{
lean_object* v_val_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3607_; 
v_val_3572_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3574_ = v___x_3564_;
v_isShared_3575_ = v_isSharedCheck_3607_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_val_3572_);
lean_dec(v___x_3564_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3607_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v_mod_3579_; uint8_t v___x_3580_; 
v___x_3576_ = lean_box(0);
v___x_3577_ = l_Lean_Environment_header(v_env_3551_);
lean_dec_ref(v_env_3551_);
v___x_3578_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3577_);
v_mod_3579_ = lean_array_get(v___x_3576_, v___x_3578_, v_val_3572_);
lean_dec(v_val_3572_);
lean_dec_ref(v___x_3578_);
v___x_3580_ = l_Lean_isPrivateName(v_declHint_3547_);
lean_dec(v_declHint_3547_);
if (v___x_3580_ == 0)
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; 
v___x_3581_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_3582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
lean_ctor_set(v___x_3582_, 1, v_c_3563_);
v___x_3583_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = l_Lean_MessageData_ofName(v_mod_3579_);
v___x_3586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3584_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_3588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3586_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
v___x_3589_ = l_Lean_MessageData_note(v___x_3588_);
v___x_3590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3590_, 0, v_msg_3546_);
lean_ctor_set(v___x_3590_, 1, v___x_3589_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set_tag(v___x_3574_, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3590_);
v___x_3592_ = v___x_3574_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3594_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
lean_ctor_set(v___x_3595_, 1, v_c_3563_);
v___x_3596_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_3597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3595_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = l_Lean_MessageData_ofName(v_mod_3579_);
v___x_3599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3597_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3599_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v___x_3602_ = l_Lean_MessageData_note(v___x_3601_);
v___x_3603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3603_, 0, v_msg_3546_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set_tag(v___x_3574_, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3603_);
v___x_3605_ = v___x_3574_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3608_; 
lean_dec_ref(v_env_3551_);
lean_dec(v_declHint_3547_);
v___x_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3608_, 0, v_msg_3546_);
return v___x_3608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_3609_, lean_object* v_declHint_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3609_, v_declHint_3610_, v___y_3611_);
lean_dec(v___y_3611_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_3614_, lean_object* v_declHint_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3629_; 
v___x_3619_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3614_, v_declHint_3615_, v___y_3617_);
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3622_ = v___x_3619_;
v_isShared_3623_ = v_isSharedCheck_3629_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3619_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3629_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3627_; 
v___x_3624_ = l_Lean_unknownIdentifierMessageTag;
v___x_3625_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
lean_ctor_set(v___x_3625_, 1, v_a_3620_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set(v___x_3622_, 0, v___x_3625_);
v___x_3627_ = v___x_3622_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3625_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_3630_, lean_object* v_declHint_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3630_, v_declHint_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3636_, lean_object* v_msg_3637_, lean_object* v_declHint_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; lean_object* v_a_3643_; lean_object* v___x_3644_; 
v___x_3642_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3637_, v_declHint_3638_, v___y_3639_, v___y_3640_);
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref(v___x_3642_);
v___x_3644_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3636_, v_a_3643_, v___y_3639_, v___y_3640_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3645_, lean_object* v_msg_3646_, lean_object* v_declHint_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3645_, v_msg_3646_, v_declHint_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v_ref_3645_);
return v_res_3651_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3654_, lean_object* v_constName_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v___x_3659_; uint8_t v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3659_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3660_ = 0;
lean_inc(v_constName_3655_);
v___x_3661_ = l_Lean_MessageData_ofConstName(v_constName_3655_, v___x_3660_);
v___x_3662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3659_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3654_, v___x_3664_, v_constName_3655_, v___y_3656_, v___y_3657_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3666_, lean_object* v_constName_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3666_, v_constName_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v_ref_3666_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object* v_constName_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v_ref_3676_; lean_object* v___x_3677_; 
v_ref_3676_ = lean_ctor_get(v___y_3673_, 5);
v___x_3677_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3676_, v_constName_3672_, v___y_3673_, v___y_3674_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3678_, v___y_3679_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object* v_constName_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v___x_3687_; lean_object* v_env_3688_; uint8_t v___x_3689_; lean_object* v___x_3690_; 
v___x_3687_ = lean_st_ref_get(v___y_3685_);
v_env_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc_ref(v_env_3688_);
lean_dec(v___x_3687_);
v___x_3689_ = 0;
lean_inc(v_constName_3683_);
v___x_3690_ = l_Lean_Environment_find_x3f(v_env_3688_, v_constName_3683_, v___x_3689_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3683_, v___y_3684_, v___y_3685_);
return v___x_3691_;
}
else
{
lean_object* v_val_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v_constName_3683_);
v_val_3692_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3690_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_val_3692_);
lean_dec(v___x_3690_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
lean_ctor_set_tag(v___x_3694_, 0);
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_val_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object* v_constName_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
return v_res_3704_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0));
v___x_3707_ = l_Lean_stringToMessageData(v___x_3706_);
return v___x_3707_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3(void){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2));
v___x_3710_ = l_Lean_stringToMessageData(v___x_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* v_attrName_3711_, lean_object* v_catName_3712_, lean_object* v_declName_3713_, lean_object* v_stx_3714_, uint8_t v_kind_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_){
_start:
{
lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Attribute_Builtin_getPrio(v_stx_3714_, v_a_3716_, v_a_3717_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___y_3742_; lean_object* v___y_3743_; uint8_t v___x_3771_; uint8_t v___x_3772_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref(v___x_3739_);
v___x_3771_ = 0;
v___x_3772_ = l_Lean_instBEqAttributeKind_beq(v_kind_3715_, v___x_3771_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; 
lean_dec(v_a_3740_);
lean_dec(v_declName_3713_);
lean_dec(v_catName_3712_);
v___x_3773_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_attrName_3711_, v_kind_3715_, v_a_3716_, v_a_3717_);
return v___x_3773_;
}
else
{
lean_dec(v_attrName_3711_);
v___y_3742_ = v_a_3716_;
v___y_3743_ = v_a_3717_;
goto v___jp_3741_;
}
v___jp_3741_:
{
lean_object* v___x_3744_; 
lean_inc(v_declName_3713_);
v___x_3744_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_declName_3713_, v___y_3742_, v___y_3743_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3746_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref(v___x_3744_);
v___x_3746_ = l_Lean_ConstantInfo_type(v_a_3745_);
if (lean_obj_tag(v___x_3746_) == 4)
{
lean_object* v_declName_3747_; 
v_declName_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_declName_3747_);
lean_dec_ref(v___x_3746_);
if (lean_obj_tag(v_declName_3747_) == 1)
{
lean_object* v_pre_3748_; 
v_pre_3748_ = lean_ctor_get(v_declName_3747_, 0);
lean_inc(v_pre_3748_);
if (lean_obj_tag(v_pre_3748_) == 1)
{
lean_object* v_pre_3749_; 
v_pre_3749_ = lean_ctor_get(v_pre_3748_, 0);
lean_inc(v_pre_3749_);
if (lean_obj_tag(v_pre_3749_) == 1)
{
lean_object* v_pre_3750_; 
v_pre_3750_ = lean_ctor_get(v_pre_3749_, 0);
if (lean_obj_tag(v_pre_3750_) == 0)
{
lean_object* v_str_3751_; lean_object* v_str_3752_; lean_object* v_str_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v_str_3751_ = lean_ctor_get(v_declName_3747_, 1);
lean_inc_ref(v_str_3751_);
lean_dec_ref(v_declName_3747_);
v_str_3752_ = lean_ctor_get(v_pre_3748_, 1);
lean_inc_ref(v_str_3752_);
lean_dec_ref(v_pre_3748_);
v_str_3753_ = lean_ctor_get(v_pre_3749_, 1);
lean_inc_ref(v_str_3753_);
lean_dec_ref(v_pre_3749_);
v___x_3754_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3755_ = lean_string_dec_eq(v_str_3753_, v___x_3754_);
lean_dec_ref(v_str_3753_);
if (v___x_3755_ == 0)
{
lean_dec_ref(v_str_3752_);
lean_dec_ref(v_str_3751_);
lean_dec(v_a_3740_);
lean_dec(v_catName_3712_);
v___y_3726_ = v_a_3745_;
v___y_3727_ = v___y_3742_;
v___y_3728_ = v___y_3743_;
goto v___jp_3725_;
}
else
{
lean_object* v___x_3756_; uint8_t v___x_3757_; 
v___x_3756_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3757_ = lean_string_dec_eq(v_str_3752_, v___x_3756_);
lean_dec_ref(v_str_3752_);
if (v___x_3757_ == 0)
{
lean_dec_ref(v_str_3751_);
lean_dec(v_a_3740_);
lean_dec(v_catName_3712_);
v___y_3726_ = v_a_3745_;
v___y_3727_ = v___y_3742_;
v___y_3728_ = v___y_3743_;
goto v___jp_3725_;
}
else
{
lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3758_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_3759_ = lean_string_dec_eq(v_str_3751_, v___x_3758_);
if (v___x_3759_ == 0)
{
uint8_t v___x_3760_; 
v___x_3760_ = lean_string_dec_eq(v_str_3751_, v___x_3756_);
lean_dec_ref(v_str_3751_);
if (v___x_3760_ == 0)
{
lean_dec(v_a_3740_);
lean_dec(v_catName_3712_);
v___y_3726_ = v_a_3745_;
v___y_3727_ = v___y_3742_;
v___y_3728_ = v___y_3743_;
goto v___jp_3725_;
}
else
{
lean_object* v___x_3761_; 
lean_dec(v_a_3745_);
lean_inc(v_declName_3713_);
lean_inc(v_catName_3712_);
v___x_3761_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3712_, v_declName_3713_, v_a_3740_, v___y_3742_, v___y_3743_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_dec_ref(v___x_3761_);
v___y_3720_ = v___y_3742_;
v___y_3721_ = v___y_3743_;
goto v___jp_3719_;
}
else
{
lean_dec(v_declName_3713_);
lean_dec(v_catName_3712_);
return v___x_3761_;
}
}
}
else
{
lean_object* v___x_3762_; 
lean_dec_ref(v_str_3751_);
lean_dec(v_a_3745_);
lean_inc(v_declName_3713_);
lean_inc(v_catName_3712_);
v___x_3762_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3712_, v_declName_3713_, v_a_3740_, v___y_3742_, v___y_3743_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_dec_ref(v___x_3762_);
v___y_3720_ = v___y_3742_;
v___y_3721_ = v___y_3743_;
goto v___jp_3719_;
}
else
{
lean_dec(v_declName_3713_);
lean_dec(v_catName_3712_);
return v___x_3762_;
}
}
}
}
}
else
{
lean_dec_ref(v_pre_3749_);
lean_dec_ref(v_pre_3748_);
lean_dec_ref(v_declName_3747_);
lean_dec(v_a_3740_);
lean_dec(v_catName_3712_);
v___y_3726_ = v_a_3745_;
v___y_3727_ = v___y_3742_;
v___y_3728_ = v___y_3743_;
goto v___jp_3725_;
}
}
else
{
lean_dec_ref(v_pre_3748_);
lean_dec(v_pre_3749_);
lean_dec_ref(v_declName_3747_);
lean_dec(v_a_3740_);
lean_dec(v_catName_3712_);
v___y_3726_ = v_a_3745_;
v___y_3727_ = v___y_3742_;
v___y_3728_ = v___y_3743_;
goto v___jp_3725_;
}
}
else
{
lean_dec(v_pre_3748_);
lean_dec_ref(v_declName_3747_);
lean_dec(v_a_3740_);
lean_dec(v_catName_3712_);
v___y_3726_ = v_a_3745_;
v___y_3727_ = v___y_3742_;
v___y_3728_ = v___y_3743_;
goto v___jp_3725_;
}
}
else
{
lean_dec(v_declName_3747_);
lean_dec(v_a_3740_);
lean_dec(v_catName_3712_);
v___y_3726_ = v_a_3745_;
v___y_3727_ = v___y_3742_;
v___y_3728_ = v___y_3743_;
goto v___jp_3725_;
}
}
else
{
lean_dec_ref(v___x_3746_);
lean_dec(v_a_3740_);
lean_dec(v_catName_3712_);
v___y_3726_ = v_a_3745_;
v___y_3727_ = v___y_3742_;
v___y_3728_ = v___y_3743_;
goto v___jp_3725_;
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec(v_a_3740_);
lean_dec(v_declName_3713_);
lean_dec(v_catName_3712_);
v_a_3763_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3744_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3744_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
lean_dec(v_declName_3713_);
lean_dec(v_catName_3712_);
lean_dec(v_attrName_3711_);
v_a_3774_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3739_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3739_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
v___jp_3719_:
{
lean_object* v___x_3722_; 
lean_inc(v_declName_3713_);
v___x_3722_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_3713_, v___y_3720_, v___y_3721_);
if (lean_obj_tag(v___x_3722_) == 0)
{
uint8_t v___x_3723_; lean_object* v___x_3724_; 
lean_dec_ref(v___x_3722_);
v___x_3723_ = 1;
v___x_3724_ = l_Lean_Parser_runParserAttributeHooks(v_catName_3712_, v_declName_3713_, v___x_3723_, v___y_3720_, v___y_3721_);
return v___x_3724_;
}
else
{
lean_dec(v_declName_3713_);
lean_dec(v_catName_3712_);
return v___x_3722_;
}
}
v___jp_3725_:
{
lean_object* v___x_3729_; uint8_t v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3729_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
v___x_3730_ = 0;
v___x_3731_ = l_Lean_MessageData_ofConstName(v_declName_3713_, v___x_3730_);
v___x_3732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3729_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = l_Lean_ConstantInfo_type(v___y_3726_);
lean_dec_ref(v___y_3726_);
v___x_3736_ = l_Lean_indentExpr(v___x_3735_);
v___x_3737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3734_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3737_, v___y_3727_, v___y_3728_);
return v___x_3738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* v_attrName_3782_, lean_object* v_catName_3783_, lean_object* v_declName_3784_, lean_object* v_stx_3785_, lean_object* v_kind_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_){
_start:
{
uint8_t v_kind_boxed_3790_; lean_object* v_res_3791_; 
v_kind_boxed_3790_ = lean_unbox(v_kind_3786_);
v_res_3791_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3782_, v_catName_3783_, v_declName_3784_, v_stx_3785_, v_kind_boxed_3790_, v_a_3787_, v_a_3788_);
lean_dec(v_a_3788_);
lean_dec_ref(v_a_3787_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object* v_00_u03b1_3792_, lean_object* v_name_3793_, uint8_t v_kind_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3793_, v_kind_3794_, v___y_3795_, v___y_3796_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b1_3799_, lean_object* v_name_3800_, lean_object* v_kind_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
uint8_t v_kind_boxed_3805_; lean_object* v_res_3806_; 
v_kind_boxed_3805_ = lean_unbox(v_kind_3801_);
v_res_3806_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(v_00_u03b1_3799_, v_name_3800_, v_kind_boxed_3805_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object* v_00_u03b1_3807_, lean_object* v_constName_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3808_, v___y_3809_, v___y_3810_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3813_, lean_object* v_constName_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(v_00_u03b1_3813_, v_constName_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3819_, lean_object* v_ref_3820_, lean_object* v_constName_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3820_, v_constName_3821_, v___y_3822_, v___y_3823_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3826_, lean_object* v_ref_3827_, lean_object* v_constName_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(v_00_u03b1_3826_, v_ref_3827_, v_constName_3828_, v___y_3829_, v___y_3830_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v_ref_3827_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3833_, lean_object* v_ref_3834_, lean_object* v_msg_3835_, lean_object* v_declHint_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3834_, v_msg_3835_, v_declHint_3836_, v___y_3837_, v___y_3838_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3841_, lean_object* v_ref_3842_, lean_object* v_msg_3843_, lean_object* v_declHint_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3841_, v_ref_3842_, v_msg_3843_, v_declHint_3844_, v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v_ref_3842_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_3849_, lean_object* v_declHint_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3849_, v_declHint_3850_, v___y_3852_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_3855_, lean_object* v_declHint_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_3855_, v_declHint_3856_, v___y_3857_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3861_, lean_object* v_ref_3862_, lean_object* v_msg_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3862_, v_msg_3863_, v___y_3864_, v___y_3865_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3868_, lean_object* v_ref_3869_, lean_object* v_msg_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3868_, v_ref_3869_, v_msg_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v_ref_3869_);
return v_res_3874_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2(void){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0));
v___x_3882_ = l_Lean_mkAtom(v___x_3881_);
return v___x_3882_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3883_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2);
v___x_3884_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3885_ = lean_array_push(v___x_3884_, v___x_3883_);
return v___x_3885_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7));
v___x_3895_ = l_Lean_mkAtom(v___x_3894_);
return v___x_3895_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3896_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8);
v___x_3897_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3898_ = lean_array_push(v___x_3897_, v___x_3896_);
return v___x_3898_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3899_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9);
v___x_3900_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6));
v___x_3901_ = lean_box(2);
v___x_3902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3901_);
lean_ctor_set(v___x_3902_, 1, v___x_3900_);
lean_ctor_set(v___x_3902_, 2, v___x_3899_);
return v___x_3902_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3903_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10);
v___x_3904_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3);
v___x_3905_ = lean_array_push(v___x_3904_, v___x_3903_);
return v___x_3905_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3906_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11);
v___x_3907_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1));
v___x_3908_ = lean_box(2);
v___x_3909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
lean_ctor_set(v___x_3909_, 1, v___x_3907_);
lean_ctor_set(v___x_3909_, 2, v___x_3906_);
return v___x_3909_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3910_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12);
v___x_3911_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3912_ = lean_array_push(v___x_3911_, v___x_3910_);
return v___x_3912_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14(void){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3913_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13);
v___x_3914_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3915_ = lean_box(2);
v___x_3916_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
lean_ctor_set(v___x_3916_, 1, v___x_3914_);
lean_ctor_set(v___x_3916_, 2, v___x_3913_);
return v___x_3916_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3917_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14);
v___x_3918_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3919_ = lean_array_push(v___x_3918_, v___x_3917_);
return v___x_3919_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3920_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15);
v___x_3921_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3922_ = lean_box(2);
v___x_3923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
lean_ctor_set(v___x_3923_, 1, v___x_3921_);
lean_ctor_set(v___x_3923_, 2, v___x_3920_);
return v___x_3923_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3924_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16);
v___x_3925_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3926_ = lean_array_push(v___x_3925_, v___x_3924_);
return v___x_3926_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3927_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17);
v___x_3928_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3929_ = lean_box(2);
v___x_3930_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
lean_ctor_set(v___x_3930_, 1, v___x_3928_);
lean_ctor_set(v___x_3930_, 2, v___x_3927_);
return v___x_3930_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object* v_attrName_3932_, lean_object* v_decl_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3937_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3938_ = l_Lean_MessageData_ofName(v_attrName_3932_);
v___x_3939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3937_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3939_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
v___x_3942_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3941_, v___y_3934_, v___y_3935_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object* v_attrName_3943_, lean_object* v_decl_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_3943_, v_decl_3944_, v___y_3945_, v___y_3946_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v_decl_3944_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object* v_attrName_3949_, lean_object* v_catName_3950_, lean_object* v_declName_3951_, lean_object* v_stx_3952_, uint8_t v_kind_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3949_, v_catName_3950_, v_declName_3951_, v_stx_3952_, v_kind_3953_, v___y_3954_, v___y_3955_);
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object* v_attrName_3958_, lean_object* v_catName_3959_, lean_object* v_declName_3960_, lean_object* v_stx_3961_, lean_object* v_kind_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
uint8_t v_kind_boxed_3966_; lean_object* v_res_3967_; 
v_kind_boxed_3966_ = lean_unbox(v_kind_3962_);
v_res_3967_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_3958_, v_catName_3959_, v_declName_3960_, v_stx_3961_, v_kind_boxed_3966_, v___y_3963_, v___y_3964_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
return v_res_3967_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1(void){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__0));
v___x_3970_ = lean_mk_io_user_error(v___x_3969_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* v_attrName_3973_, lean_object* v_declName_3974_, uint8_t v_behavior_3975_, lean_object* v_ref_3976_){
_start:
{
if (lean_obj_tag(v_declName_3974_) == 1)
{
lean_object* v_pre_3981_; 
v_pre_3981_ = lean_ctor_get(v_declName_3974_, 0);
if (lean_obj_tag(v_pre_3981_) == 1)
{
lean_object* v_pre_3982_; 
v_pre_3982_ = lean_ctor_get(v_pre_3981_, 0);
if (lean_obj_tag(v_pre_3982_) == 1)
{
lean_object* v_pre_3983_; 
v_pre_3983_ = lean_ctor_get(v_pre_3982_, 0);
if (lean_obj_tag(v_pre_3983_) == 1)
{
lean_object* v_pre_3984_; 
v_pre_3984_ = lean_ctor_get(v_pre_3983_, 0);
if (lean_obj_tag(v_pre_3984_) == 0)
{
lean_object* v_str_3985_; lean_object* v_str_3986_; lean_object* v_str_3987_; lean_object* v_str_3988_; lean_object* v___x_3989_; uint8_t v___x_3990_; 
v_str_3985_ = lean_ctor_get(v_declName_3974_, 1);
v_str_3986_ = lean_ctor_get(v_pre_3981_, 1);
v_str_3987_ = lean_ctor_get(v_pre_3982_, 1);
v_str_3988_ = lean_ctor_get(v_pre_3983_, 1);
v___x_3989_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3990_ = lean_string_dec_eq(v_str_3988_, v___x_3989_);
if (v___x_3990_ == 0)
{
lean_dec_ref(v_declName_3974_);
lean_dec(v_ref_3976_);
lean_dec(v_attrName_3973_);
goto v___jp_3978_;
}
else
{
lean_object* v___x_3991_; uint8_t v___x_3992_; 
v___x_3991_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3992_ = lean_string_dec_eq(v_str_3987_, v___x_3991_);
if (v___x_3992_ == 0)
{
lean_dec_ref(v_declName_3974_);
lean_dec(v_ref_3976_);
lean_dec(v_attrName_3973_);
goto v___jp_3978_;
}
else
{
lean_object* v___x_3993_; uint8_t v___x_3994_; 
v___x_3993_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__2));
v___x_3994_ = lean_string_dec_eq(v_str_3986_, v___x_3993_);
if (v___x_3994_ == 0)
{
lean_dec_ref(v_declName_3974_);
lean_dec(v_ref_3976_);
lean_dec(v_attrName_3973_);
goto v___jp_3978_;
}
else
{
lean_object* v___x_3995_; lean_object* v_catName_3996_; lean_object* v___x_3997_; 
v___x_3995_ = lean_box(0);
lean_inc_ref(v_str_3985_);
v_catName_3996_ = l_Lean_Name_str___override(v___x_3995_, v_str_3985_);
lean_inc(v_catName_3996_);
v___x_3997_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_3996_, v_declName_3974_, v_behavior_3975_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v___f_3998_; lean_object* v___f_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
lean_dec_ref(v___x_3997_);
lean_inc_n(v_attrName_3973_, 2);
v___f_3998_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3998_, 0, v_attrName_3973_);
v___f_3999_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3999_, 0, v_attrName_3973_);
lean_closure_set(v___f_3999_, 1, v_catName_3996_);
v___x_4000_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__3));
v___x_4001_ = 1;
v___x_4002_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4002_, 0, v_ref_3976_);
lean_ctor_set(v___x_4002_, 1, v_attrName_3973_);
lean_ctor_set(v___x_4002_, 2, v___x_4000_);
lean_ctor_set_uint8(v___x_4002_, sizeof(void*)*3, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
lean_ctor_set(v___x_4003_, 1, v___f_3999_);
lean_ctor_set(v___x_4003_, 2, v___f_3998_);
v___x_4004_ = l_Lean_registerBuiltinAttribute(v___x_4003_);
return v___x_4004_;
}
else
{
lean_dec(v_catName_3996_);
lean_dec(v_ref_3976_);
lean_dec(v_attrName_3973_);
return v___x_3997_;
}
}
}
}
}
else
{
lean_dec_ref(v_declName_3974_);
lean_dec(v_ref_3976_);
lean_dec(v_attrName_3973_);
goto v___jp_3978_;
}
}
else
{
lean_dec_ref(v_declName_3974_);
lean_dec(v_ref_3976_);
lean_dec(v_attrName_3973_);
goto v___jp_3978_;
}
}
else
{
lean_dec_ref(v_declName_3974_);
lean_dec(v_ref_3976_);
lean_dec(v_attrName_3973_);
goto v___jp_3978_;
}
}
else
{
lean_dec_ref(v_declName_3974_);
lean_dec(v_ref_3976_);
lean_dec(v_attrName_3973_);
goto v___jp_3978_;
}
}
else
{
lean_dec(v_ref_3976_);
lean_dec(v_declName_3974_);
lean_dec(v_attrName_3973_);
goto v___jp_3978_;
}
v___jp_3978_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3979_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___closed__1, &l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
v___x_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
return v___x_3980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* v_attrName_4005_, lean_object* v_declName_4006_, lean_object* v_behavior_4007_, lean_object* v_ref_4008_, lean_object* v_a_4009_){
_start:
{
uint8_t v_behavior_boxed_4010_; lean_object* v_res_4011_; 
v_behavior_boxed_4010_ = lean_unbox(v_behavior_4007_);
v_res_4011_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_4005_, v_declName_4006_, v_behavior_boxed_4010_, v_ref_4008_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object* v_kind_4012_, lean_object* v_x_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v___x_4017_; lean_object* v_env_4018_; lean_object* v_nextMacroScope_4019_; lean_object* v_ngen_4020_; lean_object* v_auxDeclNGen_4021_; lean_object* v_traceState_4022_; lean_object* v_messages_4023_; lean_object* v_infoState_4024_; lean_object* v_snapshotTasks_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4037_; 
v___x_4017_ = lean_st_ref_take(v___y_4015_);
v_env_4018_ = lean_ctor_get(v___x_4017_, 0);
v_nextMacroScope_4019_ = lean_ctor_get(v___x_4017_, 1);
v_ngen_4020_ = lean_ctor_get(v___x_4017_, 2);
v_auxDeclNGen_4021_ = lean_ctor_get(v___x_4017_, 3);
v_traceState_4022_ = lean_ctor_get(v___x_4017_, 4);
v_messages_4023_ = lean_ctor_get(v___x_4017_, 6);
v_infoState_4024_ = lean_ctor_get(v___x_4017_, 7);
v_snapshotTasks_4025_ = lean_ctor_get(v___x_4017_, 8);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4037_ == 0)
{
lean_object* v_unused_4038_; 
v_unused_4038_ = lean_ctor_get(v___x_4017_, 5);
lean_dec(v_unused_4038_);
v___x_4027_ = v___x_4017_;
v_isShared_4028_ = v_isSharedCheck_4037_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_snapshotTasks_4025_);
lean_inc(v_infoState_4024_);
lean_inc(v_messages_4023_);
lean_inc(v_traceState_4022_);
lean_inc(v_auxDeclNGen_4021_);
lean_inc(v_ngen_4020_);
lean_inc(v_nextMacroScope_4019_);
lean_inc(v_env_4018_);
lean_dec(v___x_4017_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4037_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4032_; 
v___x_4029_ = l_Lean_Parser_addSyntaxNodeKind(v_env_4018_, v_kind_4012_);
v___x_4030_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 5, v___x_4030_);
lean_ctor_set(v___x_4027_, 0, v___x_4029_);
v___x_4032_ = v___x_4027_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4029_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_nextMacroScope_4019_);
lean_ctor_set(v_reuseFailAlloc_4036_, 2, v_ngen_4020_);
lean_ctor_set(v_reuseFailAlloc_4036_, 3, v_auxDeclNGen_4021_);
lean_ctor_set(v_reuseFailAlloc_4036_, 4, v_traceState_4022_);
lean_ctor_set(v_reuseFailAlloc_4036_, 5, v___x_4030_);
lean_ctor_set(v_reuseFailAlloc_4036_, 6, v_messages_4023_);
lean_ctor_set(v_reuseFailAlloc_4036_, 7, v_infoState_4024_);
lean_ctor_set(v_reuseFailAlloc_4036_, 8, v_snapshotTasks_4025_);
v___x_4032_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4033_ = lean_st_ref_set(v___y_4015_, v___x_4032_);
v___x_4034_ = lean_box(0);
v___x_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
return v___x_4035_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object* v_kind_4039_, lean_object* v_x_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_4039_, v_x_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_4045_, lean_object* v_keys_4046_, lean_object* v_vals_4047_, lean_object* v_i_4048_, lean_object* v_acc_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v___x_4053_; uint8_t v___x_4054_; 
v___x_4053_ = lean_array_get_size(v_keys_4046_);
v___x_4054_ = lean_nat_dec_lt(v_i_4048_, v___x_4053_);
if (v___x_4054_ == 0)
{
lean_object* v___x_4055_; 
lean_dec(v_i_4048_);
lean_dec_ref(v_f_4045_);
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v_acc_4049_);
return v___x_4055_;
}
else
{
lean_object* v_k_4056_; lean_object* v_v_4057_; lean_object* v___x_4058_; 
v_k_4056_ = lean_array_fget_borrowed(v_keys_4046_, v_i_4048_);
v_v_4057_ = lean_array_fget_borrowed(v_vals_4047_, v_i_4048_);
lean_inc_ref(v_f_4045_);
lean_inc(v___y_4051_);
lean_inc_ref(v___y_4050_);
lean_inc(v_v_4057_);
lean_inc(v_k_4056_);
v___x_4058_ = lean_apply_6(v_f_4045_, v_acc_4049_, v_k_4056_, v_v_4057_, v___y_4050_, v___y_4051_, lean_box(0));
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref(v___x_4058_);
v___x_4060_ = lean_unsigned_to_nat(1u);
v___x_4061_ = lean_nat_add(v_i_4048_, v___x_4060_);
lean_dec(v_i_4048_);
v_i_4048_ = v___x_4061_;
v_acc_4049_ = v_a_4059_;
goto _start;
}
else
{
lean_dec(v_i_4048_);
lean_dec_ref(v_f_4045_);
return v___x_4058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_4063_, lean_object* v_keys_4064_, lean_object* v_vals_4065_, lean_object* v_i_4066_, lean_object* v_acc_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4063_, v_keys_4064_, v_vals_4065_, v_i_4066_, v_acc_4067_, v___y_4068_, v___y_4069_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec_ref(v_vals_4065_);
lean_dec_ref(v_keys_4064_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object* v_f_4072_, lean_object* v_x_4073_, lean_object* v_x_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
if (lean_obj_tag(v_x_4073_) == 0)
{
lean_object* v_es_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4098_; 
v_es_4078_ = lean_ctor_get(v_x_4073_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_x_4073_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4080_ = v_x_4073_;
v_isShared_4081_ = v_isSharedCheck_4098_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_es_4078_);
lean_dec(v_x_4073_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4098_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; uint8_t v___x_4084_; 
v___x_4082_ = lean_unsigned_to_nat(0u);
v___x_4083_ = lean_array_get_size(v_es_4078_);
v___x_4084_ = lean_nat_dec_lt(v___x_4082_, v___x_4083_);
if (v___x_4084_ == 0)
{
lean_object* v___x_4086_; 
lean_dec_ref(v_es_4078_);
lean_dec_ref(v_f_4072_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v_x_4074_);
v___x_4086_ = v___x_4080_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_x_4074_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
else
{
uint8_t v___x_4088_; 
v___x_4088_ = lean_nat_dec_le(v___x_4083_, v___x_4083_);
if (v___x_4088_ == 0)
{
if (v___x_4084_ == 0)
{
lean_object* v___x_4090_; 
lean_dec_ref(v_es_4078_);
lean_dec_ref(v_f_4072_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v_x_4074_);
v___x_4090_ = v___x_4080_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_x_4074_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
else
{
size_t v___x_4092_; size_t v___x_4093_; lean_object* v___x_4094_; 
lean_del_object(v___x_4080_);
v___x_4092_ = ((size_t)0ULL);
v___x_4093_ = lean_usize_of_nat(v___x_4083_);
v___x_4094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4072_, v_es_4078_, v___x_4092_, v___x_4093_, v_x_4074_, v___y_4075_, v___y_4076_);
lean_dec_ref(v_es_4078_);
return v___x_4094_;
}
}
else
{
size_t v___x_4095_; size_t v___x_4096_; lean_object* v___x_4097_; 
lean_del_object(v___x_4080_);
v___x_4095_ = ((size_t)0ULL);
v___x_4096_ = lean_usize_of_nat(v___x_4083_);
v___x_4097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4072_, v_es_4078_, v___x_4095_, v___x_4096_, v_x_4074_, v___y_4075_, v___y_4076_);
lean_dec_ref(v_es_4078_);
return v___x_4097_;
}
}
}
}
else
{
lean_object* v_ks_4099_; lean_object* v_vs_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v_ks_4099_ = lean_ctor_get(v_x_4073_, 0);
lean_inc_ref(v_ks_4099_);
v_vs_4100_ = lean_ctor_get(v_x_4073_, 1);
lean_inc_ref(v_vs_4100_);
lean_dec_ref(v_x_4073_);
v___x_4101_ = lean_unsigned_to_nat(0u);
v___x_4102_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4072_, v_ks_4099_, v_vs_4100_, v___x_4101_, v_x_4074_, v___y_4075_, v___y_4076_);
lean_dec_ref(v_vs_4100_);
lean_dec_ref(v_ks_4099_);
return v___x_4102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_4103_, lean_object* v_as_4104_, size_t v_i_4105_, size_t v_stop_4106_, lean_object* v_b_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_a_4112_; lean_object* v___y_4117_; uint8_t v___x_4119_; 
v___x_4119_ = lean_usize_dec_eq(v_i_4105_, v_stop_4106_);
if (v___x_4119_ == 0)
{
lean_object* v___x_4120_; 
v___x_4120_ = lean_array_uget_borrowed(v_as_4104_, v_i_4105_);
switch(lean_obj_tag(v___x_4120_))
{
case 0:
{
lean_object* v_key_4121_; lean_object* v_val_4122_; lean_object* v___x_4123_; 
v_key_4121_ = lean_ctor_get(v___x_4120_, 0);
v_val_4122_ = lean_ctor_get(v___x_4120_, 1);
lean_inc_ref(v_f_4103_);
lean_inc(v___y_4109_);
lean_inc_ref(v___y_4108_);
lean_inc(v_val_4122_);
lean_inc(v_key_4121_);
v___x_4123_ = lean_apply_6(v_f_4103_, v_b_4107_, v_key_4121_, v_val_4122_, v___y_4108_, v___y_4109_, lean_box(0));
v___y_4117_ = v___x_4123_;
goto v___jp_4116_;
}
case 1:
{
lean_object* v_node_4124_; lean_object* v___x_4125_; 
v_node_4124_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_node_4124_);
lean_inc_ref(v_f_4103_);
v___x_4125_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4103_, v_node_4124_, v_b_4107_, v___y_4108_, v___y_4109_);
v___y_4117_ = v___x_4125_;
goto v___jp_4116_;
}
default: 
{
v_a_4112_ = v_b_4107_;
goto v___jp_4111_;
}
}
}
else
{
lean_object* v___x_4126_; 
lean_dec_ref(v_f_4103_);
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v_b_4107_);
return v___x_4126_;
}
v___jp_4111_:
{
size_t v___x_4113_; size_t v___x_4114_; 
v___x_4113_ = ((size_t)1ULL);
v___x_4114_ = lean_usize_add(v_i_4105_, v___x_4113_);
v_i_4105_ = v___x_4114_;
v_b_4107_ = v_a_4112_;
goto _start;
}
v___jp_4116_:
{
if (lean_obj_tag(v___y_4117_) == 0)
{
lean_object* v_a_4118_; 
v_a_4118_ = lean_ctor_get(v___y_4117_, 0);
lean_inc(v_a_4118_);
lean_dec_ref(v___y_4117_);
v_a_4112_ = v_a_4118_;
goto v___jp_4111_;
}
else
{
lean_dec_ref(v_f_4103_);
return v___y_4117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_4127_, lean_object* v_as_4128_, lean_object* v_i_4129_, lean_object* v_stop_4130_, lean_object* v_b_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
size_t v_i_boxed_4135_; size_t v_stop_boxed_4136_; lean_object* v_res_4137_; 
v_i_boxed_4135_ = lean_unbox_usize(v_i_4129_);
lean_dec(v_i_4129_);
v_stop_boxed_4136_ = lean_unbox_usize(v_stop_4130_);
lean_dec(v_stop_4130_);
v_res_4137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4127_, v_as_4128_, v_i_boxed_4135_, v_stop_boxed_4136_, v_b_4131_, v___y_4132_, v___y_4133_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec_ref(v_as_4128_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_4138_, lean_object* v_x_4139_, lean_object* v_x_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4138_, v_x_4139_, v_x_4140_, v___y_4141_, v___y_4142_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object* v_f_4145_, lean_object* v_x_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v___x_4152_; 
lean_inc(v___y_4150_);
lean_inc_ref(v___y_4149_);
v___x_4152_ = lean_apply_5(v_f_4145_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, lean_box(0));
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object* v_f_4153_, lean_object* v_x_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4153_, v_x_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object* v_map_4161_, lean_object* v_f_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v___f_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___f_4166_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4166_, 0, v_f_4162_);
v___x_4167_ = lean_box(0);
v___x_4168_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v___f_4166_, v_map_4161_, v___x_4167_, v___y_4163_, v___y_4164_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object* v_map_4169_, lean_object* v_f_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4169_, v_f_4170_, v___y_4171_, v___y_4172_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
return v_res_4174_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4176_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0));
v___x_4177_ = l_Lean_stringToMessageData(v___x_4176_);
return v___x_4177_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_4179_ = l_Lean_stringToMessageData(v___x_4178_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t v_attrKind_4180_, lean_object* v_declName_4181_, lean_object* v_as_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
if (lean_obj_tag(v_as_4182_) == 0)
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
lean_dec(v_declName_4181_);
v___x_4186_ = lean_box(0);
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
return v___x_4187_;
}
else
{
lean_object* v_head_4188_; lean_object* v_tail_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4219_; 
v_head_4188_ = lean_ctor_get(v_as_4182_, 0);
v_tail_4189_ = lean_ctor_get(v_as_4182_, 1);
v_isSharedCheck_4219_ = !lean_is_exclusive(v_as_4182_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4191_ = v_as_4182_;
v_isShared_4192_ = v_isSharedCheck_4219_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_tail_4189_);
lean_inc(v_head_4188_);
lean_dec(v_as_4182_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4219_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___y_4194_; lean_object* v___x_4196_; 
v___x_4196_ = l_Lean_Parser_addToken(v_head_4188_, v_attrKind_4180_, v___y_4183_, v___y_4184_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_del_object(v___x_4191_);
v___y_4194_ = v___x_4196_;
goto v___jp_4193_;
}
else
{
lean_object* v_a_4197_; uint8_t v___y_4199_; uint8_t v___x_4217_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
v___x_4217_ = l_Lean_Exception_isInterrupt(v_a_4197_);
if (v___x_4217_ == 0)
{
uint8_t v___x_4218_; 
lean_inc(v_a_4197_);
v___x_4218_ = l_Lean_Exception_isRuntime(v_a_4197_);
v___y_4199_ = v___x_4218_;
goto v___jp_4198_;
}
else
{
v___y_4199_ = v___x_4217_;
goto v___jp_4198_;
}
v___jp_4198_:
{
if (v___y_4199_ == 0)
{
if (lean_obj_tag(v_a_4197_) == 0)
{
lean_object* v_msg_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4215_; 
lean_dec_ref(v___x_4196_);
v_msg_4200_ = lean_ctor_get(v_a_4197_, 1);
v_isSharedCheck_4215_ = !lean_is_exclusive(v_a_4197_);
if (v_isSharedCheck_4215_ == 0)
{
lean_object* v_unused_4216_; 
v_unused_4216_ = lean_ctor_get(v_a_4197_, 0);
lean_dec(v_unused_4216_);
v___x_4202_ = v_a_4197_;
v_isShared_4203_ = v_isSharedCheck_4215_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_msg_4200_);
lean_dec(v_a_4197_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4215_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4207_; 
v___x_4204_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1);
lean_inc(v_declName_4181_);
v___x_4205_ = l_Lean_MessageData_ofConstName(v_declName_4181_, v___y_4199_);
if (v_isShared_4203_ == 0)
{
lean_ctor_set_tag(v___x_4202_, 7);
lean_ctor_set(v___x_4202_, 1, v___x_4205_);
lean_ctor_set(v___x_4202_, 0, v___x_4204_);
v___x_4207_ = v___x_4202_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4204_);
lean_ctor_set(v_reuseFailAlloc_4214_, 1, v___x_4205_);
v___x_4207_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
lean_object* v___x_4208_; lean_object* v___x_4210_; 
v___x_4208_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2);
if (v_isShared_4192_ == 0)
{
lean_ctor_set_tag(v___x_4191_, 7);
lean_ctor_set(v___x_4191_, 1, v___x_4208_);
lean_ctor_set(v___x_4191_, 0, v___x_4207_);
v___x_4210_ = v___x_4191_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4207_);
lean_ctor_set(v_reuseFailAlloc_4213_, 1, v___x_4208_);
v___x_4210_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4210_);
lean_ctor_set(v___x_4211_, 1, v_msg_4200_);
v___x_4212_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4211_, v___y_4183_, v___y_4184_);
v___y_4194_ = v___x_4212_;
goto v___jp_4193_;
}
}
}
}
else
{
lean_dec(v_a_4197_);
lean_del_object(v___x_4191_);
v___y_4194_ = v___x_4196_;
goto v___jp_4193_;
}
}
else
{
lean_dec(v_a_4197_);
lean_del_object(v___x_4191_);
v___y_4194_ = v___x_4196_;
goto v___jp_4193_;
}
}
}
v___jp_4193_:
{
if (lean_obj_tag(v___y_4194_) == 0)
{
lean_dec_ref(v___y_4194_);
v_as_4182_ = v_tail_4189_;
goto _start;
}
else
{
lean_dec(v_tail_4189_);
lean_dec(v_declName_4181_);
return v___y_4194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object* v_attrKind_4220_, lean_object* v_declName_4221_, lean_object* v_as_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
uint8_t v_attrKind_boxed_4226_; lean_object* v_res_4227_; 
v_attrKind_boxed_4226_ = lean_unbox(v_attrKind_4220_);
v_res_4227_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_boxed_4226_, v_declName_4221_, v_as_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object* v_catName_4229_, lean_object* v_declName_4230_, lean_object* v_stx_4231_, uint8_t v_attrKind_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___x_4241_; 
v___x_4241_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4231_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v_env_4245_; lean_object* v___x_4246_; lean_object* v_ext_4247_; lean_object* v_toEnvExtension_4248_; lean_object* v_asyncMode_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v_categories_4252_; lean_object* v_env_4253_; lean_object* v_options_4254_; lean_object* v_ref_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref(v___x_4241_);
v___x_4243_ = lean_st_ref_get(v_a_4234_);
v___x_4244_ = lean_st_ref_get(v_a_4234_);
v_env_4245_ = lean_ctor_get(v___x_4243_, 0);
lean_inc_ref(v_env_4245_);
lean_dec(v___x_4243_);
v___x_4246_ = l_Lean_Parser_parserExtension;
v_ext_4247_ = lean_ctor_get(v___x_4246_, 1);
v_toEnvExtension_4248_ = lean_ctor_get(v_ext_4247_, 0);
v_asyncMode_4249_ = lean_ctor_get(v_toEnvExtension_4248_, 2);
v___x_4250_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4251_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4250_, v___x_4246_, v_env_4245_, v_asyncMode_4249_);
v_categories_4252_ = lean_ctor_get(v___x_4251_, 2);
lean_inc_ref_n(v_categories_4252_, 2);
lean_dec(v___x_4251_);
v_env_4253_ = lean_ctor_get(v___x_4244_, 0);
lean_inc_ref(v_env_4253_);
lean_dec(v___x_4244_);
v_options_4254_ = lean_ctor_get(v_a_4233_, 2);
v_ref_4255_ = lean_ctor_get(v_a_4233_, 5);
lean_inc_ref(v_options_4254_);
v___x_4256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4256_, 0, v_env_4253_);
lean_ctor_set(v___x_4256_, 1, v_options_4254_);
lean_inc(v_declName_4230_);
v___x_4257_ = l_Lean_Parser_mkParserOfConstant(v_categories_4252_, v_declName_4230_, v___x_4256_);
lean_dec_ref(v___x_4256_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v_snd_4259_; lean_object* v_info_4260_; lean_object* v_fst_4261_; lean_object* v_collectTokens_4262_; lean_object* v_collectKinds_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref(v___x_4257_);
v_snd_4259_ = lean_ctor_get(v_a_4258_, 1);
lean_inc(v_snd_4259_);
v_info_4260_ = lean_ctor_get(v_snd_4259_, 0);
v_fst_4261_ = lean_ctor_get(v_a_4258_, 0);
lean_inc(v_fst_4261_);
lean_dec(v_a_4258_);
v_collectTokens_4262_ = lean_ctor_get(v_info_4260_, 0);
v_collectKinds_4263_ = lean_ctor_get(v_info_4260_, 1);
v___x_4264_ = lean_box(0);
lean_inc_ref(v_collectTokens_4262_);
v___x_4265_ = lean_apply_1(v_collectTokens_4262_, v___x_4264_);
lean_inc(v_declName_4230_);
v___x_4266_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4232_, v_declName_4230_, v___x_4265_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v___f_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
lean_dec_ref(v___x_4266_);
v___f_4267_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0));
v___x_4268_ = lean_obj_once(&l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
lean_inc_ref(v_collectKinds_4263_);
v___x_4269_ = lean_apply_1(v_collectKinds_4263_, v___x_4268_);
v___x_4270_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v___x_4269_, v___f_4267_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v___x_4271_; uint8_t v___x_4272_; uint8_t v___x_4273_; lean_object* v___x_4274_; 
lean_dec_ref(v___x_4270_);
lean_inc(v_a_4242_);
lean_inc(v_snd_4259_);
lean_inc_n(v_declName_4230_, 2);
lean_inc_n(v_catName_4229_, 2);
v___x_4271_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_4271_, 0, v_catName_4229_);
lean_ctor_set(v___x_4271_, 1, v_declName_4230_);
lean_ctor_set(v___x_4271_, 2, v_snd_4259_);
lean_ctor_set(v___x_4271_, 3, v_a_4242_);
v___x_4272_ = lean_unbox(v_fst_4261_);
lean_ctor_set_uint8(v___x_4271_, sizeof(void*)*4, v___x_4272_);
v___x_4273_ = lean_unbox(v_fst_4261_);
lean_dec(v_fst_4261_);
v___x_4274_ = l_Lean_Parser_addParser(v_categories_4252_, v_catName_4229_, v_declName_4230_, v___x_4273_, v_snd_4259_, v_a_4242_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4284_; 
lean_dec_ref(v___x_4271_);
lean_dec(v_declName_4230_);
lean_dec(v_catName_4229_);
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4277_ = v___x_4274_;
v_isShared_4278_ = v_isSharedCheck_4284_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4274_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4284_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
lean_ctor_set_tag(v___x_4277_, 3);
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = l_Lean_MessageData_ofFormat(v___x_4280_);
v___x_4282_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4281_, v_a_4233_, v_a_4234_);
return v___x_4282_;
}
}
}
else
{
lean_object* v___x_4285_; 
lean_dec_ref(v___x_4274_);
v___x_4285_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_4246_, v___x_4271_, v_attrKind_4232_, v_a_4233_, v_a_4234_);
lean_dec_ref(v___x_4285_);
v___y_4237_ = v_a_4233_;
v___y_4238_ = v_a_4234_;
goto v___jp_4236_;
}
}
else
{
lean_dec(v_fst_4261_);
lean_dec(v_snd_4259_);
lean_dec_ref(v_categories_4252_);
lean_dec(v_a_4242_);
lean_dec(v_declName_4230_);
lean_dec(v_catName_4229_);
return v___x_4270_;
}
}
else
{
lean_dec(v_fst_4261_);
lean_dec(v_snd_4259_);
lean_dec_ref(v_categories_4252_);
lean_dec(v_a_4242_);
lean_dec(v_declName_4230_);
lean_dec(v_catName_4229_);
return v___x_4266_;
}
}
else
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4297_; 
lean_dec_ref(v_categories_4252_);
lean_dec(v_a_4242_);
lean_dec(v_declName_4230_);
lean_dec(v_catName_4229_);
v_a_4286_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4288_ = v___x_4257_;
v_isShared_4289_ = v_isSharedCheck_4297_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4257_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4297_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4295_; 
v___x_4290_ = lean_io_error_to_string(v_a_4286_);
v___x_4291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4290_);
v___x_4292_ = l_Lean_MessageData_ofFormat(v___x_4291_);
lean_inc(v_ref_4255_);
v___x_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4293_, 0, v_ref_4255_);
lean_ctor_set(v___x_4293_, 1, v___x_4292_);
if (v_isShared_4289_ == 0)
{
lean_ctor_set(v___x_4288_, 0, v___x_4293_);
v___x_4295_ = v___x_4288_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4293_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
lean_dec(v_declName_4230_);
lean_dec(v_catName_4229_);
v_a_4298_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4241_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4241_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
v___jp_4236_:
{
uint8_t v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = 0;
v___x_4240_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4229_, v_declName_4230_, v___x_4239_, v___y_4237_, v___y_4238_);
return v___x_4240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object* v_catName_4306_, lean_object* v_declName_4307_, lean_object* v_stx_4308_, lean_object* v_attrKind_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_){
_start:
{
uint8_t v_attrKind_boxed_4313_; lean_object* v_res_4314_; 
v_attrKind_boxed_4313_ = lean_unbox(v_attrKind_4309_);
v_res_4314_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4306_, v_declName_4307_, v_stx_4308_, v_attrKind_boxed_4313_, v_a_4310_, v_a_4311_);
lean_dec(v_a_4311_);
lean_dec_ref(v_a_4310_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* v___attrName_4315_, lean_object* v_catName_4316_, lean_object* v_declName_4317_, lean_object* v_stx_4318_, uint8_t v_attrKind_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v___x_4323_; 
v___x_4323_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4316_, v_declName_4317_, v_stx_4318_, v_attrKind_4319_, v_a_4320_, v_a_4321_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* v___attrName_4324_, lean_object* v_catName_4325_, lean_object* v_declName_4326_, lean_object* v_stx_4327_, lean_object* v_attrKind_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_){
_start:
{
uint8_t v_attrKind_boxed_4332_; lean_object* v_res_4333_; 
v_attrKind_boxed_4332_ = lean_unbox(v_attrKind_4328_);
v_res_4333_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4324_, v_catName_4325_, v_declName_4326_, v_stx_4327_, v_attrKind_boxed_4332_, v_a_4329_, v_a_4330_);
lean_dec(v_a_4330_);
lean_dec_ref(v_a_4329_);
lean_dec(v___attrName_4324_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object* v_00_u03b2_4334_, lean_object* v_map_4335_, lean_object* v_f_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v___x_4340_; 
v___x_4340_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4335_, v_f_4336_, v___y_4337_, v___y_4338_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b2_4341_, lean_object* v_map_4342_, lean_object* v_f_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(v_00_u03b2_4341_, v_map_4342_, v_f_4343_, v___y_4344_, v___y_4345_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object* v_map_4348_, lean_object* v_f_4349_, lean_object* v_init_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4349_, v_map_4348_, v_init_4350_, v___y_4351_, v___y_4352_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object* v_map_4355_, lean_object* v_f_4356_, lean_object* v_init_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4355_, v_f_4356_, v_init_4357_, v___y_4358_, v___y_4359_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object* v_00_u03c3_4362_, lean_object* v_00_u03b2_4363_, lean_object* v_map_4364_, lean_object* v_f_4365_, lean_object* v_init_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4365_, v_map_4364_, v_init_4366_, v___y_4367_, v___y_4368_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object* v_00_u03c3_4371_, lean_object* v_00_u03b2_4372_, lean_object* v_map_4373_, lean_object* v_f_4374_, lean_object* v_init_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(v_00_u03c3_4371_, v_00_u03b2_4372_, v_map_4373_, v_f_4374_, v_init_4375_, v___y_4376_, v___y_4377_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_4380_, lean_object* v_00_u03b1_4381_, lean_object* v_00_u03b2_4382_, lean_object* v_f_4383_, lean_object* v_x_4384_, lean_object* v_x_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_){
_start:
{
lean_object* v___x_4389_; 
v___x_4389_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4383_, v_x_4384_, v_x_4385_, v___y_4386_, v___y_4387_);
return v___x_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03c3_4390_, lean_object* v_00_u03b1_4391_, lean_object* v_00_u03b2_4392_, lean_object* v_f_4393_, lean_object* v_x_4394_, lean_object* v_x_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(v_00_u03c3_4390_, v_00_u03b1_4391_, v_00_u03b2_4392_, v_f_4393_, v_x_4394_, v_x_4395_, v___y_4396_, v___y_4397_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4400_, lean_object* v_00_u03b2_4401_, lean_object* v_00_u03c3_4402_, lean_object* v_f_4403_, lean_object* v_as_4404_, size_t v_i_4405_, size_t v_stop_4406_, lean_object* v_b_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v___x_4411_; 
v___x_4411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4403_, v_as_4404_, v_i_4405_, v_stop_4406_, v_b_4407_, v___y_4408_, v___y_4409_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4412_, lean_object* v_00_u03b2_4413_, lean_object* v_00_u03c3_4414_, lean_object* v_f_4415_, lean_object* v_as_4416_, lean_object* v_i_4417_, lean_object* v_stop_4418_, lean_object* v_b_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
size_t v_i_boxed_4423_; size_t v_stop_boxed_4424_; lean_object* v_res_4425_; 
v_i_boxed_4423_ = lean_unbox_usize(v_i_4417_);
lean_dec(v_i_4417_);
v_stop_boxed_4424_ = lean_unbox_usize(v_stop_4418_);
lean_dec(v_stop_4418_);
v_res_4425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4412_, v_00_u03b2_4413_, v_00_u03c3_4414_, v_f_4415_, v_as_4416_, v_i_boxed_4423_, v_stop_boxed_4424_, v_b_4419_, v___y_4420_, v___y_4421_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec_ref(v_as_4416_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_4426_, lean_object* v_00_u03b1_4427_, lean_object* v_00_u03b2_4428_, lean_object* v_f_4429_, lean_object* v_keys_4430_, lean_object* v_vals_4431_, lean_object* v_heq_4432_, lean_object* v_i_4433_, lean_object* v_acc_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v___x_4438_; 
v___x_4438_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4429_, v_keys_4430_, v_vals_4431_, v_i_4433_, v_acc_4434_, v___y_4435_, v___y_4436_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_4439_, lean_object* v_00_u03b1_4440_, lean_object* v_00_u03b2_4441_, lean_object* v_f_4442_, lean_object* v_keys_4443_, lean_object* v_vals_4444_, lean_object* v_heq_4445_, lean_object* v_i_4446_, lean_object* v_acc_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4439_, v_00_u03b1_4440_, v_00_u03b2_4441_, v_f_4442_, v_keys_4443_, v_vals_4444_, v_heq_4445_, v_i_4446_, v_acc_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec_ref(v_vals_4444_);
lean_dec_ref(v_keys_4443_);
return v_res_4451_;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___auto__1(void){
_start:
{
lean_object* v___x_4452_; 
v___x_4452_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object* v_catName_4453_, lean_object* v_declName_4454_, lean_object* v_stx_4455_, uint8_t v_attrKind_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v___x_4460_; 
v___x_4460_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4453_, v_declName_4454_, v_stx_4455_, v_attrKind_4456_, v___y_4457_, v___y_4458_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object* v_catName_4461_, lean_object* v_declName_4462_, lean_object* v_stx_4463_, lean_object* v_attrKind_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
uint8_t v_attrKind_boxed_4468_; lean_object* v_res_4469_; 
v_attrKind_boxed_4468_ = lean_unbox(v_attrKind_4464_);
v_res_4469_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4461_, v_declName_4462_, v_stx_4463_, v_attrKind_boxed_4468_, v___y_4465_, v___y_4466_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* v_attrName_4471_, lean_object* v_catName_4472_, lean_object* v_ref_4473_){
_start:
{
lean_object* v___f_4474_; lean_object* v___f_4475_; lean_object* v___x_4476_; uint8_t v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v___f_4474_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4474_, 0, v_catName_4472_);
lean_inc(v_attrName_4471_);
v___f_4475_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4475_, 0, v_attrName_4471_);
v___x_4476_ = ((lean_object*)(l_Lean_Parser_mkParserAttributeImpl___closed__0));
v___x_4477_ = 1;
v___x_4478_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4478_, 0, v_ref_4473_);
lean_ctor_set(v___x_4478_, 1, v_attrName_4471_);
lean_ctor_set(v___x_4478_, 2, v___x_4476_);
lean_ctor_set_uint8(v___x_4478_, sizeof(void*)*3, v___x_4477_);
v___x_4479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
lean_ctor_set(v___x_4479_, 1, v___f_4474_);
lean_ctor_set(v___x_4479_, 2, v___f_4475_);
return v___x_4479_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4480_; 
v___x_4480_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* v_attrName_4481_, lean_object* v_catName_4482_, lean_object* v_ref_4483_){
_start:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; 
v___x_4485_ = l_Lean_Parser_mkParserAttributeImpl(v_attrName_4481_, v_catName_4482_, v_ref_4483_);
v___x_4486_ = l_Lean_registerBuiltinAttribute(v___x_4485_);
return v___x_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object* v_attrName_4487_, lean_object* v_catName_4488_, lean_object* v_ref_4489_, lean_object* v_a_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4487_, v_catName_4488_, v_ref_4489_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object* v_ref_4495_, lean_object* v_args_4496_){
_start:
{
if (lean_obj_tag(v_args_4496_) == 1)
{
lean_object* v_head_4499_; 
v_head_4499_ = lean_ctor_get(v_args_4496_, 0);
lean_inc(v_head_4499_);
if (lean_obj_tag(v_head_4499_) == 2)
{
lean_object* v_tail_4500_; 
v_tail_4500_ = lean_ctor_get(v_args_4496_, 1);
lean_inc(v_tail_4500_);
lean_dec_ref(v_args_4496_);
if (lean_obj_tag(v_tail_4500_) == 1)
{
lean_object* v_head_4501_; 
v_head_4501_ = lean_ctor_get(v_tail_4500_, 0);
lean_inc(v_head_4501_);
if (lean_obj_tag(v_head_4501_) == 2)
{
lean_object* v_tail_4502_; 
v_tail_4502_ = lean_ctor_get(v_tail_4500_, 1);
lean_inc(v_tail_4502_);
lean_dec_ref(v_tail_4500_);
if (lean_obj_tag(v_tail_4502_) == 0)
{
lean_object* v_v_4503_; lean_object* v_v_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4512_; 
v_v_4503_ = lean_ctor_get(v_head_4499_, 0);
lean_inc(v_v_4503_);
lean_dec_ref(v_head_4499_);
v_v_4504_ = lean_ctor_get(v_head_4501_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v_head_4501_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4506_ = v_head_4501_;
v_isShared_4507_ = v_isSharedCheck_4512_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_v_4504_);
lean_dec(v_head_4501_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4512_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4508_ = l_Lean_Parser_mkParserAttributeImpl(v_v_4503_, v_v_4504_, v_ref_4495_);
if (v_isShared_4507_ == 0)
{
lean_ctor_set_tag(v___x_4506_, 1);
lean_ctor_set(v___x_4506_, 0, v___x_4508_);
v___x_4510_ = v___x_4506_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4508_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
else
{
lean_dec_ref(v_head_4501_);
lean_dec(v_tail_4502_);
lean_dec_ref(v_head_4499_);
lean_dec(v_ref_4495_);
goto v___jp_4497_;
}
}
else
{
lean_dec(v_head_4501_);
lean_dec_ref(v_tail_4500_);
lean_dec_ref(v_head_4499_);
lean_dec(v_ref_4495_);
goto v___jp_4497_;
}
}
else
{
lean_dec(v_tail_4500_);
lean_dec_ref(v_head_4499_);
lean_dec(v_ref_4495_);
goto v___jp_4497_;
}
}
else
{
lean_dec(v_head_4499_);
lean_dec_ref(v_args_4496_);
lean_dec(v_ref_4495_);
goto v___jp_4497_;
}
}
else
{
lean_dec(v_args_4496_);
lean_dec(v_ref_4495_);
goto v___jp_4497_;
}
v___jp_4497_:
{
lean_object* v___x_4498_; 
v___x_4498_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
return v___x_4498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___f_4518_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4519_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4520_ = l_Lean_registerAttributeImplBuilder(v___x_4519_, v___f_4518_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object* v_a_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
return v_res_4522_;
}
}
static lean_object* _init_l_Lean_Parser_registerParserCategory___auto__1(void){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object* v_env_4524_, lean_object* v_attrName_4525_, lean_object* v_catName_4526_, uint8_t v_behavior_4527_, lean_object* v_ref_4528_){
_start:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
lean_inc(v_ref_4528_);
lean_inc(v_catName_4526_);
v___x_4530_ = l_Lean_Parser_addParserCategory(v_env_4524_, v_catName_4526_, v_ref_4528_, v_behavior_4527_);
v___x_4531_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_4530_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4545_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4534_ = v___x_4531_;
v_isShared_4535_ = v_isSharedCheck_4545_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_a_4532_);
lean_dec(v___x_4531_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4545_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4536_; lean_object* v___x_4538_; 
v___x_4536_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
if (v_isShared_4535_ == 0)
{
lean_ctor_set_tag(v___x_4534_, 2);
lean_ctor_set(v___x_4534_, 0, v_attrName_4525_);
v___x_4538_ = v___x_4534_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_attrName_4525_);
v___x_4538_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4539_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4539_, 0, v_catName_4526_);
v___x_4540_ = lean_box(0);
v___x_4541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4539_);
lean_ctor_set(v___x_4541_, 1, v___x_4540_);
v___x_4542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4538_);
lean_ctor_set(v___x_4542_, 1, v___x_4541_);
v___x_4543_ = l_Lean_registerAttributeOfBuilder(v_a_4532_, v___x_4536_, v_ref_4528_, v___x_4542_);
return v___x_4543_;
}
}
}
else
{
lean_dec(v_ref_4528_);
lean_dec(v_catName_4526_);
lean_dec(v_attrName_4525_);
return v___x_4531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* v_env_4546_, lean_object* v_attrName_4547_, lean_object* v_catName_4548_, lean_object* v_behavior_4549_, lean_object* v_ref_4550_, lean_object* v_a_4551_){
_start:
{
uint8_t v_behavior_boxed_4552_; lean_object* v_res_4553_; 
v_behavior_boxed_4552_ = lean_unbox(v_behavior_4549_);
v_res_4553_ = l_Lean_Parser_registerParserCategory(v_env_4546_, v_attrName_4547_, v_catName_4548_, v_behavior_boxed_4552_, v_ref_4550_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4576_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4577_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4578_ = 0;
v___x_4579_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4580_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4576_, v___x_4577_, v___x_4578_, v___x_4579_);
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object* v_a_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
return v_res_4582_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4588_ = lean_unsigned_to_nat(3431364690u);
v___x_4589_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4590_ = l_Lean_Name_num___override(v___x_4589_, v___x_4588_);
return v___x_4590_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4591_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4592_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4593_ = l_Lean_Name_str___override(v___x_4592_, v___x_4591_);
return v___x_4593_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4594_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4595_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4596_ = l_Lean_Name_str___override(v___x_4595_, v___x_4594_);
return v___x_4596_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4597_ = lean_unsigned_to_nat(2u);
v___x_4598_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4599_ = l_Lean_Name_num___override(v___x_4598_, v___x_4597_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; 
v___x_4601_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4602_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4603_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4604_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4601_, v___x_4602_, v___x_4603_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object* v_a_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
return v_res_4606_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4616_ = lean_unsigned_to_nat(2342493449u);
v___x_4617_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4618_ = l_Lean_Name_num___override(v___x_4617_, v___x_4616_);
return v___x_4618_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4619_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4620_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4621_ = l_Lean_Name_str___override(v___x_4620_, v___x_4619_);
return v___x_4621_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4622_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4623_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4624_ = l_Lean_Name_str___override(v___x_4623_, v___x_4622_);
return v___x_4624_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4625_ = lean_unsigned_to_nat(2u);
v___x_4626_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4627_ = l_Lean_Name_num___override(v___x_4626_, v___x_4625_);
return v___x_4627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4629_; lean_object* v___x_4630_; uint8_t v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4629_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4630_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4631_ = 0;
v___x_4632_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4633_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4629_, v___x_4630_, v___x_4631_, v___x_4632_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object* v_a_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
return v_res_4635_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4641_ = lean_unsigned_to_nat(3226070615u);
v___x_4642_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4643_ = l_Lean_Name_num___override(v___x_4642_, v___x_4641_);
return v___x_4643_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4644_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4645_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4646_ = l_Lean_Name_str___override(v___x_4645_, v___x_4644_);
return v___x_4646_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4647_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4648_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4649_ = l_Lean_Name_str___override(v___x_4648_, v___x_4647_);
return v___x_4649_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4650_ = lean_unsigned_to_nat(2u);
v___x_4651_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4652_ = l_Lean_Name_num___override(v___x_4651_, v___x_4650_);
return v___x_4652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4654_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4655_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4656_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4657_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4654_, v___x_4655_, v___x_4656_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object* v_a_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* v_rbp_4660_){
_start:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4661_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4662_ = l_Lean_Parser_categoryParser(v___x_4661_, v_rbp_4660_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t v_addOpenSimple_4663_, lean_object* v_x_4664_, lean_object* v_x_4665_){
_start:
{
if (lean_obj_tag(v_x_4665_) == 0)
{
return v_x_4664_;
}
else
{
lean_object* v_head_4666_; lean_object* v_tail_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4690_; 
v_head_4666_ = lean_ctor_get(v_x_4665_, 0);
v_tail_4667_ = lean_ctor_get(v_x_4665_, 1);
v_isSharedCheck_4690_ = !lean_is_exclusive(v_x_4665_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4669_ = v_x_4665_;
v_isShared_4670_ = v_isSharedCheck_4690_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_tail_4667_);
lean_inc(v_head_4666_);
lean_dec(v_x_4665_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4690_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v_fst_4671_; lean_object* v_snd_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4689_; 
v_fst_4671_ = lean_ctor_get(v_x_4664_, 0);
v_snd_4672_ = lean_ctor_get(v_x_4664_, 1);
v_isSharedCheck_4689_ = !lean_is_exclusive(v_x_4664_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4674_ = v_x_4664_;
v_isShared_4675_ = v_isSharedCheck_4689_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_snd_4672_);
lean_inc(v_fst_4671_);
lean_dec(v_x_4664_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4689_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___y_4677_; 
if (v_addOpenSimple_4663_ == 0)
{
lean_del_object(v___x_4669_);
v___y_4677_ = v_snd_4672_;
goto v___jp_4676_;
}
else
{
lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4687_; 
v___x_4684_ = lean_box(0);
lean_inc(v_head_4666_);
v___x_4685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4685_, 0, v_head_4666_);
lean_ctor_set(v___x_4685_, 1, v___x_4684_);
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 1, v_snd_4672_);
lean_ctor_set(v___x_4669_, 0, v___x_4685_);
v___x_4687_ = v___x_4669_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4685_);
lean_ctor_set(v_reuseFailAlloc_4688_, 1, v_snd_4672_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
v___y_4677_ = v___x_4687_;
goto v___jp_4676_;
}
}
v___jp_4676_:
{
lean_object* v___x_4678_; lean_object* v_env_4679_; lean_object* v___x_4681_; 
v___x_4678_ = l_Lean_Parser_parserExtension;
v_env_4679_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v___x_4678_, v_fst_4671_, v_head_4666_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 1, v___y_4677_);
lean_ctor_set(v___x_4674_, 0, v_env_4679_);
v___x_4681_ = v___x_4674_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_env_4679_);
lean_ctor_set(v_reuseFailAlloc_4683_, 1, v___y_4677_);
v___x_4681_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
v_x_4664_ = v___x_4681_;
v_x_4665_ = v_tail_4667_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object* v_addOpenSimple_4691_, lean_object* v_x_4692_, lean_object* v_x_4693_){
_start:
{
uint8_t v_addOpenSimple_boxed_4694_; lean_object* v_res_4695_; 
v_addOpenSimple_boxed_4694_ = lean_unbox(v_addOpenSimple_4691_);
v_res_4695_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_boxed_4694_, v_x_4692_, v_x_4693_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t v_addOpenSimple_4696_, lean_object* v_as_4697_, size_t v_i_4698_, size_t v_stop_4699_, lean_object* v_b_4700_){
_start:
{
uint8_t v___x_4701_; 
v___x_4701_ = lean_usize_dec_eq(v_i_4698_, v_stop_4699_);
if (v___x_4701_ == 0)
{
lean_object* v_toParserModuleContext_4702_; lean_object* v_toInputContext_4703_; lean_object* v_toCacheableParserContext_4704_; lean_object* v_tokens_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4732_; 
v_toParserModuleContext_4702_ = lean_ctor_get(v_b_4700_, 1);
v_toInputContext_4703_ = lean_ctor_get(v_b_4700_, 0);
v_toCacheableParserContext_4704_ = lean_ctor_get(v_b_4700_, 2);
v_tokens_4705_ = lean_ctor_get(v_b_4700_, 3);
v_isSharedCheck_4732_ = !lean_is_exclusive(v_b_4700_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4707_ = v_b_4700_;
v_isShared_4708_ = v_isSharedCheck_4732_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_tokens_4705_);
lean_inc(v_toCacheableParserContext_4704_);
lean_inc(v_toParserModuleContext_4702_);
lean_inc(v_toInputContext_4703_);
lean_dec(v_b_4700_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4732_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v_env_4709_; lean_object* v_options_4710_; lean_object* v_currNamespace_4711_; lean_object* v_openDecls_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4731_; 
v_env_4709_ = lean_ctor_get(v_toParserModuleContext_4702_, 0);
v_options_4710_ = lean_ctor_get(v_toParserModuleContext_4702_, 1);
v_currNamespace_4711_ = lean_ctor_get(v_toParserModuleContext_4702_, 2);
v_openDecls_4712_ = lean_ctor_get(v_toParserModuleContext_4702_, 3);
v_isSharedCheck_4731_ = !lean_is_exclusive(v_toParserModuleContext_4702_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4714_ = v_toParserModuleContext_4702_;
v_isShared_4715_ = v_isSharedCheck_4731_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_openDecls_4712_);
lean_inc(v_currNamespace_4711_);
lean_inc(v_options_4710_);
lean_inc(v_env_4709_);
lean_dec(v_toParserModuleContext_4702_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4731_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4716_; lean_object* v_nss_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v_fst_4720_; lean_object* v_snd_4721_; lean_object* v___x_4723_; 
v___x_4716_ = lean_array_uget_borrowed(v_as_4697_, v_i_4698_);
lean_inc(v___x_4716_);
lean_inc(v_openDecls_4712_);
lean_inc(v_currNamespace_4711_);
lean_inc_ref(v_env_4709_);
v_nss_4717_ = l_Lean_ResolveName_resolveNamespace(v_env_4709_, v_currNamespace_4711_, v_openDecls_4712_, v___x_4716_);
v___x_4718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4718_, 0, v_env_4709_);
lean_ctor_set(v___x_4718_, 1, v_openDecls_4712_);
v___x_4719_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4696_, v___x_4718_, v_nss_4717_);
v_fst_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_fst_4720_);
v_snd_4721_ = lean_ctor_get(v___x_4719_, 1);
lean_inc(v_snd_4721_);
lean_dec_ref(v___x_4719_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 3, v_snd_4721_);
lean_ctor_set(v___x_4714_, 0, v_fst_4720_);
v___x_4723_ = v___x_4714_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_fst_4720_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_options_4710_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_currNamespace_4711_);
lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_snd_4721_);
v___x_4723_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
lean_object* v___x_4725_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 1, v___x_4723_);
v___x_4725_ = v___x_4707_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_toInputContext_4703_);
lean_ctor_set(v_reuseFailAlloc_4729_, 1, v___x_4723_);
lean_ctor_set(v_reuseFailAlloc_4729_, 2, v_toCacheableParserContext_4704_);
lean_ctor_set(v_reuseFailAlloc_4729_, 3, v_tokens_4705_);
v___x_4725_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
size_t v___x_4726_; size_t v___x_4727_; 
v___x_4726_ = ((size_t)1ULL);
v___x_4727_ = lean_usize_add(v_i_4698_, v___x_4726_);
v_i_4698_ = v___x_4727_;
v_b_4700_ = v___x_4725_;
goto _start;
}
}
}
}
}
else
{
return v_b_4700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object* v_addOpenSimple_4733_, lean_object* v_as_4734_, lean_object* v_i_4735_, lean_object* v_stop_4736_, lean_object* v_b_4737_){
_start:
{
uint8_t v_addOpenSimple_boxed_4738_; size_t v_i_boxed_4739_; size_t v_stop_boxed_4740_; lean_object* v_res_4741_; 
v_addOpenSimple_boxed_4738_ = lean_unbox(v_addOpenSimple_4733_);
v_i_boxed_4739_ = lean_unbox_usize(v_i_4735_);
lean_dec(v_i_4735_);
v_stop_boxed_4740_ = lean_unbox_usize(v_stop_4736_);
lean_dec(v_stop_4736_);
v_res_4741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_boxed_4738_, v_as_4734_, v_i_boxed_4739_, v_stop_boxed_4740_, v_b_4737_);
lean_dec_ref(v_as_4734_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object* v___x_4742_, lean_object* v_ids_4743_, uint8_t v_addOpenSimple_4744_, lean_object* v_c_4745_){
_start:
{
lean_object* v___y_4747_; lean_object* v___x_4766_; lean_object* v___x_4767_; uint8_t v___x_4768_; 
v___x_4766_ = lean_unsigned_to_nat(0u);
v___x_4767_ = lean_array_get_size(v_ids_4743_);
v___x_4768_ = lean_nat_dec_lt(v___x_4766_, v___x_4767_);
if (v___x_4768_ == 0)
{
v___y_4747_ = v_c_4745_;
goto v___jp_4746_;
}
else
{
uint8_t v___x_4769_; 
v___x_4769_ = lean_nat_dec_le(v___x_4767_, v___x_4767_);
if (v___x_4769_ == 0)
{
if (v___x_4768_ == 0)
{
v___y_4747_ = v_c_4745_;
goto v___jp_4746_;
}
else
{
size_t v___x_4770_; size_t v___x_4771_; lean_object* v___x_4772_; 
v___x_4770_ = ((size_t)0ULL);
v___x_4771_ = lean_usize_of_nat(v___x_4767_);
v___x_4772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4744_, v_ids_4743_, v___x_4770_, v___x_4771_, v_c_4745_);
v___y_4747_ = v___x_4772_;
goto v___jp_4746_;
}
}
else
{
size_t v___x_4773_; size_t v___x_4774_; lean_object* v___x_4775_; 
v___x_4773_ = ((size_t)0ULL);
v___x_4774_ = lean_usize_of_nat(v___x_4767_);
v___x_4775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4744_, v_ids_4743_, v___x_4773_, v___x_4774_, v_c_4745_);
v___y_4747_ = v___x_4775_;
goto v___jp_4746_;
}
}
v___jp_4746_:
{
lean_object* v_toParserModuleContext_4748_; lean_object* v_toInputContext_4749_; lean_object* v_toCacheableParserContext_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4764_; 
v_toParserModuleContext_4748_ = lean_ctor_get(v___y_4747_, 1);
v_toInputContext_4749_ = lean_ctor_get(v___y_4747_, 0);
v_toCacheableParserContext_4750_ = lean_ctor_get(v___y_4747_, 2);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___y_4747_);
if (v_isSharedCheck_4764_ == 0)
{
lean_object* v_unused_4765_; 
v_unused_4765_ = lean_ctor_get(v___y_4747_, 3);
lean_dec(v_unused_4765_);
v___x_4752_ = v___y_4747_;
v_isShared_4753_ = v_isSharedCheck_4764_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_toCacheableParserContext_4750_);
lean_inc(v_toParserModuleContext_4748_);
lean_inc(v_toInputContext_4749_);
lean_dec(v___y_4747_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4764_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v_env_4754_; lean_object* v___x_4755_; lean_object* v_ext_4756_; lean_object* v_toEnvExtension_4757_; lean_object* v_asyncMode_4758_; lean_object* v___x_4759_; lean_object* v_tokens_4760_; lean_object* v___x_4762_; 
v_env_4754_ = lean_ctor_get(v_toParserModuleContext_4748_, 0);
v___x_4755_ = l_Lean_Parser_parserExtension;
v_ext_4756_ = lean_ctor_get(v___x_4755_, 1);
v_toEnvExtension_4757_ = lean_ctor_get(v_ext_4756_, 0);
v_asyncMode_4758_ = lean_ctor_get(v_toEnvExtension_4757_, 2);
lean_inc_ref(v_env_4754_);
v___x_4759_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4742_, v___x_4755_, v_env_4754_, v_asyncMode_4758_);
v_tokens_4760_ = lean_ctor_get(v___x_4759_, 0);
lean_inc_ref(v_tokens_4760_);
lean_dec(v___x_4759_);
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 3, v_tokens_4760_);
v___x_4762_ = v___x_4752_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_toInputContext_4749_);
lean_ctor_set(v_reuseFailAlloc_4763_, 1, v_toParserModuleContext_4748_);
lean_ctor_set(v_reuseFailAlloc_4763_, 2, v_toCacheableParserContext_4750_);
lean_ctor_set(v_reuseFailAlloc_4763_, 3, v_tokens_4760_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object* v___x_4776_, lean_object* v_ids_4777_, lean_object* v_addOpenSimple_4778_, lean_object* v_c_4779_){
_start:
{
uint8_t v_addOpenSimple_boxed_4780_; lean_object* v_res_4781_; 
v_addOpenSimple_boxed_4780_ = lean_unbox(v_addOpenSimple_4778_);
v_res_4781_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_4776_, v_ids_4777_, v_addOpenSimple_boxed_4780_, v_c_4779_);
lean_dec_ref(v_ids_4777_);
lean_dec_ref(v___x_4776_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* v_ids_4782_, uint8_t v_addOpenSimple_4783_, lean_object* v_p_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___f_4789_; lean_object* v___x_4790_; 
v___x_4787_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4788_ = lean_box(v_addOpenSimple_4783_);
v___f_4789_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4789_, 0, v___x_4787_);
lean_closure_set(v___f_4789_, 1, v_ids_4782_);
lean_closure_set(v___f_4789_, 2, v___x_4788_);
v___x_4790_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_4789_, v_p_4784_, v_a_4785_, v_a_4786_);
return v___x_4790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* v_ids_4791_, lean_object* v_addOpenSimple_4792_, lean_object* v_p_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_){
_start:
{
uint8_t v_addOpenSimple_boxed_4796_; lean_object* v_res_4797_; 
v_addOpenSimple_boxed_4796_ = lean_unbox(v_addOpenSimple_4792_);
v_res_4797_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_4791_, v_addOpenSimple_boxed_4796_, v_p_4793_, v_a_4794_, v_a_4795_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t v_sz_4798_, size_t v_i_4799_, lean_object* v_bs_4800_){
_start:
{
uint8_t v___x_4801_; 
v___x_4801_ = lean_usize_dec_lt(v_i_4799_, v_sz_4798_);
if (v___x_4801_ == 0)
{
return v_bs_4800_;
}
else
{
lean_object* v_v_4802_; lean_object* v___x_4803_; lean_object* v_bs_x27_4804_; lean_object* v___x_4805_; size_t v___x_4806_; size_t v___x_4807_; lean_object* v___x_4808_; 
v_v_4802_ = lean_array_uget(v_bs_4800_, v_i_4799_);
v___x_4803_ = lean_unsigned_to_nat(0u);
v_bs_x27_4804_ = lean_array_uset(v_bs_4800_, v_i_4799_, v___x_4803_);
v___x_4805_ = l_Lean_Syntax_getId(v_v_4802_);
lean_dec(v_v_4802_);
v___x_4806_ = ((size_t)1ULL);
v___x_4807_ = lean_usize_add(v_i_4799_, v___x_4806_);
v___x_4808_ = lean_array_uset(v_bs_x27_4804_, v_i_4799_, v___x_4805_);
v_i_4799_ = v___x_4807_;
v_bs_4800_ = v___x_4808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object* v_sz_4810_, lean_object* v_i_4811_, lean_object* v_bs_4812_){
_start:
{
size_t v_sz_boxed_4813_; size_t v_i_boxed_4814_; lean_object* v_res_4815_; 
v_sz_boxed_4813_ = lean_unbox_usize(v_sz_4810_);
lean_dec(v_sz_4810_);
v_i_boxed_4814_ = lean_unbox_usize(v_i_4811_);
lean_dec(v_i_4811_);
v_res_4815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_boxed_4813_, v_i_boxed_4814_, v_bs_4812_);
return v_res_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* v_openDeclStx_4829_, lean_object* v_p_4830_, lean_object* v_c_4831_, lean_object* v_s_4832_){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; uint8_t v___x_4835_; 
lean_inc(v_openDeclStx_4829_);
v___x_4833_ = l_Lean_Syntax_getKind(v_openDeclStx_4829_);
v___x_4834_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__2));
v___x_4835_ = lean_name_eq(v___x_4833_, v___x_4834_);
if (v___x_4835_ == 0)
{
lean_object* v___x_4836_; uint8_t v___x_4837_; 
v___x_4836_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__4));
v___x_4837_ = lean_name_eq(v___x_4833_, v___x_4836_);
lean_dec(v___x_4833_);
if (v___x_4837_ == 0)
{
lean_object* v___x_4838_; 
lean_dec(v_openDeclStx_4829_);
v___x_4838_ = lean_apply_2(v_p_4830_, v_c_4831_, v_s_4832_);
return v___x_4838_;
}
else
{
lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; size_t v_sz_4842_; size_t v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4839_ = lean_unsigned_to_nat(1u);
v___x_4840_ = l_Lean_Syntax_getArg(v_openDeclStx_4829_, v___x_4839_);
lean_dec(v_openDeclStx_4829_);
v___x_4841_ = l_Lean_Syntax_getArgs(v___x_4840_);
lean_dec(v___x_4840_);
v_sz_4842_ = lean_array_size(v___x_4841_);
v___x_4843_ = ((size_t)0ULL);
v___x_4844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4842_, v___x_4843_, v___x_4841_);
v___x_4845_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4844_, v___x_4835_, v_p_4830_, v_c_4831_, v_s_4832_);
return v___x_4845_;
}
}
else
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; size_t v_sz_4849_; size_t v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; 
lean_dec(v___x_4833_);
v___x_4846_ = lean_unsigned_to_nat(0u);
v___x_4847_ = l_Lean_Syntax_getArg(v_openDeclStx_4829_, v___x_4846_);
lean_dec(v_openDeclStx_4829_);
v___x_4848_ = l_Lean_Syntax_getArgs(v___x_4847_);
lean_dec(v___x_4847_);
v_sz_4849_ = lean_array_size(v___x_4848_);
v___x_4850_ = ((size_t)0ULL);
v___x_4851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4849_, v___x_4850_, v___x_4848_);
v___x_4852_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4851_, v___x_4835_, v_p_4830_, v_c_4831_, v_s_4832_);
return v___x_4852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* v_p_4859_, lean_object* v_c_4860_, lean_object* v_s_4861_){
_start:
{
lean_object* v_stxStack_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; uint8_t v___x_4865_; 
v_stxStack_4862_ = lean_ctor_get(v_s_4861_, 0);
v___x_4863_ = lean_unsigned_to_nat(0u);
v___x_4864_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4862_);
v___x_4865_ = lean_nat_dec_lt(v___x_4863_, v___x_4864_);
lean_dec(v___x_4864_);
if (v___x_4865_ == 0)
{
lean_object* v___x_4866_; 
v___x_4866_ = lean_apply_2(v_p_4859_, v_c_4860_, v_s_4861_);
return v___x_4866_;
}
else
{
lean_object* v_stx_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; uint8_t v___x_4870_; 
v_stx_4867_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4862_);
lean_inc(v_stx_4867_);
v___x_4868_ = l_Lean_Syntax_getKind(v_stx_4867_);
v___x_4869_ = ((lean_object*)(l_Lean_Parser_withOpenFn___closed__1));
v___x_4870_ = lean_name_eq(v___x_4868_, v___x_4869_);
lean_dec(v___x_4868_);
if (v___x_4870_ == 0)
{
lean_object* v___x_4871_; 
lean_dec(v_stx_4867_);
v___x_4871_ = lean_apply_2(v_p_4859_, v_c_4860_, v_s_4861_);
return v___x_4871_;
}
else
{
lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4872_ = lean_unsigned_to_nat(1u);
v___x_4873_ = l_Lean_Syntax_getArg(v_stx_4867_, v___x_4872_);
lean_dec(v_stx_4867_);
v___x_4874_ = l_Lean_Parser_withOpenDeclFnCore(v___x_4873_, v_p_4859_, v_c_4860_, v_s_4861_);
return v___x_4874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* v_p_4875_){
_start:
{
lean_object* v_info_4876_; lean_object* v_fn_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4885_; 
v_info_4876_ = lean_ctor_get(v_p_4875_, 0);
v_fn_4877_ = lean_ctor_get(v_p_4875_, 1);
v_isSharedCheck_4885_ = !lean_is_exclusive(v_p_4875_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4879_ = v_p_4875_;
v_isShared_4880_ = v_isSharedCheck_4885_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_fn_4877_);
lean_inc(v_info_4876_);
lean_dec(v_p_4875_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4885_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4881_; lean_object* v___x_4883_; 
v___x_4881_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(v___x_4881_, 0, v_fn_4877_);
if (v_isShared_4880_ == 0)
{
lean_ctor_set(v___x_4879_, 1, v___x_4881_);
v___x_4883_ = v___x_4879_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_info_4876_);
lean_ctor_set(v_reuseFailAlloc_4884_, 1, v___x_4881_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* v_p_4886_, lean_object* v_c_4887_, lean_object* v_s_4888_){
_start:
{
lean_object* v_stxStack_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; uint8_t v___x_4892_; 
v_stxStack_4889_ = lean_ctor_get(v_s_4888_, 0);
v___x_4890_ = lean_unsigned_to_nat(0u);
v___x_4891_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4889_);
v___x_4892_ = lean_nat_dec_lt(v___x_4890_, v___x_4891_);
lean_dec(v___x_4891_);
if (v___x_4892_ == 0)
{
lean_object* v___x_4893_; 
v___x_4893_ = lean_apply_2(v_p_4886_, v_c_4887_, v_s_4888_);
return v___x_4893_;
}
else
{
lean_object* v_stx_4894_; lean_object* v___x_4895_; 
v_stx_4894_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4889_);
v___x_4895_ = l_Lean_Parser_withOpenDeclFnCore(v_stx_4894_, v_p_4886_, v_c_4887_, v_s_4888_);
return v___x_4895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* v_p_4896_){
_start:
{
lean_object* v_info_4897_; lean_object* v_fn_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4906_; 
v_info_4897_ = lean_ctor_get(v_p_4896_, 0);
v_fn_4898_ = lean_ctor_get(v_p_4896_, 1);
v_isSharedCheck_4906_ = !lean_is_exclusive(v_p_4896_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4900_ = v_p_4896_;
v_isShared_4901_ = v_isSharedCheck_4906_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_fn_4898_);
lean_inc(v_info_4897_);
lean_dec(v_p_4896_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4906_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4902_; lean_object* v___x_4904_; 
v___x_4902_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(v___x_4902_, 0, v_fn_4898_);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 1, v___x_4902_);
v___x_4904_ = v___x_4900_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_info_4897_);
lean_ctor_set(v_reuseFailAlloc_4905_, 1, v___x_4902_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object* v___x_4907_){
_start:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4909_ = lean_st_ref_get(v___x_4907_);
v___x_4910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4909_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v___x_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v_res_4913_; 
v_res_4913_ = l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_4911_);
lean_dec(v___x_4911_);
return v_res_4913_;
}
}
static lean_object* _init_l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4914_; lean_object* v___f_4915_; 
v___x_4914_ = l_Lean_Parser_parserAliasesRef;
v___f_4915_ = lean_alloc_closure((void*)(l_Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4915_, 0, v___x_4914_);
return v___f_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___f_4917_ = lean_obj_once(&l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_, &l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once, _init_l_Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_);
v___x_4918_ = lean_box(0);
v___x_4919_ = lean_box(2);
v___x_4920_ = l_Lean_registerEnvExtension___redArg(v___f_4917_, v___x_4918_, v___x_4919_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v_a_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx(lean_object* v_x_4923_){
_start:
{
switch(lean_obj_tag(v_x_4923_))
{
case 0:
{
lean_object* v___x_4924_; 
v___x_4924_ = lean_unsigned_to_nat(0u);
return v___x_4924_;
}
case 1:
{
lean_object* v___x_4925_; 
v___x_4925_ = lean_unsigned_to_nat(1u);
return v___x_4925_;
}
default: 
{
lean_object* v___x_4926_; 
v___x_4926_ = lean_unsigned_to_nat(2u);
return v___x_4926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___boxed(lean_object* v_x_4927_){
_start:
{
lean_object* v_res_4928_; 
v_res_4928_ = l_Lean_Parser_ParserResolution_ctorIdx(v_x_4927_);
lean_dec_ref(v_x_4927_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object* v_t_4929_, lean_object* v_k_4930_){
_start:
{
switch(lean_obj_tag(v_t_4929_))
{
case 0:
{
lean_object* v_cat_4931_; lean_object* v___x_4932_; 
v_cat_4931_ = lean_ctor_get(v_t_4929_, 0);
lean_inc(v_cat_4931_);
lean_dec_ref(v_t_4929_);
v___x_4932_ = lean_apply_1(v_k_4930_, v_cat_4931_);
return v___x_4932_;
}
case 1:
{
lean_object* v_decl_4933_; uint8_t v_isDescr_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v_decl_4933_ = lean_ctor_get(v_t_4929_, 0);
lean_inc(v_decl_4933_);
v_isDescr_4934_ = lean_ctor_get_uint8(v_t_4929_, sizeof(void*)*1);
lean_dec_ref(v_t_4929_);
v___x_4935_ = lean_box(v_isDescr_4934_);
v___x_4936_ = lean_apply_2(v_k_4930_, v_decl_4933_, v___x_4935_);
return v___x_4936_;
}
default: 
{
lean_object* v_p_4937_; lean_object* v___x_4938_; 
v_p_4937_ = lean_ctor_get(v_t_4929_, 0);
lean_inc_ref(v_p_4937_);
lean_dec_ref(v_t_4929_);
v___x_4938_ = lean_apply_1(v_k_4930_, v_p_4937_);
return v___x_4938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object* v_motive_4939_, lean_object* v_ctorIdx_4940_, lean_object* v_t_4941_, lean_object* v_h_4942_, lean_object* v_k_4943_){
_start:
{
lean_object* v___x_4944_; 
v___x_4944_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_4941_, v_k_4943_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object* v_motive_4945_, lean_object* v_ctorIdx_4946_, lean_object* v_t_4947_, lean_object* v_h_4948_, lean_object* v_k_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l_Lean_Parser_ParserResolution_ctorElim(v_motive_4945_, v_ctorIdx_4946_, v_t_4947_, v_h_4948_, v_k_4949_);
lean_dec(v_ctorIdx_4946_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object* v_t_4951_, lean_object* v_category_4952_){
_start:
{
lean_object* v___x_4953_; 
v___x_4953_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_4951_, v_category_4952_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object* v_motive_4954_, lean_object* v_t_4955_, lean_object* v_h_4956_, lean_object* v_category_4957_){
_start:
{
lean_object* v___x_4958_; 
v___x_4958_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_4955_, v_category_4957_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object* v_t_4959_, lean_object* v_parser_4960_){
_start:
{
lean_object* v___x_4961_; 
v___x_4961_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_4959_, v_parser_4960_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object* v_motive_4962_, lean_object* v_t_4963_, lean_object* v_h_4964_, lean_object* v_parser_4965_){
_start:
{
lean_object* v___x_4966_; 
v___x_4966_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_4963_, v_parser_4965_);
return v___x_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object* v_t_4967_, lean_object* v_alias_4968_){
_start:
{
lean_object* v___x_4969_; 
v___x_4969_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_4967_, v_alias_4968_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object* v_motive_4970_, lean_object* v_t_4971_, lean_object* v_h_4972_, lean_object* v_alias_4973_){
_start:
{
lean_object* v___x_4974_; 
v___x_4974_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_4971_, v_alias_4973_);
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object* v_env_4978_, lean_object* v_name_4979_){
_start:
{
uint8_t v___x_4980_; lean_object* v___x_4981_; 
v___x_4980_ = 0;
v___x_4981_ = l_Lean_Environment_find_x3f(v_env_4978_, v_name_4979_, v___x_4980_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v___x_4982_; 
v___x_4982_ = lean_box(0);
return v___x_4982_;
}
else
{
lean_object* v_val_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_5030_; 
v_val_4983_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_4985_ = v___x_4981_;
v_isShared_4986_ = v_isSharedCheck_5030_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_val_4983_);
lean_dec(v___x_4981_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_5030_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4987_; 
v___x_4987_ = l_Lean_ConstantInfo_type(v_val_4983_);
lean_dec(v_val_4983_);
if (lean_obj_tag(v___x_4987_) == 4)
{
lean_object* v_declName_4988_; 
v_declName_4988_ = lean_ctor_get(v___x_4987_, 0);
lean_inc(v_declName_4988_);
lean_dec_ref(v___x_4987_);
if (lean_obj_tag(v_declName_4988_) == 1)
{
lean_object* v_pre_4989_; 
v_pre_4989_ = lean_ctor_get(v_declName_4988_, 0);
lean_inc(v_pre_4989_);
if (lean_obj_tag(v_pre_4989_) == 1)
{
lean_object* v_pre_4990_; 
v_pre_4990_ = lean_ctor_get(v_pre_4989_, 0);
switch(lean_obj_tag(v_pre_4990_))
{
case 1:
{
lean_object* v_pre_4991_; 
lean_inc_ref(v_pre_4990_);
lean_del_object(v___x_4985_);
v_pre_4991_ = lean_ctor_get(v_pre_4990_, 0);
if (lean_obj_tag(v_pre_4991_) == 0)
{
lean_object* v_str_4992_; lean_object* v_str_4993_; lean_object* v_str_4994_; lean_object* v___x_4995_; uint8_t v___x_4996_; 
v_str_4992_ = lean_ctor_get(v_declName_4988_, 1);
lean_inc_ref(v_str_4992_);
lean_dec_ref(v_declName_4988_);
v_str_4993_ = lean_ctor_get(v_pre_4989_, 1);
lean_inc_ref(v_str_4993_);
lean_dec_ref(v_pre_4989_);
v_str_4994_ = lean_ctor_get(v_pre_4990_, 1);
lean_inc_ref(v_str_4994_);
lean_dec_ref(v_pre_4990_);
v___x_4995_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_4996_ = lean_string_dec_eq(v_str_4994_, v___x_4995_);
lean_dec_ref(v_str_4994_);
if (v___x_4996_ == 0)
{
lean_object* v___x_4997_; 
lean_dec_ref(v_str_4993_);
lean_dec_ref(v_str_4992_);
v___x_4997_ = lean_box(0);
return v___x_4997_;
}
else
{
lean_object* v___x_4998_; uint8_t v___x_4999_; 
v___x_4998_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_4999_ = lean_string_dec_eq(v_str_4993_, v___x_4998_);
lean_dec_ref(v_str_4993_);
if (v___x_4999_ == 0)
{
lean_object* v___x_5000_; 
lean_dec_ref(v_str_4992_);
v___x_5000_ = lean_box(0);
return v___x_5000_;
}
else
{
uint8_t v___x_5001_; 
v___x_5001_ = lean_string_dec_eq(v_str_4992_, v___x_4998_);
if (v___x_5001_ == 0)
{
lean_object* v___x_5002_; uint8_t v___x_5003_; 
v___x_5002_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_5003_ = lean_string_dec_eq(v_str_4992_, v___x_5002_);
lean_dec_ref(v_str_4992_);
if (v___x_5003_ == 0)
{
lean_object* v___x_5004_; 
v___x_5004_ = lean_box(0);
return v___x_5004_;
}
else
{
lean_object* v___x_5005_; 
v___x_5005_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5005_;
}
}
else
{
lean_object* v___x_5006_; 
lean_dec_ref(v_str_4992_);
v___x_5006_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5006_;
}
}
}
}
else
{
lean_object* v___x_5007_; 
lean_dec_ref(v_pre_4990_);
lean_dec_ref(v_pre_4989_);
lean_dec_ref(v_declName_4988_);
v___x_5007_ = lean_box(0);
return v___x_5007_;
}
}
case 0:
{
lean_object* v_str_5008_; lean_object* v_str_5009_; lean_object* v___x_5010_; uint8_t v___x_5011_; 
v_str_5008_ = lean_ctor_get(v_declName_4988_, 1);
lean_inc_ref(v_str_5008_);
lean_dec_ref(v_declName_4988_);
v_str_5009_ = lean_ctor_get(v_pre_4989_, 1);
lean_inc_ref(v_str_5009_);
lean_dec_ref(v_pre_4989_);
v___x_5010_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5011_ = lean_string_dec_eq(v_str_5009_, v___x_5010_);
lean_dec_ref(v_str_5009_);
if (v___x_5011_ == 0)
{
lean_object* v___x_5012_; 
lean_dec_ref(v_str_5008_);
lean_del_object(v___x_4985_);
v___x_5012_ = lean_box(0);
return v___x_5012_;
}
else
{
lean_object* v___x_5013_; uint8_t v___x_5014_; 
v___x_5013_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_5014_ = lean_string_dec_eq(v_str_5008_, v___x_5013_);
if (v___x_5014_ == 0)
{
lean_object* v___x_5015_; uint8_t v___x_5016_; 
v___x_5015_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_5016_ = lean_string_dec_eq(v_str_5008_, v___x_5015_);
lean_dec_ref(v_str_5008_);
if (v___x_5016_ == 0)
{
lean_object* v___x_5017_; 
lean_del_object(v___x_4985_);
v___x_5017_ = lean_box(0);
return v___x_5017_;
}
else
{
lean_object* v___x_5018_; lean_object* v___x_5020_; 
v___x_5018_ = lean_box(v___x_5011_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v___x_5018_);
v___x_5020_ = v___x_4985_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v___x_5018_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
}
else
{
lean_object* v___x_5022_; lean_object* v___x_5024_; 
lean_dec_ref(v_str_5008_);
v___x_5022_ = lean_box(v___x_5011_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v___x_5022_);
v___x_5024_ = v___x_4985_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5022_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
default: 
{
lean_object* v___x_5026_; 
lean_dec_ref(v_pre_4989_);
lean_dec_ref(v_declName_4988_);
lean_del_object(v___x_4985_);
v___x_5026_ = lean_box(0);
return v___x_5026_;
}
}
}
else
{
lean_object* v___x_5027_; 
lean_dec_ref(v_declName_4988_);
lean_dec(v_pre_4989_);
lean_del_object(v___x_4985_);
v___x_5027_ = lean_box(0);
return v___x_5027_;
}
}
else
{
lean_object* v___x_5028_; 
lean_dec(v_declName_4988_);
lean_del_object(v___x_4985_);
v___x_5028_ = lean_box(0);
return v___x_5028_;
}
}
else
{
lean_object* v___x_5029_; 
lean_dec_ref(v___x_4987_);
lean_del_object(v___x_4985_);
v___x_5029_ = lean_box(0);
return v___x_5029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object* v_env_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_){
_start:
{
if (lean_obj_tag(v_a_5032_) == 0)
{
lean_object* v___x_5034_; 
lean_dec_ref(v_env_5031_);
v___x_5034_ = lean_array_to_list(v_a_5033_);
return v___x_5034_;
}
else
{
lean_object* v_head_5035_; lean_object* v_snd_5036_; 
v_head_5035_ = lean_ctor_get(v_a_5032_, 0);
v_snd_5036_ = lean_ctor_get(v_head_5035_, 1);
if (lean_obj_tag(v_snd_5036_) == 0)
{
lean_object* v_tail_5037_; lean_object* v_fst_5038_; lean_object* v___x_5039_; 
lean_inc(v_head_5035_);
v_tail_5037_ = lean_ctor_get(v_a_5032_, 1);
lean_inc(v_tail_5037_);
lean_dec_ref(v_a_5032_);
v_fst_5038_ = lean_ctor_get(v_head_5035_, 0);
lean_inc_n(v_fst_5038_, 2);
lean_dec(v_head_5035_);
lean_inc_ref(v_env_5031_);
v___x_5039_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5031_, v_fst_5038_);
if (lean_obj_tag(v___x_5039_) == 0)
{
lean_dec(v_fst_5038_);
v_a_5032_ = v_tail_5037_;
goto _start;
}
else
{
lean_object* v_val_5041_; lean_object* v___x_5042_; uint8_t v___x_5043_; lean_object* v___x_5044_; 
v_val_5041_ = lean_ctor_get(v___x_5039_, 0);
lean_inc(v_val_5041_);
lean_dec_ref(v___x_5039_);
v___x_5042_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5042_, 0, v_fst_5038_);
v___x_5043_ = lean_unbox(v_val_5041_);
lean_dec(v_val_5041_);
lean_ctor_set_uint8(v___x_5042_, sizeof(void*)*1, v___x_5043_);
v___x_5044_ = lean_array_push(v_a_5033_, v___x_5042_);
v_a_5032_ = v_tail_5037_;
v_a_5033_ = v___x_5044_;
goto _start;
}
}
else
{
lean_object* v_tail_5046_; 
v_tail_5046_ = lean_ctor_get(v_a_5032_, 1);
lean_inc(v_tail_5046_);
lean_dec_ref(v_a_5032_);
v_a_5032_ = v_tail_5046_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object* v_env_5051_, lean_object* v_as_x27_5052_, lean_object* v_b_5053_){
_start:
{
if (lean_obj_tag(v_as_x27_5052_) == 0)
{
lean_dec_ref(v_env_5051_);
lean_inc_ref(v_b_5053_);
return v_b_5053_;
}
else
{
lean_object* v_head_5054_; lean_object* v_tail_5055_; lean_object* v___x_5057_; uint8_t v_isShared_5058_; uint8_t v_isSharedCheck_5089_; 
v_head_5054_ = lean_ctor_get(v_as_x27_5052_, 0);
v_tail_5055_ = lean_ctor_get(v_as_x27_5052_, 1);
v_isSharedCheck_5089_ = !lean_is_exclusive(v_as_x27_5052_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5057_ = v_as_x27_5052_;
v_isShared_5058_ = v_isSharedCheck_5089_;
goto v_resetjp_5056_;
}
else
{
lean_inc(v_tail_5055_);
lean_inc(v_head_5054_);
lean_dec(v_as_x27_5052_);
v___x_5057_ = lean_box(0);
v_isShared_5058_ = v_isSharedCheck_5089_;
goto v_resetjp_5056_;
}
v_resetjp_5056_:
{
lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5059_ = lean_box(0);
v___x_5060_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_5054_) == 1)
{
lean_object* v_fields_5061_; 
v_fields_5061_ = lean_ctor_get(v_head_5054_, 1);
if (lean_obj_tag(v_fields_5061_) == 0)
{
lean_object* v_n_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5085_; 
v_n_5062_ = lean_ctor_get(v_head_5054_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v_head_5054_);
if (v_isSharedCheck_5085_ == 0)
{
lean_object* v_unused_5086_; 
v_unused_5086_ = lean_ctor_get(v_head_5054_, 1);
lean_dec(v_unused_5086_);
v___x_5064_ = v_head_5054_;
v_isShared_5065_ = v_isSharedCheck_5085_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_n_5062_);
lean_dec(v_head_5054_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5085_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5066_; 
lean_inc(v_n_5062_);
lean_inc_ref(v_env_5051_);
v___x_5066_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5051_, v_n_5062_);
if (lean_obj_tag(v___x_5066_) == 1)
{
lean_object* v_val_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5083_; 
lean_dec(v_tail_5055_);
lean_dec_ref(v_env_5051_);
v_val_5067_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5069_ = v___x_5066_;
v_isShared_5070_ = v_isSharedCheck_5083_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_val_5067_);
lean_dec(v___x_5066_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5083_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5071_; uint8_t v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5075_; 
v___x_5071_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5071_, 0, v_n_5062_);
v___x_5072_ = lean_unbox(v_val_5067_);
lean_dec(v_val_5067_);
lean_ctor_set_uint8(v___x_5071_, sizeof(void*)*1, v___x_5072_);
v___x_5073_ = lean_box(0);
if (v_isShared_5058_ == 0)
{
lean_ctor_set(v___x_5057_, 1, v___x_5073_);
lean_ctor_set(v___x_5057_, 0, v___x_5071_);
v___x_5075_ = v___x_5057_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v___x_5071_);
lean_ctor_set(v_reuseFailAlloc_5082_, 1, v___x_5073_);
v___x_5075_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
lean_object* v___x_5077_; 
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 0, v___x_5075_);
v___x_5077_ = v___x_5069_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5075_);
v___x_5077_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
lean_object* v___x_5079_; 
if (v_isShared_5065_ == 0)
{
lean_ctor_set_tag(v___x_5064_, 0);
lean_ctor_set(v___x_5064_, 1, v___x_5059_);
lean_ctor_set(v___x_5064_, 0, v___x_5077_);
v___x_5079_ = v___x_5064_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v___x_5077_);
lean_ctor_set(v_reuseFailAlloc_5080_, 1, v___x_5059_);
v___x_5079_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
return v___x_5079_;
}
}
}
}
}
else
{
lean_dec(v___x_5066_);
lean_del_object(v___x_5064_);
lean_dec(v_n_5062_);
lean_del_object(v___x_5057_);
v_as_x27_5052_ = v_tail_5055_;
v_b_5053_ = v___x_5060_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_head_5054_);
lean_del_object(v___x_5057_);
v_as_x27_5052_ = v_tail_5055_;
v_b_5053_ = v___x_5060_;
goto _start;
}
}
else
{
lean_del_object(v___x_5057_);
lean_dec(v_head_5054_);
v_as_x27_5052_ = v_tail_5055_;
v_b_5053_ = v___x_5060_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object* v_env_5090_, lean_object* v_as_x27_5091_, lean_object* v_b_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5090_, v_as_x27_5091_, v_b_5092_);
lean_dec_ref(v_b_5092_);
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object* v_env_5096_, lean_object* v_opts_5097_, lean_object* v_currNamespace_5098_, lean_object* v_openDecls_5099_, lean_object* v_ident_5100_){
_start:
{
if (lean_obj_tag(v_ident_5100_) == 3)
{
lean_object* v_val_5101_; lean_object* v_preresolved_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v_fst_5105_; lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5140_; 
v_val_5101_ = lean_ctor_get(v_ident_5100_, 2);
lean_inc(v_val_5101_);
v_preresolved_5102_ = lean_ctor_get(v_ident_5100_, 3);
lean_inc(v_preresolved_5102_);
lean_dec_ref(v_ident_5100_);
v___x_5103_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
lean_inc_ref(v_env_5096_);
v___x_5104_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5096_, v_preresolved_5102_, v___x_5103_);
v_fst_5105_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5140_ == 0)
{
lean_object* v_unused_5141_; 
v_unused_5141_ = lean_ctor_get(v___x_5104_, 1);
lean_dec(v_unused_5141_);
v___x_5107_ = v___x_5104_;
v_isShared_5108_ = v_isSharedCheck_5140_;
goto v_resetjp_5106_;
}
else
{
lean_inc(v_fst_5105_);
lean_dec(v___x_5104_);
v___x_5107_ = lean_box(0);
v_isShared_5108_ = v_isSharedCheck_5140_;
goto v_resetjp_5106_;
}
v_resetjp_5106_:
{
if (lean_obj_tag(v_fst_5105_) == 0)
{
lean_object* v___x_5109_; uint8_t v___x_5110_; 
lean_inc(v_val_5101_);
v___x_5109_ = lean_erase_macro_scopes(v_val_5101_);
lean_inc_ref(v_env_5096_);
v___x_5110_ = l_Lean_Parser_isParserCategory(v_env_5096_, v___x_5109_);
if (v___x_5110_ == 0)
{
lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; uint8_t v___x_5114_; 
lean_inc_ref_n(v_env_5096_, 2);
v___x_5111_ = l_Lean_ResolveName_resolveGlobalName(v_env_5096_, v_opts_5097_, v_currNamespace_5098_, v_openDecls_5099_, v_val_5101_);
v___x_5112_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0));
v___x_5113_ = l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(v_env_5096_, v___x_5111_, v___x_5112_);
v___x_5114_ = l_List_isEmpty___redArg(v___x_5113_);
if (v___x_5114_ == 0)
{
lean_dec(v___x_5109_);
lean_del_object(v___x_5107_);
lean_dec_ref(v_env_5096_);
return v___x_5113_;
}
else
{
lean_object* v___x_5115_; lean_object* v_asyncMode_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
lean_dec(v___x_5113_);
v___x_5115_ = l_Lean_Parser_aliasExtension;
v_asyncMode_5116_ = lean_ctor_get(v___x_5115_, 2);
v___x_5117_ = lean_box(1);
v___x_5118_ = lean_box(0);
v___x_5119_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5117_, v___x_5115_, v_env_5096_, v_asyncMode_5116_, v___x_5118_);
v___x_5120_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5119_, v___x_5109_);
lean_dec(v___x_5109_);
lean_dec(v___x_5119_);
if (lean_obj_tag(v___x_5120_) == 1)
{
lean_object* v_val_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5132_; 
v_val_5121_ = lean_ctor_get(v___x_5120_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5123_ = v___x_5120_;
v_isShared_5124_ = v_isSharedCheck_5132_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_val_5121_);
lean_dec(v___x_5120_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5132_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
lean_ctor_set_tag(v___x_5123_, 2);
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_val_5121_);
v___x_5126_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
lean_object* v___x_5127_; lean_object* v___x_5129_; 
v___x_5127_ = lean_box(0);
if (v_isShared_5108_ == 0)
{
lean_ctor_set_tag(v___x_5107_, 1);
lean_ctor_set(v___x_5107_, 1, v___x_5127_);
lean_ctor_set(v___x_5107_, 0, v___x_5126_);
v___x_5129_ = v___x_5107_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v___x_5126_);
lean_ctor_set(v_reuseFailAlloc_5130_, 1, v___x_5127_);
v___x_5129_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
return v___x_5129_;
}
}
}
}
else
{
lean_object* v___x_5133_; 
lean_dec(v___x_5120_);
lean_del_object(v___x_5107_);
v___x_5133_ = lean_box(0);
return v___x_5133_;
}
}
}
else
{
lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5137_; 
lean_dec(v_val_5101_);
lean_dec(v_openDecls_5099_);
lean_dec(v_currNamespace_5098_);
lean_dec_ref(v_env_5096_);
v___x_5134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5134_, 0, v___x_5109_);
v___x_5135_ = lean_box(0);
if (v_isShared_5108_ == 0)
{
lean_ctor_set_tag(v___x_5107_, 1);
lean_ctor_set(v___x_5107_, 1, v___x_5135_);
lean_ctor_set(v___x_5107_, 0, v___x_5134_);
v___x_5137_ = v___x_5107_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v___x_5134_);
lean_ctor_set(v_reuseFailAlloc_5138_, 1, v___x_5135_);
v___x_5137_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
return v___x_5137_;
}
}
}
else
{
lean_object* v_val_5139_; 
lean_del_object(v___x_5107_);
lean_dec(v_val_5101_);
lean_dec(v_openDecls_5099_);
lean_dec(v_currNamespace_5098_);
lean_dec_ref(v_env_5096_);
v_val_5139_ = lean_ctor_get(v_fst_5105_, 0);
lean_inc(v_val_5139_);
lean_dec_ref(v_fst_5105_);
return v_val_5139_;
}
}
}
else
{
lean_object* v___x_5142_; 
lean_dec(v_ident_5100_);
lean_dec(v_openDecls_5099_);
lean_dec(v_currNamespace_5098_);
lean_dec_ref(v_env_5096_);
v___x_5142_ = lean_box(0);
return v___x_5142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object* v_env_5143_, lean_object* v_opts_5144_, lean_object* v_currNamespace_5145_, lean_object* v_openDecls_5146_, lean_object* v_ident_5147_){
_start:
{
lean_object* v_res_5148_; 
v_res_5148_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5143_, v_opts_5144_, v_currNamespace_5145_, v_openDecls_5146_, v_ident_5147_);
lean_dec_ref(v_opts_5144_);
return v_res_5148_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object* v_env_5149_, lean_object* v_as_5150_, lean_object* v_as_x27_5151_, lean_object* v_b_5152_, lean_object* v_a_5153_){
_start:
{
lean_object* v___x_5154_; 
v___x_5154_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5149_, v_as_x27_5151_, v_b_5152_);
return v___x_5154_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object* v_env_5155_, lean_object* v_as_5156_, lean_object* v_as_x27_5157_, lean_object* v_b_5158_, lean_object* v_a_5159_){
_start:
{
lean_object* v_res_5160_; 
v_res_5160_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(v_env_5155_, v_as_5156_, v_as_x27_5157_, v_b_5158_, v_a_5159_);
lean_dec_ref(v_b_5158_);
lean_dec(v_as_5156_);
return v_res_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object* v_ctx_5161_, lean_object* v_id_5162_, uint8_t v_unsetExporting_5163_){
_start:
{
lean_object* v___y_5165_; 
if (v_unsetExporting_5163_ == 0)
{
lean_object* v_toParserModuleContext_5171_; lean_object* v_env_5172_; 
v_toParserModuleContext_5171_ = lean_ctor_get(v_ctx_5161_, 1);
v_env_5172_ = lean_ctor_get(v_toParserModuleContext_5171_, 0);
lean_inc_ref(v_env_5172_);
v___y_5165_ = v_env_5172_;
goto v___jp_5164_;
}
else
{
lean_object* v_toParserModuleContext_5173_; lean_object* v_env_5174_; uint8_t v___x_5175_; lean_object* v___x_5176_; 
v_toParserModuleContext_5173_ = lean_ctor_get(v_ctx_5161_, 1);
v_env_5174_ = lean_ctor_get(v_toParserModuleContext_5173_, 0);
v___x_5175_ = 0;
lean_inc_ref(v_env_5174_);
v___x_5176_ = l_Lean_Environment_setExporting(v_env_5174_, v___x_5175_);
v___y_5165_ = v___x_5176_;
goto v___jp_5164_;
}
v___jp_5164_:
{
lean_object* v_toParserModuleContext_5166_; lean_object* v_options_5167_; lean_object* v_currNamespace_5168_; lean_object* v_openDecls_5169_; lean_object* v___x_5170_; 
v_toParserModuleContext_5166_ = lean_ctor_get(v_ctx_5161_, 1);
lean_inc_ref(v_toParserModuleContext_5166_);
lean_dec_ref(v_ctx_5161_);
v_options_5167_ = lean_ctor_get(v_toParserModuleContext_5166_, 1);
lean_inc_ref(v_options_5167_);
v_currNamespace_5168_ = lean_ctor_get(v_toParserModuleContext_5166_, 2);
lean_inc(v_currNamespace_5168_);
v_openDecls_5169_ = lean_ctor_get(v_toParserModuleContext_5166_, 3);
lean_inc(v_openDecls_5169_);
lean_dec_ref(v_toParserModuleContext_5166_);
v___x_5170_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v___y_5165_, v_options_5167_, v_currNamespace_5168_, v_openDecls_5169_, v_id_5162_);
lean_dec_ref(v_options_5167_);
return v___x_5170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object* v_ctx_5177_, lean_object* v_id_5178_, lean_object* v_unsetExporting_5179_){
_start:
{
uint8_t v_unsetExporting_boxed_5180_; lean_object* v_res_5181_; 
v_unsetExporting_boxed_5180_ = lean_unbox(v_unsetExporting_5179_);
v_res_5181_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5177_, v_id_5178_, v_unsetExporting_boxed_5180_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object* v_id_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_){
_start:
{
lean_object* v___x_5186_; lean_object* v_env_5187_; lean_object* v_options_5188_; lean_object* v_currNamespace_5189_; lean_object* v_openDecls_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; 
v___x_5186_ = lean_st_ref_get(v_a_5184_);
v_env_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc_ref(v_env_5187_);
lean_dec(v___x_5186_);
v_options_5188_ = lean_ctor_get(v_a_5183_, 2);
v_currNamespace_5189_ = lean_ctor_get(v_a_5183_, 6);
v_openDecls_5190_ = lean_ctor_get(v_a_5183_, 7);
lean_inc(v_openDecls_5190_);
lean_inc(v_currNamespace_5189_);
v___x_5191_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5187_, v_options_5188_, v_currNamespace_5189_, v_openDecls_5190_, v_id_5182_);
v___x_5192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5191_);
return v___x_5192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object* v_id_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l_Lean_Parser_resolveParserName(v_id_5193_, v_a_5194_, v_a_5195_);
lean_dec(v_a_5195_);
lean_dec_ref(v_a_5194_);
return v_res_5197_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object* v_x_5198_, lean_object* v_x_5199_){
_start:
{
if (lean_obj_tag(v_x_5198_) == 0)
{
if (lean_obj_tag(v_x_5199_) == 0)
{
uint8_t v___x_5200_; 
v___x_5200_ = 1;
return v___x_5200_;
}
else
{
uint8_t v___x_5201_; 
lean_dec_ref(v_x_5199_);
v___x_5201_ = 0;
return v___x_5201_;
}
}
else
{
if (lean_obj_tag(v_x_5199_) == 0)
{
uint8_t v___x_5202_; 
lean_dec_ref(v_x_5198_);
v___x_5202_ = 0;
return v___x_5202_;
}
else
{
lean_object* v_val_5203_; lean_object* v_val_5204_; uint8_t v___x_5205_; 
v_val_5203_ = lean_ctor_get(v_x_5198_, 0);
lean_inc(v_val_5203_);
lean_dec_ref(v_x_5198_);
v_val_5204_ = lean_ctor_get(v_x_5199_, 0);
lean_inc(v_val_5204_);
lean_dec_ref(v_x_5199_);
v___x_5205_ = l_Lean_Parser_instBEqError_beq(v_val_5203_, v_val_5204_);
return v___x_5205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object* v_x_5206_, lean_object* v_x_5207_){
_start:
{
uint8_t v_res_5208_; lean_object* v_r_5209_; 
v_res_5208_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5206_, v_x_5207_);
v_r_5209_ = lean_box(v_res_5208_);
return v_r_5209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t v___x_5210_, lean_object* v_ctx_5211_){
_start:
{
lean_object* v_toParserModuleContext_5212_; lean_object* v_toInputContext_5213_; lean_object* v_toCacheableParserContext_5214_; lean_object* v_tokens_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5240_; 
v_toParserModuleContext_5212_ = lean_ctor_get(v_ctx_5211_, 1);
v_toInputContext_5213_ = lean_ctor_get(v_ctx_5211_, 0);
v_toCacheableParserContext_5214_ = lean_ctor_get(v_ctx_5211_, 2);
v_tokens_5215_ = lean_ctor_get(v_ctx_5211_, 3);
v_isSharedCheck_5240_ = !lean_is_exclusive(v_ctx_5211_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5217_ = v_ctx_5211_;
v_isShared_5218_ = v_isSharedCheck_5240_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_tokens_5215_);
lean_inc(v_toCacheableParserContext_5214_);
lean_inc(v_toParserModuleContext_5212_);
lean_inc(v_toInputContext_5213_);
lean_dec(v_ctx_5211_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5240_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v_env_5219_; lean_object* v_options_5220_; lean_object* v_currNamespace_5221_; lean_object* v_openDecls_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5239_; 
v_env_5219_ = lean_ctor_get(v_toParserModuleContext_5212_, 0);
v_options_5220_ = lean_ctor_get(v_toParserModuleContext_5212_, 1);
v_currNamespace_5221_ = lean_ctor_get(v_toParserModuleContext_5212_, 2);
v_openDecls_5222_ = lean_ctor_get(v_toParserModuleContext_5212_, 3);
v_isSharedCheck_5239_ = !lean_is_exclusive(v_toParserModuleContext_5212_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5224_ = v_toParserModuleContext_5212_;
v_isShared_5225_ = v_isSharedCheck_5239_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_openDecls_5222_);
lean_inc(v_currNamespace_5221_);
lean_inc(v_options_5220_);
lean_inc(v_env_5219_);
lean_dec(v_toParserModuleContext_5212_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5239_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
lean_object* v___x_5226_; uint8_t v___y_5228_; lean_object* v___x_5236_; uint8_t v___x_5237_; 
v___x_5226_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_5236_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_5237_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_5220_, v___x_5236_);
if (v___x_5237_ == 0)
{
uint8_t v___x_5238_; 
v___x_5238_ = 1;
v___y_5228_ = v___x_5238_;
goto v___jp_5227_;
}
else
{
v___y_5228_ = v___x_5210_;
goto v___jp_5227_;
}
v___jp_5227_:
{
lean_object* v___x_5229_; lean_object* v___x_5231_; 
v___x_5229_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_5220_, v___x_5226_, v___y_5228_);
if (v_isShared_5225_ == 0)
{
lean_ctor_set(v___x_5224_, 1, v___x_5229_);
v___x_5231_ = v___x_5224_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v_env_5219_);
lean_ctor_set(v_reuseFailAlloc_5235_, 1, v___x_5229_);
lean_ctor_set(v_reuseFailAlloc_5235_, 2, v_currNamespace_5221_);
lean_ctor_set(v_reuseFailAlloc_5235_, 3, v_openDecls_5222_);
v___x_5231_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
lean_object* v___x_5233_; 
if (v_isShared_5218_ == 0)
{
lean_ctor_set(v___x_5217_, 1, v___x_5231_);
v___x_5233_ = v___x_5217_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_toInputContext_5213_);
lean_ctor_set(v_reuseFailAlloc_5234_, 1, v___x_5231_);
lean_ctor_set(v_reuseFailAlloc_5234_, 2, v_toCacheableParserContext_5214_);
lean_ctor_set(v_reuseFailAlloc_5234_, 3, v_tokens_5215_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object* v___x_5241_, lean_object* v_ctx_5242_){
_start:
{
uint8_t v___x_1088__boxed_5243_; lean_object* v_res_5244_; 
v___x_1088__boxed_5243_ = lean_unbox(v___x_5241_);
v_res_5244_ = l_Lean_Parser_parserOfStackFn___lam__0(v___x_1088__boxed_5243_, v_ctx_5242_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* v_offset_5252_, lean_object* v_ctx_5253_, lean_object* v_s_5254_){
_start:
{
lean_object* v_stxStack_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; uint8_t v___x_5259_; 
v_stxStack_5255_ = lean_ctor_get(v_s_5254_, 0);
v___x_5256_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5255_);
v___x_5257_ = lean_unsigned_to_nat(1u);
v___x_5258_ = lean_nat_add(v_offset_5252_, v___x_5257_);
v___x_5259_ = lean_nat_dec_lt(v___x_5256_, v___x_5258_);
lean_dec(v___x_5258_);
if (v___x_5259_ == 0)
{
lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5260_ = lean_nat_sub(v___x_5256_, v_offset_5252_);
lean_dec(v___x_5256_);
v___x_5261_ = lean_nat_sub(v___x_5260_, v___x_5257_);
lean_dec(v___x_5260_);
v___x_5262_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5255_, v___x_5261_);
lean_dec(v___x_5261_);
if (lean_obj_tag(v___x_5262_) == 3)
{
uint8_t v___x_5274_; lean_object* v___x_5275_; 
v___x_5274_ = 1;
lean_inc_ref(v___x_5262_);
lean_inc_ref(v_ctx_5253_);
v___x_5275_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5253_, v___x_5262_, v___x_5274_);
if (lean_obj_tag(v___x_5275_) == 0)
{
lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
lean_dec_ref(v_ctx_5253_);
v___x_5276_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__1));
v___x_5277_ = lean_box(0);
v___x_5278_ = l_Lean_Syntax_formatStx(v___x_5262_, v___x_5277_, v___x_5259_);
v___x_5279_ = l_Std_Format_defWidth;
v___x_5280_ = lean_unsigned_to_nat(0u);
v___x_5281_ = l_Std_Format_pretty(v___x_5278_, v___x_5279_, v___x_5280_, v___x_5280_);
v___x_5282_ = lean_string_append(v___x_5276_, v___x_5281_);
lean_dec_ref(v___x_5281_);
v___x_5283_ = lean_box(0);
v___x_5284_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5254_, v___x_5282_, v___x_5283_, v___x_5274_);
return v___x_5284_;
}
else
{
lean_object* v_head_5285_; lean_object* v_tail_5286_; lean_object* v_iniSz_5287_; lean_object* v_s_5289_; 
v_head_5285_ = lean_ctor_get(v___x_5275_, 0);
lean_inc(v_head_5285_);
v_tail_5286_ = lean_ctor_get(v___x_5275_, 1);
lean_inc(v_tail_5286_);
lean_dec_ref(v___x_5275_);
v_iniSz_5287_ = l_Lean_Parser_ParserState_stackSize(v_s_5254_);
switch(lean_obj_tag(v_head_5285_))
{
case 0:
{
if (lean_obj_tag(v_tail_5286_) == 0)
{
lean_object* v_cat_5299_; lean_object* v___x_5300_; 
lean_dec_ref(v___x_5262_);
v_cat_5299_ = lean_ctor_get(v_head_5285_, 0);
lean_inc(v_cat_5299_);
lean_dec_ref(v_head_5285_);
v___x_5300_ = l_Lean_Parser_categoryParserFn(v_cat_5299_, v_ctx_5253_, v_s_5254_);
v_s_5289_ = v___x_5300_;
goto v___jp_5288_;
}
else
{
lean_dec_ref(v_tail_5286_);
lean_dec_ref(v_head_5285_);
lean_dec(v_iniSz_5287_);
lean_dec_ref(v_ctx_5253_);
goto v___jp_5263_;
}
}
case 1:
{
if (lean_obj_tag(v_tail_5286_) == 0)
{
lean_object* v_decl_5301_; lean_object* v___x_5302_; lean_object* v___f_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; 
lean_dec_ref(v___x_5262_);
v_decl_5301_ = lean_ctor_get(v_head_5285_, 0);
lean_inc(v_decl_5301_);
lean_dec_ref(v_head_5285_);
v___x_5302_ = lean_box(v___x_5259_);
v___f_5303_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5303_, 0, v___x_5302_);
v___x_5304_ = lean_box(0);
v___x_5305_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_5305_, 0, v_decl_5301_);
lean_closure_set(v___x_5305_, 1, v___x_5304_);
v___x_5306_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5303_, v___x_5305_, v_ctx_5253_, v_s_5254_);
v_s_5289_ = v___x_5306_;
goto v___jp_5288_;
}
else
{
lean_dec_ref(v_tail_5286_);
lean_dec_ref(v_head_5285_);
lean_dec(v_iniSz_5287_);
lean_dec_ref(v_ctx_5253_);
goto v___jp_5263_;
}
}
default: 
{
if (lean_obj_tag(v_tail_5286_) == 0)
{
lean_object* v_p_5307_; 
v_p_5307_ = lean_ctor_get(v_head_5285_, 0);
lean_inc_ref(v_p_5307_);
lean_dec_ref(v_head_5285_);
if (lean_obj_tag(v_p_5307_) == 0)
{
lean_object* v_p_5308_; lean_object* v_fn_5309_; lean_object* v___x_5310_; 
lean_dec_ref(v___x_5262_);
v_p_5308_ = lean_ctor_get(v_p_5307_, 0);
lean_inc(v_p_5308_);
lean_dec_ref(v_p_5307_);
v_fn_5309_ = lean_ctor_get(v_p_5308_, 1);
lean_inc_ref(v_fn_5309_);
lean_dec(v_p_5308_);
v___x_5310_ = lean_apply_2(v_fn_5309_, v_ctx_5253_, v_s_5254_);
v_s_5289_ = v___x_5310_;
goto v___jp_5288_;
}
else
{
lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; 
lean_dec_ref(v_p_5307_);
lean_dec(v_iniSz_5287_);
lean_dec_ref(v_ctx_5253_);
v___x_5311_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__3));
v___x_5312_ = lean_box(0);
v___x_5313_ = l_Lean_Syntax_formatStx(v___x_5262_, v___x_5312_, v___x_5259_);
v___x_5314_ = l_Std_Format_defWidth;
v___x_5315_ = lean_unsigned_to_nat(0u);
v___x_5316_ = l_Std_Format_pretty(v___x_5313_, v___x_5314_, v___x_5315_, v___x_5315_);
v___x_5317_ = lean_string_append(v___x_5311_, v___x_5316_);
lean_dec_ref(v___x_5316_);
v___x_5318_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__4));
v___x_5319_ = lean_string_append(v___x_5317_, v___x_5318_);
v___x_5320_ = lean_box(0);
v___x_5321_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5254_, v___x_5319_, v___x_5320_, v___x_5274_);
return v___x_5321_;
}
}
else
{
lean_dec_ref(v_tail_5286_);
lean_dec_ref(v_head_5285_);
lean_dec(v_iniSz_5287_);
lean_dec_ref(v_ctx_5253_);
goto v___jp_5263_;
}
}
}
v___jp_5288_:
{
lean_object* v_errorMsg_5290_; lean_object* v___x_5291_; uint8_t v___x_5292_; 
v_errorMsg_5290_ = lean_ctor_get(v_s_5289_, 4);
v___x_5291_ = lean_box(0);
lean_inc(v_errorMsg_5290_);
v___x_5292_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_errorMsg_5290_, v___x_5291_);
if (v___x_5292_ == 0)
{
lean_dec(v_iniSz_5287_);
return v_s_5289_;
}
else
{
lean_object* v___x_5293_; lean_object* v___x_5294_; uint8_t v___x_5295_; 
v___x_5293_ = l_Lean_Parser_ParserState_stackSize(v_s_5289_);
v___x_5294_ = lean_nat_add(v_iniSz_5287_, v___x_5257_);
lean_dec(v_iniSz_5287_);
v___x_5295_ = lean_nat_dec_eq(v___x_5293_, v___x_5294_);
lean_dec(v___x_5294_);
lean_dec(v___x_5293_);
if (v___x_5295_ == 0)
{
lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5296_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__2));
v___x_5297_ = lean_box(0);
v___x_5298_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5289_, v___x_5296_, v___x_5297_, v___x_5292_);
return v___x_5298_;
}
else
{
return v_s_5289_;
}
}
}
}
}
else
{
lean_object* v___x_5322_; lean_object* v___x_5323_; uint8_t v___x_5324_; lean_object* v___x_5325_; 
lean_dec(v___x_5262_);
lean_dec_ref(v_ctx_5253_);
v___x_5322_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__5));
v___x_5323_ = lean_box(0);
v___x_5324_ = 1;
v___x_5325_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5254_, v___x_5322_, v___x_5323_, v___x_5324_);
return v___x_5325_;
}
v___jp_5263_:
{
lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; uint8_t v___x_5272_; lean_object* v___x_5273_; 
v___x_5264_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__0));
v___x_5265_ = lean_box(0);
v___x_5266_ = l_Lean_Syntax_formatStx(v___x_5262_, v___x_5265_, v___x_5259_);
v___x_5267_ = l_Std_Format_defWidth;
v___x_5268_ = lean_unsigned_to_nat(0u);
v___x_5269_ = l_Std_Format_pretty(v___x_5266_, v___x_5267_, v___x_5268_, v___x_5268_);
v___x_5270_ = lean_string_append(v___x_5264_, v___x_5269_);
lean_dec_ref(v___x_5269_);
v___x_5271_ = lean_box(0);
v___x_5272_ = 1;
v___x_5273_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5254_, v___x_5270_, v___x_5271_, v___x_5272_);
return v___x_5273_;
}
}
else
{
lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; 
lean_dec(v___x_5256_);
lean_dec_ref(v_ctx_5253_);
v___x_5326_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__6));
v___x_5327_ = lean_box(0);
v___x_5328_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5254_, v___x_5326_, v___x_5327_, v___x_5259_);
return v___x_5328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* v_offset_5329_, lean_object* v_ctx_5330_, lean_object* v_s_5331_){
_start:
{
lean_object* v_res_5332_; 
v_res_5332_ = l_Lean_Parser_parserOfStackFn(v_offset_5329_, v_ctx_5330_, v_s_5331_);
lean_dec(v_offset_5329_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object* v_prec_5333_, lean_object* v_x_5334_){
_start:
{
lean_object* v_quotDepth_5335_; uint8_t v_suppressInsideQuot_5336_; lean_object* v_savedPos_x3f_5337_; lean_object* v_forbiddenTk_x3f_5338_; lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5345_; 
v_quotDepth_5335_ = lean_ctor_get(v_x_5334_, 1);
v_suppressInsideQuot_5336_ = lean_ctor_get_uint8(v_x_5334_, sizeof(void*)*4);
v_savedPos_x3f_5337_ = lean_ctor_get(v_x_5334_, 2);
v_forbiddenTk_x3f_5338_ = lean_ctor_get(v_x_5334_, 3);
v_isSharedCheck_5345_ = !lean_is_exclusive(v_x_5334_);
if (v_isSharedCheck_5345_ == 0)
{
lean_object* v_unused_5346_; 
v_unused_5346_ = lean_ctor_get(v_x_5334_, 0);
lean_dec(v_unused_5346_);
v___x_5340_ = v_x_5334_;
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
else
{
lean_inc(v_forbiddenTk_x3f_5338_);
lean_inc(v_savedPos_x3f_5337_);
lean_inc(v_quotDepth_5335_);
lean_dec(v_x_5334_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
lean_object* v___x_5343_; 
if (v_isShared_5341_ == 0)
{
lean_ctor_set(v___x_5340_, 0, v_prec_5333_);
v___x_5343_ = v___x_5340_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v_prec_5333_);
lean_ctor_set(v_reuseFailAlloc_5344_, 1, v_quotDepth_5335_);
lean_ctor_set(v_reuseFailAlloc_5344_, 2, v_savedPos_x3f_5337_);
lean_ctor_set(v_reuseFailAlloc_5344_, 3, v_forbiddenTk_x3f_5338_);
lean_ctor_set_uint8(v_reuseFailAlloc_5344_, sizeof(void*)*4, v_suppressInsideQuot_5336_);
v___x_5343_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
return v___x_5343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object* v___y_5347_){
_start:
{
lean_inc(v___y_5347_);
return v___y_5347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object* v___y_5348_){
_start:
{
lean_object* v_res_5349_; 
v_res_5349_ = l_Lean_Parser_parserOfStack___lam__1(v___y_5348_);
lean_dec(v___y_5348_);
return v_res_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object* v___y_5350_){
_start:
{
lean_inc_ref(v___y_5350_);
return v___y_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object* v___y_5351_){
_start:
{
lean_object* v_res_5352_; 
v_res_5352_ = l_Lean_Parser_parserOfStack___lam__2(v___y_5351_);
lean_dec_ref(v___y_5351_);
return v_res_5352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* v_offset_5359_, lean_object* v_prec_5360_){
_start:
{
lean_object* v___f_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; 
v___f_5361_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___lam__0), 2, 1);
lean_closure_set(v___f_5361_, 0, v_prec_5360_);
v___x_5362_ = ((lean_object*)(l_Lean_Parser_parserOfStack___closed__2));
v___x_5363_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___boxed), 3, 1);
lean_closure_set(v___x_5363_, 0, v_offset_5359_);
v___x_5364_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5364_, 0, v___f_5361_);
lean_closure_set(v___x_5364_, 1, v___x_5363_);
v___x_5365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5365_, 0, v___x_5362_);
lean_ctor_set(v___x_5365_, 1, v___x_5364_);
return v___x_5365_;
}
}
lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_BuiltinDocAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_BuiltinDocAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinTokenTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinTokenTable);
lean_dec_ref(res);
res = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinSyntaxNodeKindSetRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinSyntaxNodeKindSetRef);
lean_dec_ref(res);
res = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2250767024____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_builtinParserCategoriesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_builtinParserCategoriesRef);
lean_dec_ref(res);
l_Lean_Parser_ParserExtension_instInhabitedState_default = _init_l_Lean_Parser_ParserExtension_instInhabitedState_default();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedState_default);
l_Lean_Parser_ParserExtension_instInhabitedState = _init_l_Lean_Parser_ParserExtension_instInhabitedState();
lean_mark_persistent(l_Lean_Parser_ParserExtension_instInhabitedState);
res = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAliasesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAliasesRef);
lean_dec_ref(res);
res = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAlias2kindRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAlias2kindRef);
lean_dec_ref(res);
res = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserAliases2infoRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserAliases2infoRef);
lean_dec_ref(res);
res = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
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
res = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Parser_parserExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Parser_parserExtension);
lean_dec_ref(res);
res = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
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
res = l_Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
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
