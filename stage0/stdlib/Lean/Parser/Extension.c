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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0;
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
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_122_; uint64_t v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(1723u);
v___x_123_ = lean_uint64_of_nat(v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(lean_object* v_x_125_, size_t v_x_126_, size_t v_x_127_, lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_object* v_es_130_; size_t v___x_131_; size_t v___x_132_; lean_object* v_j_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_es_130_ = lean_ctor_get(v_x_125_, 0);
v___x_131_ = ((size_t)31ULL);
v___x_132_ = lean_usize_land(v_x_126_, v___x_131_);
v_j_133_ = lean_usize_to_nat(v___x_132_);
v___x_134_ = lean_array_get_size(v_es_130_);
v___x_135_ = lean_nat_dec_lt(v_j_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_dec(v_j_133_);
lean_dec(v_x_129_);
lean_dec(v_x_128_);
return v_x_125_;
}
else
{
lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_174_; 
lean_inc_ref(v_es_130_);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v_x_125_, 0);
lean_dec(v_unused_175_);
v___x_137_ = v_x_125_;
v_isShared_138_ = v_isSharedCheck_174_;
goto v_resetjp_136_;
}
else
{
lean_dec(v_x_125_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_174_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v_v_139_; lean_object* v___x_140_; lean_object* v_xs_x27_141_; lean_object* v___y_143_; 
v_v_139_ = lean_array_fget(v_es_130_, v_j_133_);
v___x_140_ = lean_box(0);
v_xs_x27_141_ = lean_array_fset(v_es_130_, v_j_133_, v___x_140_);
switch(lean_obj_tag(v_v_139_))
{
case 0:
{
lean_object* v_key_148_; lean_object* v_val_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_159_; 
v_key_148_ = lean_ctor_get(v_v_139_, 0);
v_val_149_ = lean_ctor_get(v_v_139_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_v_139_);
if (v_isSharedCheck_159_ == 0)
{
v___x_151_ = v_v_139_;
v_isShared_152_ = v_isSharedCheck_159_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_val_149_);
lean_inc(v_key_148_);
lean_dec(v_v_139_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_159_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
uint8_t v___x_153_; 
v___x_153_ = lean_name_eq(v_x_128_, v_key_148_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_del_object(v___x_151_);
v___x_154_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_148_, v_val_149_, v_x_128_, v_x_129_);
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
v___y_143_ = v___x_155_;
goto v___jp_142_;
}
else
{
lean_object* v___x_157_; 
lean_dec(v_val_149_);
lean_dec(v_key_148_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 1, v_x_129_);
lean_ctor_set(v___x_151_, 0, v_x_128_);
v___x_157_ = v___x_151_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_x_128_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_x_129_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
v___y_143_ = v___x_157_;
goto v___jp_142_;
}
}
}
}
case 1:
{
lean_object* v_node_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_172_; 
v_node_160_ = lean_ctor_get(v_v_139_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v_v_139_);
if (v_isSharedCheck_172_ == 0)
{
v___x_162_ = v_v_139_;
v_isShared_163_ = v_isSharedCheck_172_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_node_160_);
lean_dec(v_v_139_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_172_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_164_ = ((size_t)5ULL);
v___x_165_ = lean_usize_shift_right(v_x_126_, v___x_164_);
v___x_166_ = ((size_t)1ULL);
v___x_167_ = lean_usize_add(v_x_127_, v___x_166_);
v___x_168_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_node_160_, v___x_165_, v___x_167_, v_x_128_, v_x_129_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_168_);
v___x_170_ = v___x_162_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
v___y_143_ = v___x_170_;
goto v___jp_142_;
}
}
}
default: 
{
lean_object* v___x_173_; 
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v_x_128_);
lean_ctor_set(v___x_173_, 1, v_x_129_);
v___y_143_ = v___x_173_;
goto v___jp_142_;
}
}
v___jp_142_:
{
lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_144_ = lean_array_fset(v_xs_x27_141_, v_j_133_, v___y_143_);
lean_dec(v_j_133_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_144_);
v___x_146_ = v___x_137_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
else
{
lean_object* v_ks_176_; lean_object* v_vs_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_197_; 
v_ks_176_ = lean_ctor_get(v_x_125_, 0);
v_vs_177_ = lean_ctor_get(v_x_125_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_197_ == 0)
{
v___x_179_ = v_x_125_;
v_isShared_180_ = v_isSharedCheck_197_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_vs_177_);
lean_inc(v_ks_176_);
lean_dec(v_x_125_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_197_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_ks_176_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_vs_177_);
v___x_182_ = v_reuseFailAlloc_196_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v_newNode_183_; uint8_t v___y_185_; size_t v___x_191_; uint8_t v___x_192_; 
v_newNode_183_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v___x_182_, v_x_128_, v_x_129_);
v___x_191_ = ((size_t)7ULL);
v___x_192_ = lean_usize_dec_le(v___x_191_, v_x_127_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_193_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_183_);
v___x_194_ = lean_unsigned_to_nat(4u);
v___x_195_ = lean_nat_dec_lt(v___x_193_, v___x_194_);
lean_dec(v___x_193_);
v___y_185_ = v___x_195_;
goto v___jp_184_;
}
else
{
v___y_185_ = v___x_192_;
goto v___jp_184_;
}
v___jp_184_:
{
if (v___y_185_ == 0)
{
lean_object* v_ks_186_; lean_object* v_vs_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_ks_186_ = lean_ctor_get(v_newNode_183_, 0);
lean_inc_ref(v_ks_186_);
v_vs_187_ = lean_ctor_get(v_newNode_183_, 1);
lean_inc_ref(v_vs_187_);
lean_dec_ref(v_newNode_183_);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0);
v___x_190_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_x_127_, v_ks_186_, v_vs_187_, v___x_188_, v___x_189_);
lean_dec_ref(v_vs_187_);
lean_dec_ref(v_ks_186_);
return v___x_190_;
}
else
{
return v_newNode_183_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(size_t v_depth_198_, lean_object* v_keys_199_, lean_object* v_vals_200_, lean_object* v_i_201_, lean_object* v_entries_202_){
_start:
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = lean_array_get_size(v_keys_199_);
v___x_204_ = lean_nat_dec_lt(v_i_201_, v___x_203_);
if (v___x_204_ == 0)
{
lean_dec(v_i_201_);
return v_entries_202_;
}
else
{
lean_object* v_k_205_; lean_object* v_v_206_; uint64_t v___y_208_; 
v_k_205_ = lean_array_fget_borrowed(v_keys_199_, v_i_201_);
v_v_206_ = lean_array_fget_borrowed(v_vals_200_, v_i_201_);
if (lean_obj_tag(v_k_205_) == 0)
{
uint64_t v___x_219_; 
v___x_219_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_208_ = v___x_219_;
goto v___jp_207_;
}
else
{
uint64_t v_hash_220_; 
v_hash_220_ = lean_ctor_get_uint64(v_k_205_, sizeof(void*)*2);
v___y_208_ = v_hash_220_;
goto v___jp_207_;
}
v___jp_207_:
{
size_t v_h_209_; size_t v___x_210_; lean_object* v___x_211_; size_t v___x_212_; size_t v___x_213_; size_t v___x_214_; size_t v_h_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_h_209_ = lean_uint64_to_usize(v___y_208_);
v___x_210_ = ((size_t)5ULL);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_sub(v_depth_198_, v___x_212_);
v___x_214_ = lean_usize_mul(v___x_210_, v___x_213_);
v_h_215_ = lean_usize_shift_right(v_h_209_, v___x_214_);
v___x_216_ = lean_nat_add(v_i_201_, v___x_211_);
lean_dec(v_i_201_);
lean_inc(v_v_206_);
lean_inc(v_k_205_);
v___x_217_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_entries_202_, v_h_215_, v_depth_198_, v_k_205_, v_v_206_);
v_i_201_ = v___x_216_;
v_entries_202_ = v___x_217_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_221_, lean_object* v_keys_222_, lean_object* v_vals_223_, lean_object* v_i_224_, lean_object* v_entries_225_){
_start:
{
size_t v_depth_boxed_226_; lean_object* v_res_227_; 
v_depth_boxed_226_ = lean_unbox_usize(v_depth_221_);
lean_dec(v_depth_221_);
v_res_227_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_boxed_226_, v_keys_222_, v_vals_223_, v_i_224_, v_entries_225_);
lean_dec_ref(v_vals_223_);
lean_dec_ref(v_keys_222_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
size_t v_x_540__boxed_233_; size_t v_x_541__boxed_234_; lean_object* v_res_235_; 
v_x_540__boxed_233_ = lean_unbox_usize(v_x_229_);
lean_dec(v_x_229_);
v_x_541__boxed_234_ = lean_unbox_usize(v_x_230_);
lean_dec(v_x_230_);
v_res_235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_228_, v_x_540__boxed_233_, v_x_541__boxed_234_, v_x_231_, v_x_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
uint64_t v___y_240_; 
if (lean_obj_tag(v_x_237_) == 0)
{
uint64_t v___x_244_; 
v___x_244_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_240_ = v___x_244_;
goto v___jp_239_;
}
else
{
uint64_t v_hash_245_; 
v_hash_245_ = lean_ctor_get_uint64(v_x_237_, sizeof(void*)*2);
v___y_240_ = v_hash_245_;
goto v___jp_239_;
}
v___jp_239_:
{
size_t v___x_241_; size_t v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_uint64_to_usize(v___y_240_);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_236_, v___x_241_, v___x_242_, v_x_237_, v_x_238_);
return v___x_243_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_246_, lean_object* v_i_247_, lean_object* v_k_248_){
_start:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_array_get_size(v_keys_246_);
v___x_250_ = lean_nat_dec_lt(v_i_247_, v___x_249_);
if (v___x_250_ == 0)
{
lean_dec(v_i_247_);
return v___x_250_;
}
else
{
lean_object* v_k_x27_251_; uint8_t v___x_252_; 
v_k_x27_251_ = lean_array_fget_borrowed(v_keys_246_, v_i_247_);
v___x_252_ = lean_name_eq(v_k_248_, v_k_x27_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_add(v_i_247_, v___x_253_);
lean_dec(v_i_247_);
v_i_247_ = v___x_254_;
goto _start;
}
else
{
lean_dec(v_i_247_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_256_, lean_object* v_i_257_, lean_object* v_k_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_256_, v_i_257_, v_k_258_);
lean_dec(v_k_258_);
lean_dec_ref(v_keys_256_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(lean_object* v_x_261_, size_t v_x_262_, lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
lean_object* v_es_264_; lean_object* v___x_265_; size_t v___x_266_; size_t v___x_267_; lean_object* v_j_268_; lean_object* v___x_269_; 
v_es_264_ = lean_ctor_get(v_x_261_, 0);
v___x_265_ = lean_box(2);
v___x_266_ = ((size_t)31ULL);
v___x_267_ = lean_usize_land(v_x_262_, v___x_266_);
v_j_268_ = lean_usize_to_nat(v___x_267_);
v___x_269_ = lean_array_get_borrowed(v___x_265_, v_es_264_, v_j_268_);
lean_dec(v_j_268_);
switch(lean_obj_tag(v___x_269_))
{
case 0:
{
lean_object* v_key_270_; uint8_t v___x_271_; 
v_key_270_ = lean_ctor_get(v___x_269_, 0);
v___x_271_ = lean_name_eq(v_x_263_, v_key_270_);
return v___x_271_;
}
case 1:
{
lean_object* v_node_272_; size_t v___x_273_; size_t v___x_274_; 
v_node_272_ = lean_ctor_get(v___x_269_, 0);
v___x_273_ = ((size_t)5ULL);
v___x_274_ = lean_usize_shift_right(v_x_262_, v___x_273_);
v_x_261_ = v_node_272_;
v_x_262_ = v___x_274_;
goto _start;
}
default: 
{
uint8_t v___x_276_; 
v___x_276_ = 0;
return v___x_276_;
}
}
}
else
{
lean_object* v_ks_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_ks_277_ = lean_ctor_get(v_x_261_, 0);
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_ks_277_, v___x_278_, v_x_263_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
size_t v_x_733__boxed_283_; uint8_t v_res_284_; lean_object* v_r_285_; 
v_x_733__boxed_283_ = lean_unbox_usize(v_x_281_);
lean_dec(v_x_281_);
v_res_284_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_280_, v_x_733__boxed_283_, v_x_282_);
lean_dec(v_x_282_);
lean_dec_ref(v_x_280_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
uint64_t v___y_289_; 
if (lean_obj_tag(v_x_287_) == 0)
{
uint64_t v___x_292_; 
v___x_292_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_289_ = v___x_292_;
goto v___jp_288_;
}
else
{
uint64_t v_hash_293_; 
v_hash_293_ = lean_ctor_get_uint64(v_x_287_, sizeof(void*)*2);
v___y_289_ = v_hash_293_;
goto v___jp_288_;
}
v___jp_288_:
{
size_t v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_uint64_to_usize(v___y_289_);
v___x_291_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_286_, v___x_290_, v_x_287_);
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg___boxed(lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_294_, v_x_295_);
lean_dec(v_x_295_);
lean_dec_ref(v_x_294_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object* v_categories_298_, lean_object* v_catName_299_, lean_object* v_initial_300_){
_start:
{
uint8_t v___x_301_; 
v___x_301_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_298_, v_catName_299_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_298_, v_catName_299_, v_initial_300_);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
else
{
lean_object* v___x_304_; 
lean_dec_ref(v_initial_300_);
lean_dec_ref(v_categories_298_);
v___x_304_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_299_);
return v___x_304_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(lean_object* v_00_u03b2_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
uint8_t v___x_308_; 
v___x_308_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_306_, v_x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___boxed(lean_object* v_00_u03b2_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(v_00_u03b2_309_, v_x_310_, v_x_311_);
lean_dec(v_x_311_);
lean_dec_ref(v_x_310_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1(lean_object* v_00_u03b2_314_, lean_object* v_x_315_, lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_x_315_, v_x_316_, v_x_317_);
return v___x_318_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(lean_object* v_00_u03b2_319_, lean_object* v_x_320_, size_t v_x_321_, lean_object* v_x_322_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_320_, v_x_321_, v_x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_324_, lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
size_t v_x_817__boxed_328_; uint8_t v_res_329_; lean_object* v_r_330_; 
v_x_817__boxed_328_ = lean_unbox_usize(v_x_326_);
lean_dec(v_x_326_);
v_res_329_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(v_00_u03b2_324_, v_x_325_, v_x_817__boxed_328_, v_x_327_);
lean_dec(v_x_327_);
lean_dec_ref(v_x_325_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(lean_object* v_00_u03b2_331_, lean_object* v_x_332_, size_t v_x_333_, size_t v_x_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_332_, v_x_333_, v_x_334_, v_x_335_, v_x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_338_, lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
size_t v_x_828__boxed_344_; size_t v_x_829__boxed_345_; lean_object* v_res_346_; 
v_x_828__boxed_344_ = lean_unbox_usize(v_x_340_);
lean_dec(v_x_340_);
v_x_829__boxed_345_ = lean_unbox_usize(v_x_341_);
lean_dec(v_x_341_);
v_res_346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(v_00_u03b2_338_, v_x_339_, v_x_828__boxed_344_, v_x_829__boxed_345_, v_x_342_, v_x_343_);
return v_res_346_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_347_, lean_object* v_keys_348_, lean_object* v_vals_349_, lean_object* v_heq_350_, lean_object* v_i_351_, lean_object* v_k_352_){
_start:
{
uint8_t v___x_353_; 
v___x_353_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_348_, v_i_351_, v_k_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_354_, lean_object* v_keys_355_, lean_object* v_vals_356_, lean_object* v_heq_357_, lean_object* v_i_358_, lean_object* v_k_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(v_00_u03b2_354_, v_keys_355_, v_vals_356_, v_heq_357_, v_i_358_, v_k_359_);
lean_dec(v_k_359_);
lean_dec_ref(v_vals_356_);
lean_dec_ref(v_keys_355_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_362_, lean_object* v_n_363_, lean_object* v_k_364_, lean_object* v_v_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v_n_363_, v_k_364_, v_v_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_367_, size_t v_depth_368_, lean_object* v_keys_369_, lean_object* v_vals_370_, lean_object* v_heq_371_, lean_object* v_i_372_, lean_object* v_entries_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_368_, v_keys_369_, v_vals_370_, v_i_372_, v_entries_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_375_, lean_object* v_depth_376_, lean_object* v_keys_377_, lean_object* v_vals_378_, lean_object* v_heq_379_, lean_object* v_i_380_, lean_object* v_entries_381_){
_start:
{
size_t v_depth_boxed_382_; lean_object* v_res_383_; 
v_depth_boxed_382_ = lean_unbox_usize(v_depth_376_);
lean_dec(v_depth_376_);
v_res_383_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(v_00_u03b2_375_, v_depth_boxed_382_, v_keys_377_, v_vals_378_, v_heq_379_, v_i_380_, v_entries_381_);
lean_dec_ref(v_vals_378_);
lean_dec_ref(v_keys_377_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_x_385_, v_x_386_, v_x_387_, v_x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(lean_object* v_e_390_){
_start:
{
if (lean_obj_tag(v_e_390_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_400_; 
v_a_392_ = lean_ctor_get(v_e_390_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v_e_390_);
if (v_isSharedCheck_400_ == 0)
{
v___x_394_ = v_e_390_;
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v_e_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = lean_mk_io_user_error(v_a_392_);
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 1);
lean_ctor_set(v___x_394_, 0, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
v_a_401_ = lean_ctor_get(v_e_390_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v_e_390_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v_e_390_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v_e_390_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 0);
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg___boxed(lean_object* v_e_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(lean_object* v_00_u03b1_412_, lean_object* v_e_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___boxed(lean_object* v_00_u03b1_416_, lean_object* v_e_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(v_00_u03b1_416_, v_e_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object* v_catName_423_, lean_object* v_declName_424_, uint8_t v_behavior_425_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_427_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_428_ = lean_st_ref_get(v___x_427_);
v___x_429_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_430_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_431_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_431_, 0, v_declName_424_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
lean_ctor_set(v___x_431_, 2, v___x_430_);
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*3, v_behavior_425_);
v___x_432_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(v___x_428_, v_catName_423_, v___x_431_);
v___x_433_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_432_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_442_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_442_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = lean_st_ref_set(v___x_427_, v_a_434_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_438_);
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
v_a_443_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_433_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_433_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object* v_catName_451_, lean_object* v_declName_452_, lean_object* v_behavior_453_, lean_object* v_a_454_){
_start:
{
uint8_t v_behavior_boxed_455_; lean_object* v_res_456_; 
v_behavior_boxed_455_ = lean_unbox(v_behavior_453_);
v_res_456_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_451_, v_declName_452_, v_behavior_boxed_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(lean_object* v_x_457_){
_start:
{
switch(lean_obj_tag(v_x_457_))
{
case 0:
{
lean_object* v___x_458_; 
v___x_458_ = lean_unsigned_to_nat(0u);
return v___x_458_;
}
case 1:
{
lean_object* v___x_459_; 
v___x_459_ = lean_unsigned_to_nat(1u);
return v___x_459_;
}
case 2:
{
lean_object* v___x_460_; 
v___x_460_ = lean_unsigned_to_nat(2u);
return v___x_460_;
}
default: 
{
lean_object* v___x_461_; 
v___x_461_ = lean_unsigned_to_nat(3u);
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___boxed(lean_object* v_x_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx(v_x_462_);
lean_dec_ref(v_x_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(lean_object* v_t_464_, lean_object* v_k_465_){
_start:
{
switch(lean_obj_tag(v_t_464_))
{
case 0:
{
lean_object* v_val_466_; lean_object* v___x_467_; 
v_val_466_ = lean_ctor_get(v_t_464_, 0);
lean_inc_ref(v_val_466_);
lean_dec_ref_known(v_t_464_, 1);
v___x_467_ = lean_apply_1(v_k_465_, v_val_466_);
return v___x_467_;
}
case 1:
{
lean_object* v_val_468_; lean_object* v___x_469_; 
v_val_468_ = lean_ctor_get(v_t_464_, 0);
lean_inc(v_val_468_);
lean_dec_ref_known(v_t_464_, 1);
v___x_469_ = lean_apply_1(v_k_465_, v_val_468_);
return v___x_469_;
}
case 2:
{
lean_object* v_catName_470_; lean_object* v_declName_471_; uint8_t v_behavior_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_catName_470_ = lean_ctor_get(v_t_464_, 0);
lean_inc(v_catName_470_);
v_declName_471_ = lean_ctor_get(v_t_464_, 1);
lean_inc(v_declName_471_);
v_behavior_472_ = lean_ctor_get_uint8(v_t_464_, sizeof(void*)*2);
lean_dec_ref_known(v_t_464_, 2);
v___x_473_ = lean_box(v_behavior_472_);
v___x_474_ = lean_apply_3(v_k_465_, v_catName_470_, v_declName_471_, v___x_473_);
return v___x_474_;
}
default: 
{
lean_object* v_catName_475_; lean_object* v_declName_476_; lean_object* v_prio_477_; lean_object* v___x_478_; 
v_catName_475_ = lean_ctor_get(v_t_464_, 0);
lean_inc(v_catName_475_);
v_declName_476_ = lean_ctor_get(v_t_464_, 1);
lean_inc(v_declName_476_);
v_prio_477_ = lean_ctor_get(v_t_464_, 2);
lean_inc(v_prio_477_);
lean_dec_ref_known(v_t_464_, 3);
v___x_478_ = lean_apply_3(v_k_465_, v_catName_475_, v_declName_476_, v_prio_477_);
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(lean_object* v_motive_479_, lean_object* v_ctorIdx_480_, lean_object* v_t_481_, lean_object* v_h_482_, lean_object* v_k_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_481_, v_k_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___boxed(lean_object* v_motive_485_, lean_object* v_ctorIdx_486_, lean_object* v_t_487_, lean_object* v_h_488_, lean_object* v_k_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(v_motive_485_, v_ctorIdx_486_, v_t_487_, v_h_488_, v_k_489_);
lean_dec(v_ctorIdx_486_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim___redArg(lean_object* v_t_491_, lean_object* v_token_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_491_, v_token_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim(lean_object* v_motive_494_, lean_object* v_t_495_, lean_object* v_h_496_, lean_object* v_token_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_495_, v_token_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim___redArg(lean_object* v_t_499_, lean_object* v_kind_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_499_, v_kind_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim(lean_object* v_motive_502_, lean_object* v_t_503_, lean_object* v_h_504_, lean_object* v_kind_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_503_, v_kind_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim___redArg(lean_object* v_t_507_, lean_object* v_category_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_507_, v_category_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim(lean_object* v_motive_510_, lean_object* v_t_511_, lean_object* v_h_512_, lean_object* v_category_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_511_, v_category_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim___redArg(lean_object* v_t_515_, lean_object* v_parser_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_515_, v_parser_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim(lean_object* v_motive_518_, lean_object* v_t_519_, lean_object* v_h_520_, lean_object* v_parser_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_519_, v_parser_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx(lean_object* v_x_528_){
_start:
{
switch(lean_obj_tag(v_x_528_))
{
case 0:
{
lean_object* v___x_529_; 
v___x_529_ = lean_unsigned_to_nat(0u);
return v___x_529_;
}
case 1:
{
lean_object* v___x_530_; 
v___x_530_ = lean_unsigned_to_nat(1u);
return v___x_530_;
}
case 2:
{
lean_object* v___x_531_; 
v___x_531_ = lean_unsigned_to_nat(2u);
return v___x_531_;
}
default: 
{
lean_object* v___x_532_; 
v___x_532_ = lean_unsigned_to_nat(3u);
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___boxed(lean_object* v_x_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Parser_ParserExtension_Entry_ctorIdx(v_x_533_);
lean_dec_ref(v_x_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(lean_object* v_t_535_, lean_object* v_k_536_){
_start:
{
switch(lean_obj_tag(v_t_535_))
{
case 0:
{
lean_object* v_val_537_; lean_object* v___x_538_; 
v_val_537_ = lean_ctor_get(v_t_535_, 0);
lean_inc_ref(v_val_537_);
lean_dec_ref_known(v_t_535_, 1);
v___x_538_ = lean_apply_1(v_k_536_, v_val_537_);
return v___x_538_;
}
case 1:
{
lean_object* v_val_539_; lean_object* v___x_540_; 
v_val_539_ = lean_ctor_get(v_t_535_, 0);
lean_inc(v_val_539_);
lean_dec_ref_known(v_t_535_, 1);
v___x_540_ = lean_apply_1(v_k_536_, v_val_539_);
return v___x_540_;
}
case 2:
{
lean_object* v_catName_541_; lean_object* v_declName_542_; uint8_t v_behavior_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_catName_541_ = lean_ctor_get(v_t_535_, 0);
lean_inc(v_catName_541_);
v_declName_542_ = lean_ctor_get(v_t_535_, 1);
lean_inc(v_declName_542_);
v_behavior_543_ = lean_ctor_get_uint8(v_t_535_, sizeof(void*)*2);
lean_dec_ref_known(v_t_535_, 2);
v___x_544_ = lean_box(v_behavior_543_);
v___x_545_ = lean_apply_3(v_k_536_, v_catName_541_, v_declName_542_, v___x_544_);
return v___x_545_;
}
default: 
{
lean_object* v_catName_546_; lean_object* v_declName_547_; uint8_t v_leading_548_; lean_object* v_p_549_; lean_object* v_prio_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_catName_546_ = lean_ctor_get(v_t_535_, 0);
lean_inc(v_catName_546_);
v_declName_547_ = lean_ctor_get(v_t_535_, 1);
lean_inc(v_declName_547_);
v_leading_548_ = lean_ctor_get_uint8(v_t_535_, sizeof(void*)*4);
v_p_549_ = lean_ctor_get(v_t_535_, 2);
lean_inc_ref(v_p_549_);
v_prio_550_ = lean_ctor_get(v_t_535_, 3);
lean_inc(v_prio_550_);
lean_dec_ref_known(v_t_535_, 4);
v___x_551_ = lean_box(v_leading_548_);
v___x_552_ = lean_apply_5(v_k_536_, v_catName_546_, v_declName_547_, v___x_551_, v_p_549_, v_prio_550_);
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim(lean_object* v_motive_553_, lean_object* v_ctorIdx_554_, lean_object* v_t_555_, lean_object* v_h_556_, lean_object* v_k_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_555_, v_k_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___boxed(lean_object* v_motive_559_, lean_object* v_ctorIdx_560_, lean_object* v_t_561_, lean_object* v_h_562_, lean_object* v_k_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Parser_ParserExtension_Entry_ctorElim(v_motive_559_, v_ctorIdx_560_, v_t_561_, v_h_562_, v_k_563_);
lean_dec(v_ctorIdx_560_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim___redArg(lean_object* v_t_565_, lean_object* v_token_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_565_, v_token_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim(lean_object* v_motive_568_, lean_object* v_t_569_, lean_object* v_h_570_, lean_object* v_token_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_569_, v_token_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim___redArg(lean_object* v_t_573_, lean_object* v_kind_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_573_, v_kind_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim(lean_object* v_motive_576_, lean_object* v_t_577_, lean_object* v_h_578_, lean_object* v_kind_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_577_, v_kind_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim___redArg(lean_object* v_t_581_, lean_object* v_category_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_581_, v_category_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim(lean_object* v_motive_584_, lean_object* v_t_585_, lean_object* v_h_586_, lean_object* v_category_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_585_, v_category_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim___redArg(lean_object* v_t_589_, lean_object* v_parser_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_589_, v_parser_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim(lean_object* v_motive_592_, lean_object* v_t_593_, lean_object* v_h_594_, lean_object* v_parser_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_593_, v_parser_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object* v_x_601_){
_start:
{
switch(lean_obj_tag(v_x_601_))
{
case 0:
{
lean_object* v_val_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
v_val_602_ = lean_ctor_get(v_x_601_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v_x_601_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_val_602_);
lean_dec(v_x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_val_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
case 1:
{
lean_object* v_val_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
v_val_610_ = lean_ctor_get(v_x_601_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v_x_601_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_val_610_);
lean_dec(v_x_601_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_val_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
case 2:
{
lean_object* v_catName_618_; lean_object* v_declName_619_; uint8_t v_behavior_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
v_catName_618_ = lean_ctor_get(v_x_601_, 0);
v_declName_619_ = lean_ctor_get(v_x_601_, 1);
v_behavior_620_ = lean_ctor_get_uint8(v_x_601_, sizeof(void*)*2);
v_isSharedCheck_627_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v_x_601_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_declName_619_);
lean_inc(v_catName_618_);
lean_dec(v_x_601_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_catName_618_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_declName_619_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*2, v_behavior_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
default: 
{
lean_object* v_catName_628_; lean_object* v_declName_629_; lean_object* v_prio_630_; lean_object* v___x_631_; 
v_catName_628_ = lean_ctor_get(v_x_601_, 0);
lean_inc(v_catName_628_);
v_declName_629_ = lean_ctor_get(v_x_601_, 1);
lean_inc(v_declName_629_);
v_prio_630_ = lean_ctor_get(v_x_601_, 3);
lean_inc(v_prio_630_);
lean_dec_ref_known(v_x_601_, 4);
v___x_631_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_631_, 0, v_catName_628_);
lean_ctor_set(v___x_631_, 1, v_declName_629_);
lean_ctor_set(v___x_631_, 2, v_prio_630_);
return v___x_631_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_633_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_632_);
lean_ctor_set(v___x_634_, 2, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default(void){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = lean_obj_once(&l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0, &l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0_once, _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState(void){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_638_ = l_Lean_Parser_builtinTokenTable;
v___x_639_ = lean_st_ref_get(v___x_638_);
v___x_640_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_641_ = lean_st_ref_get(v___x_640_);
v___x_642_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_643_ = lean_st_ref_get(v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_644_, 0, v___x_639_);
lean_ctor_set(v___x_644_, 1, v___x_641_);
lean_ctor_set(v___x_644_, 2, v___x_643_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object* v_tokens_651_, lean_object* v_tk_652_){
_start:
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = ((lean_object*)(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0));
v___x_654_ = lean_string_dec_eq(v_tk_652_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Data_Trie_find_x3f___redArg(v_tokens_651_, v_tk_652_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_inc_ref(v_tk_652_);
v___x_656_ = l_Lean_Data_Trie_insert___redArg(v_tokens_651_, v_tk_652_, v_tk_652_);
lean_dec_ref(v_tk_652_);
v___x_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
else
{
lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref(v_tk_652_);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v___x_655_, 0);
lean_dec(v_unused_665_);
v___x_659_ = v___x_655_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_dec(v___x_655_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_tokens_651_);
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_tokens_651_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
else
{
lean_object* v___x_666_; 
lean_dec_ref(v_tk_652_);
lean_dec_ref(v_tokens_651_);
v___x_666_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1));
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg(lean_object* v_catName_669_){
_start:
{
lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_670_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0));
v___x_671_ = 1;
v___x_672_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_669_, v___x_671_);
v___x_673_ = lean_string_append(v___x_670_, v___x_672_);
lean_dec_ref(v___x_672_);
v___x_674_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_675_ = lean_string_append(v___x_673_, v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object* v_00_u03b1_677_, lean_object* v_catName_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object* v_categories_682_, lean_object* v_catName_683_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__0));
v___x_685_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__1));
v___x_686_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_684_, v___x_685_, v_categories_682_, v_catName_683_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory___boxed(lean_object* v_categories_687_, lean_object* v_catName_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Parser_getCategory(v_categories_687_, v_catName_688_);
lean_dec_ref(v_categories_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(lean_object* v_as_691_){
_start:
{
lean_object* v___f_692_; lean_object* v___x_693_; 
v___f_692_ = ((lean_object*)(l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0));
v___x_693_ = l_List_eraseDupsBy___redArg(v___f_692_, v_as_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(lean_object* v_p_694_, lean_object* v_prio_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
if (lean_obj_tag(v_x_697_) == 0)
{
lean_dec(v_prio_695_);
lean_dec_ref(v_p_694_);
return v_x_696_;
}
else
{
lean_object* v_head_698_; lean_object* v_tail_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_719_; 
v_head_698_ = lean_ctor_get(v_x_697_, 0);
v_tail_699_ = lean_ctor_get(v_x_697_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_x_697_);
if (v_isSharedCheck_719_ == 0)
{
v___x_701_ = v_x_697_;
v_isShared_702_ = v_isSharedCheck_719_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_tail_699_);
lean_inc(v_head_698_);
lean_dec(v_x_697_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_719_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_leadingTable_703_; lean_object* v_leadingParsers_704_; lean_object* v_trailingTable_705_; lean_object* v_trailingParsers_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_718_; 
v_leadingTable_703_ = lean_ctor_get(v_x_696_, 0);
v_leadingParsers_704_ = lean_ctor_get(v_x_696_, 1);
v_trailingTable_705_ = lean_ctor_get(v_x_696_, 2);
v_trailingParsers_706_ = lean_ctor_get(v_x_696_, 3);
v_isSharedCheck_718_ = !lean_is_exclusive(v_x_696_);
if (v_isSharedCheck_718_ == 0)
{
v___x_708_ = v_x_696_;
v_isShared_709_ = v_isSharedCheck_718_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_trailingParsers_706_);
lean_inc(v_trailingTable_705_);
lean_inc(v_leadingParsers_704_);
lean_inc(v_leadingTable_703_);
lean_dec(v_x_696_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_718_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
lean_inc(v_prio_695_);
lean_inc_ref(v_p_694_);
if (v_isShared_702_ == 0)
{
lean_ctor_set_tag(v___x_701_, 0);
lean_ctor_set(v___x_701_, 1, v_prio_695_);
lean_ctor_set(v___x_701_, 0, v_p_694_);
v___x_711_ = v___x_701_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_p_694_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_prio_695_);
v___x_711_ = v_reuseFailAlloc_717_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = l_Lean_Parser_TokenMap_insert___redArg(v_leadingTable_703_, v_head_698_, v___x_711_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_712_);
v___x_714_ = v___x_708_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_leadingParsers_704_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_trailingTable_705_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_trailingParsers_706_);
v___x_714_ = v_reuseFailAlloc_716_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
v_x_696_ = v___x_714_;
v_x_697_ = v_tail_699_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_720_, lean_object* v_vals_721_, lean_object* v_i_722_, lean_object* v_k_723_){
_start:
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_array_get_size(v_keys_720_);
v___x_725_ = lean_nat_dec_lt(v_i_722_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec(v_i_722_);
v___x_726_ = lean_box(0);
return v___x_726_;
}
else
{
lean_object* v_k_x27_727_; uint8_t v___x_728_; 
v_k_x27_727_ = lean_array_fget_borrowed(v_keys_720_, v_i_722_);
v___x_728_ = lean_name_eq(v_k_723_, v_k_x27_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_add(v_i_722_, v___x_729_);
lean_dec(v_i_722_);
v_i_722_ = v___x_730_;
goto _start;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_array_fget_borrowed(v_vals_721_, v_i_722_);
lean_dec(v_i_722_);
lean_inc(v___x_732_);
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_734_, lean_object* v_vals_735_, lean_object* v_i_736_, lean_object* v_k_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_734_, v_vals_735_, v_i_736_, v_k_737_);
lean_dec(v_k_737_);
lean_dec_ref(v_vals_735_);
lean_dec_ref(v_keys_734_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(lean_object* v_x_739_, size_t v_x_740_, lean_object* v_x_741_){
_start:
{
if (lean_obj_tag(v_x_739_) == 0)
{
lean_object* v_es_742_; lean_object* v___x_743_; size_t v___x_744_; size_t v___x_745_; lean_object* v_j_746_; lean_object* v___x_747_; 
v_es_742_ = lean_ctor_get(v_x_739_, 0);
v___x_743_ = lean_box(2);
v___x_744_ = ((size_t)31ULL);
v___x_745_ = lean_usize_land(v_x_740_, v___x_744_);
v_j_746_ = lean_usize_to_nat(v___x_745_);
v___x_747_ = lean_array_get_borrowed(v___x_743_, v_es_742_, v_j_746_);
lean_dec(v_j_746_);
switch(lean_obj_tag(v___x_747_))
{
case 0:
{
lean_object* v_key_748_; lean_object* v_val_749_; uint8_t v___x_750_; 
v_key_748_ = lean_ctor_get(v___x_747_, 0);
v_val_749_ = lean_ctor_get(v___x_747_, 1);
v___x_750_ = lean_name_eq(v_x_741_, v_key_748_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
v___x_751_ = lean_box(0);
return v___x_751_;
}
else
{
lean_object* v___x_752_; 
lean_inc(v_val_749_);
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v_val_749_);
return v___x_752_;
}
}
case 1:
{
lean_object* v_node_753_; size_t v___x_754_; size_t v___x_755_; 
v_node_753_ = lean_ctor_get(v___x_747_, 0);
v___x_754_ = ((size_t)5ULL);
v___x_755_ = lean_usize_shift_right(v_x_740_, v___x_754_);
v_x_739_ = v_node_753_;
v_x_740_ = v___x_755_;
goto _start;
}
default: 
{
lean_object* v___x_757_; 
v___x_757_ = lean_box(0);
return v___x_757_;
}
}
}
else
{
lean_object* v_ks_758_; lean_object* v_vs_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_ks_758_ = lean_ctor_get(v_x_739_, 0);
v_vs_759_ = lean_ctor_get(v_x_739_, 1);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_ks_758_, v_vs_759_, v___x_760_, v_x_741_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg___boxed(lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
size_t v_x_493__boxed_765_; lean_object* v_res_766_; 
v_x_493__boxed_765_ = lean_unbox_usize(v_x_763_);
lean_dec(v_x_763_);
v_res_766_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_762_, v_x_493__boxed_765_, v_x_764_);
lean_dec(v_x_764_);
lean_dec_ref(v_x_762_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
uint64_t v___y_770_; 
if (lean_obj_tag(v_x_768_) == 0)
{
uint64_t v___x_773_; 
v___x_773_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___closed__0);
v___y_770_ = v___x_773_;
goto v___jp_769_;
}
else
{
uint64_t v_hash_774_; 
v_hash_774_ = lean_ctor_get_uint64(v_x_768_, sizeof(void*)*2);
v___y_770_ = v_hash_774_;
goto v___jp_769_;
}
v___jp_769_:
{
size_t v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_uint64_to_usize(v___y_770_);
v___x_772_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_767_, v___x_771_, v_x_768_);
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg___boxed(lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_775_, v_x_776_);
lean_dec(v_x_776_);
lean_dec_ref(v_x_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
if (lean_obj_tag(v_a_778_) == 0)
{
lean_object* v___x_780_; 
v___x_780_ = l_List_reverse___redArg(v_a_779_);
return v___x_780_;
}
else
{
lean_object* v_head_781_; lean_object* v_tail_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_792_; 
v_head_781_ = lean_ctor_get(v_a_778_, 0);
v_tail_782_ = lean_ctor_get(v_a_778_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_a_778_);
if (v_isSharedCheck_792_ == 0)
{
v___x_784_ = v_a_778_;
v_isShared_785_ = v_isSharedCheck_792_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_tail_782_);
lean_inc(v_head_781_);
lean_dec(v_a_778_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_792_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_786_ = lean_box(0);
v___x_787_ = l_Lean_Name_str___override(v___x_786_, v_head_781_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v_a_779_);
lean_ctor_set(v___x_784_, 0, v___x_787_);
v___x_789_ = v___x_784_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_a_779_);
v___x_789_ = v_reuseFailAlloc_791_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
v_a_778_ = v_tail_782_;
v_a_779_ = v___x_789_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object* v_categories_793_, lean_object* v_catName_794_, lean_object* v_declName_795_, lean_object* v_p_796_, lean_object* v_prio_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_793_, v_catName_794_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v___x_799_; 
lean_dec(v_prio_797_);
lean_dec_ref(v_p_796_);
lean_dec(v_declName_795_);
lean_dec_ref(v_categories_793_);
v___x_799_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_794_);
return v___x_799_;
}
else
{
lean_object* v_val_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_846_; 
v_val_800_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_846_ == 0)
{
v___x_802_ = v___x_798_;
v_isShared_803_ = v_isSharedCheck_846_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_val_800_);
lean_dec(v___x_798_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_846_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v_info_804_; lean_object* v_declName_805_; lean_object* v_kinds_806_; lean_object* v_tables_807_; uint8_t v_behavior_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_845_; 
v_info_804_ = lean_ctor_get(v_p_796_, 0);
v_declName_805_ = lean_ctor_get(v_val_800_, 0);
v_kinds_806_ = lean_ctor_get(v_val_800_, 1);
v_tables_807_ = lean_ctor_get(v_val_800_, 2);
v_behavior_808_ = lean_ctor_get_uint8(v_val_800_, sizeof(void*)*3);
v_isSharedCheck_845_ = !lean_is_exclusive(v_val_800_);
if (v_isSharedCheck_845_ == 0)
{
v___x_810_ = v_val_800_;
v_isShared_811_ = v_isSharedCheck_845_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_tables_807_);
lean_inc(v_kinds_806_);
lean_inc(v_declName_805_);
lean_dec(v_val_800_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_845_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_firstTokens_812_; lean_object* v_kinds_813_; lean_object* v_tks_815_; 
v_firstTokens_812_ = lean_ctor_get(v_info_804_, 2);
v_kinds_813_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_806_, v_declName_795_);
switch(lean_obj_tag(v_firstTokens_812_))
{
case 2:
{
lean_object* v_a_827_; 
v_a_827_ = lean_ctor_get(v_firstTokens_812_, 0);
lean_inc(v_a_827_);
v_tks_815_ = v_a_827_;
goto v___jp_814_;
}
case 3:
{
lean_object* v_a_828_; 
v_a_828_ = lean_ctor_get(v_firstTokens_812_, 0);
lean_inc(v_a_828_);
v_tks_815_ = v_a_828_;
goto v___jp_814_;
}
default: 
{
lean_object* v_leadingTable_829_; lean_object* v_leadingParsers_830_; lean_object* v_trailingTable_831_; lean_object* v_trailingParsers_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_844_; 
lean_del_object(v___x_810_);
lean_del_object(v___x_802_);
v_leadingTable_829_ = lean_ctor_get(v_tables_807_, 0);
v_leadingParsers_830_ = lean_ctor_get(v_tables_807_, 1);
v_trailingTable_831_ = lean_ctor_get(v_tables_807_, 2);
v_trailingParsers_832_ = lean_ctor_get(v_tables_807_, 3);
v_isSharedCheck_844_ = !lean_is_exclusive(v_tables_807_);
if (v_isSharedCheck_844_ == 0)
{
v___x_834_ = v_tables_807_;
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_trailingParsers_832_);
lean_inc(v_trailingTable_831_);
lean_inc(v_leadingParsers_830_);
lean_inc(v_leadingTable_829_);
lean_dec(v_tables_807_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v_tables_839_; 
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v_p_796_);
lean_ctor_set(v___x_836_, 1, v_prio_797_);
v___x_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v_leadingParsers_830_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_837_);
v_tables_839_ = v___x_834_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_leadingTable_829_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v_trailingTable_831_);
lean_ctor_set(v_reuseFailAlloc_843_, 3, v_trailingParsers_832_);
v_tables_839_ = v_reuseFailAlloc_843_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_840_, 0, v_declName_805_);
lean_ctor_set(v___x_840_, 1, v_kinds_813_);
lean_ctor_set(v___x_840_, 2, v_tables_839_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3, v_behavior_808_);
v___x_841_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_793_, v_catName_794_, v___x_840_);
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
}
}
v___jp_814_:
{
lean_object* v___x_816_; lean_object* v_tks_817_; lean_object* v___x_818_; lean_object* v_tables_819_; lean_object* v___x_821_; 
v___x_816_ = lean_box(0);
v_tks_817_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_815_, v___x_816_);
v___x_818_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_817_);
v_tables_819_ = l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(v_p_796_, v_prio_797_, v_tables_807_, v___x_818_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 2, v_tables_819_);
lean_ctor_set(v___x_810_, 1, v_kinds_813_);
v___x_821_ = v___x_810_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_declName_805_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_kinds_813_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v_tables_819_);
lean_ctor_set_uint8(v_reuseFailAlloc_826_, sizeof(void*)*3, v_behavior_808_);
v___x_821_ = v_reuseFailAlloc_826_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_793_, v_catName_794_, v___x_821_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_822_);
v___x_824_ = v___x_802_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_848_, v_x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___boxed(lean_object* v_00_u03b2_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(v_00_u03b2_851_, v_x_852_, v_x_853_);
lean_dec(v_x_853_);
lean_dec_ref(v_x_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_object* v_00_u03b2_855_, lean_object* v_x_856_, size_t v_x_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_856_, v_x_857_, v_x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___boxed(lean_object* v_00_u03b2_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
size_t v_x_665__boxed_864_; lean_object* v_res_865_; 
v_x_665__boxed_864_ = lean_unbox_usize(v_x_862_);
lean_dec(v_x_862_);
v_res_865_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(v_00_u03b2_860_, v_x_861_, v_x_665__boxed_864_, v_x_863_);
lean_dec(v_x_863_);
lean_dec_ref(v_x_861_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_866_, lean_object* v_keys_867_, lean_object* v_vals_868_, lean_object* v_heq_869_, lean_object* v_i_870_, lean_object* v_k_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_867_, v_vals_868_, v_i_870_, v_k_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_873_, lean_object* v_keys_874_, lean_object* v_vals_875_, lean_object* v_heq_876_, lean_object* v_i_877_, lean_object* v_k_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(v_00_u03b2_873_, v_keys_874_, v_vals_875_, v_heq_876_, v_i_877_, v_k_878_);
lean_dec(v_k_878_);
lean_dec_ref(v_vals_875_);
lean_dec_ref(v_keys_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(lean_object* v_p_880_, lean_object* v_prio_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
if (lean_obj_tag(v_x_883_) == 0)
{
lean_dec(v_prio_881_);
lean_dec_ref(v_p_880_);
return v_x_882_;
}
else
{
lean_object* v_head_884_; lean_object* v_tail_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_905_; 
v_head_884_ = lean_ctor_get(v_x_883_, 0);
v_tail_885_ = lean_ctor_get(v_x_883_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_x_883_);
if (v_isSharedCheck_905_ == 0)
{
v___x_887_ = v_x_883_;
v_isShared_888_ = v_isSharedCheck_905_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_tail_885_);
lean_inc(v_head_884_);
lean_dec(v_x_883_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_905_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_leadingTable_889_; lean_object* v_leadingParsers_890_; lean_object* v_trailingTable_891_; lean_object* v_trailingParsers_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_904_; 
v_leadingTable_889_ = lean_ctor_get(v_x_882_, 0);
v_leadingParsers_890_ = lean_ctor_get(v_x_882_, 1);
v_trailingTable_891_ = lean_ctor_get(v_x_882_, 2);
v_trailingParsers_892_ = lean_ctor_get(v_x_882_, 3);
v_isSharedCheck_904_ = !lean_is_exclusive(v_x_882_);
if (v_isSharedCheck_904_ == 0)
{
v___x_894_ = v_x_882_;
v_isShared_895_ = v_isSharedCheck_904_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_trailingParsers_892_);
lean_inc(v_trailingTable_891_);
lean_inc(v_leadingParsers_890_);
lean_inc(v_leadingTable_889_);
lean_dec(v_x_882_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_904_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
lean_inc(v_prio_881_);
lean_inc_ref(v_p_880_);
if (v_isShared_888_ == 0)
{
lean_ctor_set_tag(v___x_887_, 0);
lean_ctor_set(v___x_887_, 1, v_prio_881_);
lean_ctor_set(v___x_887_, 0, v_p_880_);
v___x_897_ = v___x_887_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_p_880_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_prio_881_);
v___x_897_ = v_reuseFailAlloc_903_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = l_Lean_Parser_TokenMap_insert___redArg(v_trailingTable_891_, v_head_884_, v___x_897_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 2, v___x_898_);
v___x_900_ = v___x_894_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_leadingTable_889_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_leadingParsers_890_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_trailingParsers_892_);
v___x_900_ = v_reuseFailAlloc_902_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
v_x_882_ = v___x_900_;
v_x_883_ = v_tail_885_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object* v_tables_906_, lean_object* v_p_907_, lean_object* v_prio_908_){
_start:
{
lean_object* v_tks_910_; lean_object* v_info_915_; lean_object* v_firstTokens_916_; 
v_info_915_ = lean_ctor_get(v_p_907_, 0);
v_firstTokens_916_ = lean_ctor_get(v_info_915_, 2);
switch(lean_obj_tag(v_firstTokens_916_))
{
case 2:
{
lean_object* v_a_917_; 
v_a_917_ = lean_ctor_get(v_firstTokens_916_, 0);
lean_inc(v_a_917_);
v_tks_910_ = v_a_917_;
goto v___jp_909_;
}
case 3:
{
lean_object* v_a_918_; 
v_a_918_ = lean_ctor_get(v_firstTokens_916_, 0);
lean_inc(v_a_918_);
v_tks_910_ = v_a_918_;
goto v___jp_909_;
}
default: 
{
lean_object* v_leadingTable_919_; lean_object* v_leadingParsers_920_; lean_object* v_trailingTable_921_; lean_object* v_trailingParsers_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_931_; 
v_leadingTable_919_ = lean_ctor_get(v_tables_906_, 0);
v_leadingParsers_920_ = lean_ctor_get(v_tables_906_, 1);
v_trailingTable_921_ = lean_ctor_get(v_tables_906_, 2);
v_trailingParsers_922_ = lean_ctor_get(v_tables_906_, 3);
v_isSharedCheck_931_ = !lean_is_exclusive(v_tables_906_);
if (v_isSharedCheck_931_ == 0)
{
v___x_924_ = v_tables_906_;
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_trailingParsers_922_);
lean_inc(v_trailingTable_921_);
lean_inc(v_leadingParsers_920_);
lean_inc(v_leadingTable_919_);
lean_dec(v_tables_906_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_p_907_);
lean_ctor_set(v___x_926_, 1, v_prio_908_);
v___x_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v_trailingParsers_922_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 3, v___x_927_);
v___x_929_ = v___x_924_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_leadingTable_919_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_leadingParsers_920_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_trailingTable_921_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
v___jp_909_:
{
lean_object* v___x_911_; lean_object* v_tks_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_911_ = lean_box(0);
v_tks_912_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_910_, v___x_911_);
v___x_913_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_912_);
v___x_914_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(v_p_907_, v_prio_908_, v_tables_906_, v___x_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object* v_categories_932_, lean_object* v_catName_933_, lean_object* v_declName_934_, lean_object* v_p_935_, lean_object* v_prio_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_932_, v_catName_933_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_938_; 
lean_dec(v_prio_936_);
lean_dec_ref(v_p_935_);
lean_dec(v_declName_934_);
lean_dec_ref(v_categories_932_);
v___x_938_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_933_);
return v___x_938_;
}
else
{
lean_object* v_val_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_960_; 
v_val_939_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_960_ == 0)
{
v___x_941_ = v___x_937_;
v_isShared_942_ = v_isSharedCheck_960_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_val_939_);
lean_dec(v___x_937_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_960_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_declName_943_; lean_object* v_kinds_944_; lean_object* v_tables_945_; uint8_t v_behavior_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_959_; 
v_declName_943_ = lean_ctor_get(v_val_939_, 0);
v_kinds_944_ = lean_ctor_get(v_val_939_, 1);
v_tables_945_ = lean_ctor_get(v_val_939_, 2);
v_behavior_946_ = lean_ctor_get_uint8(v_val_939_, sizeof(void*)*3);
v_isSharedCheck_959_ = !lean_is_exclusive(v_val_939_);
if (v_isSharedCheck_959_ == 0)
{
v___x_948_ = v_val_939_;
v_isShared_949_ = v_isSharedCheck_959_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_tables_945_);
lean_inc(v_kinds_944_);
lean_inc(v_declName_943_);
lean_dec(v_val_939_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_959_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_kinds_950_; lean_object* v_tables_951_; lean_object* v___x_953_; 
v_kinds_950_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_944_, v_declName_934_);
v_tables_951_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(v_tables_945_, v_p_935_, v_prio_936_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 2, v_tables_951_);
lean_ctor_set(v___x_948_, 1, v_kinds_950_);
v___x_953_ = v___x_948_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_declName_943_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_kinds_950_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_tables_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*3, v_behavior_946_);
v___x_953_ = v_reuseFailAlloc_958_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_932_, v_catName_933_, v___x_953_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_954_);
v___x_956_ = v___x_941_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object* v_categories_961_, lean_object* v_catName_962_, lean_object* v_declName_963_, uint8_t v_leading_964_, lean_object* v_p_965_, lean_object* v_prio_966_){
_start:
{
if (v_leading_964_ == 0)
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Parser_addTrailingParser(v_categories_961_, v_catName_962_, v_declName_963_, v_p_965_, v_prio_966_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Parser_addLeadingParser(v_categories_961_, v_catName_962_, v_declName_963_, v_p_965_, v_prio_966_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object* v_categories_969_, lean_object* v_catName_970_, lean_object* v_declName_971_, lean_object* v_leading_972_, lean_object* v_p_973_, lean_object* v_prio_974_){
_start:
{
uint8_t v_leading_boxed_975_; lean_object* v_res_976_; 
v_leading_boxed_975_ = lean_unbox(v_leading_972_);
v_res_976_ = l_Lean_Parser_addParser(v_categories_969_, v_catName_970_, v_declName_971_, v_leading_boxed_975_, v_p_973_, v_prio_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(lean_object* v_x_977_, lean_object* v_x_978_){
_start:
{
if (lean_obj_tag(v_x_978_) == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v_x_977_);
return v___x_979_;
}
else
{
lean_object* v_head_980_; lean_object* v_tail_981_; lean_object* v___x_982_; 
v_head_980_ = lean_ctor_get(v_x_978_, 0);
lean_inc(v_head_980_);
v_tail_981_ = lean_ctor_get(v_x_978_, 1);
lean_inc(v_tail_981_);
lean_dec_ref_known(v_x_978_, 2);
v___x_982_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_x_977_, v_head_980_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_dec(v_tail_981_);
return v___x_982_;
}
else
{
lean_object* v_a_983_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v_x_977_ = v_a_983_;
v_x_978_ = v_tail_981_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object* v_tokenTable_985_, lean_object* v_info_986_){
_start:
{
lean_object* v_collectTokens_987_; lean_object* v___x_988_; lean_object* v_newTokens_989_; lean_object* v___x_990_; 
v_collectTokens_987_ = lean_ctor_get(v_info_986_, 0);
lean_inc_ref(v_collectTokens_987_);
lean_dec_ref(v_info_986_);
v___x_988_ = lean_box(0);
v_newTokens_989_ = lean_apply_1(v_collectTokens_987_, v___x_988_);
v___x_990_ = l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(v_tokenTable_985_, v_newTokens_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object* v_info_993_, lean_object* v_declName_994_){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_996_ = l_Lean_Parser_builtinTokenTable;
v___x_997_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_998_ = lean_st_ref_swap(v___x_996_, v___x_997_);
v___x_999_ = l_Lean_Parser_addParserTokens(v___x_998_, v_info_993_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1016_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1016_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1016_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1004_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0));
v___x_1005_ = l_Lean_privateToUserName(v_declName_994_);
v___x_1006_ = 1;
v___x_1007_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1005_, v___x_1006_);
v___x_1008_ = lean_string_append(v___x_1004_, v___x_1007_);
lean_dec_ref(v___x_1007_);
v___x_1009_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_1010_ = lean_string_append(v___x_1008_, v___x_1009_);
v___x_1011_ = lean_string_append(v___x_1010_, v_a_1000_);
lean_dec(v_a_1000_);
v___x_1012_ = lean_mk_io_user_error(v___x_1011_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 1);
lean_ctor_set(v___x_1002_, 0, v___x_1012_);
v___x_1014_ = v___x_1002_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v_declName_994_);
v_a_1017_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1019_ = v___x_999_;
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_999_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1021_ = lean_st_ref_set(v___x_996_, v_a_1017_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set_tag(v___x_1019_, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1021_);
v___x_1023_ = v___x_1019_;
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
v___x_1192_ = lean_st_ref_set(v_mapRef_1181_, v___x_1191_);
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
v___x_1484_ = lean_st_ref_set(v___x_1481_, v___x_1483_);
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
v___x_1473_ = lean_st_ref_set(v___x_1463_, v___x_1472_);
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
v___x_1997_ = lean_st_ref_set(v___x_1994_, v___x_1996_);
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
v___x_2697_ = lean_st_ref_set(v___x_2691_, v_a_2696_);
v___x_2698_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_2699_ = lean_st_ref_take(v___x_2698_);
v_info_2700_ = lean_ctor_get(v_p_2693_, 0);
lean_inc_ref(v_info_2700_);
lean_dec_ref(v_p_2693_);
v_collectKinds_2701_ = lean_ctor_get(v_info_2700_, 1);
lean_inc_ref(v_collectKinds_2701_);
v___x_2702_ = lean_apply_1(v_collectKinds_2701_, v___x_2699_);
v___x_2703_ = lean_st_ref_set(v___x_2698_, v___x_2702_);
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
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2804_ = l_Lean_Parser_categoryParserFnRef;
v___x_2805_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_));
v___x_2806_ = lean_st_ref_set(v___x_2804_, v___x_2805_);
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
v___x_2838_ = lean_st_ref_set(v___y_2819_, v___x_2837_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2984_, lean_object* v_x_2985_, lean_object* v_x_2986_){
_start:
{
if (lean_obj_tag(v_x_2985_) == 0)
{
lean_object* v_es_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v_es_2987_ = lean_ctor_get(v_x_2985_, 0);
v___x_2988_ = lean_unsigned_to_nat(0u);
v___x_2989_ = lean_array_get_size(v_es_2987_);
v___x_2990_ = lean_nat_dec_lt(v___x_2988_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_dec(v_f_2984_);
return v_x_2986_;
}
else
{
uint8_t v___x_2991_; 
v___x_2991_ = lean_nat_dec_le(v___x_2989_, v___x_2989_);
if (v___x_2991_ == 0)
{
if (v___x_2990_ == 0)
{
lean_dec(v_f_2984_);
return v_x_2986_;
}
else
{
size_t v___x_2992_; size_t v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = ((size_t)0ULL);
v___x_2993_ = lean_usize_of_nat(v___x_2989_);
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2984_, v_es_2987_, v___x_2992_, v___x_2993_, v_x_2986_);
return v___x_2994_;
}
}
else
{
size_t v___x_2995_; size_t v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = ((size_t)0ULL);
v___x_2996_ = lean_usize_of_nat(v___x_2989_);
v___x_2997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2984_, v_es_2987_, v___x_2995_, v___x_2996_, v_x_2986_);
return v___x_2997_;
}
}
}
else
{
lean_object* v_ks_2998_; lean_object* v_vs_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v_ks_2998_ = lean_ctor_get(v_x_2985_, 0);
v_vs_2999_ = lean_ctor_get(v_x_2985_, 1);
v___x_3000_ = lean_unsigned_to_nat(0u);
v___x_3001_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2984_, v_ks_2998_, v_vs_2999_, v___x_3000_, v_x_2986_);
return v___x_3001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3002_, lean_object* v_as_3003_, size_t v_i_3004_, size_t v_stop_3005_, lean_object* v_b_3006_){
_start:
{
lean_object* v___y_3008_; uint8_t v___x_3012_; 
v___x_3012_ = lean_usize_dec_eq(v_i_3004_, v_stop_3005_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_array_uget_borrowed(v_as_3003_, v_i_3004_);
switch(lean_obj_tag(v___x_3013_))
{
case 0:
{
lean_object* v_key_3014_; lean_object* v_val_3015_; lean_object* v___x_3016_; 
v_key_3014_ = lean_ctor_get(v___x_3013_, 0);
v_val_3015_ = lean_ctor_get(v___x_3013_, 1);
lean_inc(v_f_3002_);
lean_inc(v_val_3015_);
lean_inc(v_key_3014_);
v___x_3016_ = lean_apply_3(v_f_3002_, v_b_3006_, v_key_3014_, v_val_3015_);
v___y_3008_ = v___x_3016_;
goto v___jp_3007_;
}
case 1:
{
lean_object* v_node_3017_; lean_object* v___x_3018_; 
v_node_3017_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_f_3002_);
v___x_3018_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3002_, v_node_3017_, v_b_3006_);
v___y_3008_ = v___x_3018_;
goto v___jp_3007_;
}
default: 
{
v___y_3008_ = v_b_3006_;
goto v___jp_3007_;
}
}
}
else
{
lean_dec(v_f_3002_);
return v_b_3006_;
}
v___jp_3007_:
{
size_t v___x_3009_; size_t v___x_3010_; 
v___x_3009_ = ((size_t)1ULL);
v___x_3010_ = lean_usize_add(v_i_3004_, v___x_3009_);
v_i_3004_ = v___x_3010_;
v_b_3006_ = v___y_3008_;
goto _start;
}
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3027_, lean_object* v_x_3028_, lean_object* v_x_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3027_, v_x_3028_, v_x_3029_);
lean_dec_ref(v_x_3028_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object* v_f_3031_, lean_object* v_x1_3032_, lean_object* v_x2_3033_, lean_object* v_x3_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_apply_3(v_f_3031_, v_x1_3032_, v_x2_3033_, v_x3_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object* v_map_3036_, lean_object* v_f_3037_, lean_object* v_init_3038_){
_start:
{
lean_object* v___f_3039_; lean_object* v___x_3040_; 
v___f_3039_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3039_, 0, v_f_3037_);
v___x_3040_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v___f_3039_, v_map_3036_, v_init_3038_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object* v_map_3041_, lean_object* v_f_3042_, lean_object* v_init_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3041_, v_f_3042_, v_init_3043_);
lean_dec_ref(v_map_3041_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* v_env_3046_){
_start:
{
lean_object* v___x_3047_; lean_object* v_ext_3048_; lean_object* v_toEnvExtension_3049_; lean_object* v_asyncMode_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v_kinds_3053_; lean_object* v___f_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3047_ = l_Lean_Parser_parserExtension;
v_ext_3048_ = lean_ctor_get(v___x_3047_, 1);
v_toEnvExtension_3049_ = lean_ctor_get(v_ext_3048_, 0);
v_asyncMode_3050_ = lean_ctor_get(v_toEnvExtension_3049_, 2);
v___x_3051_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3052_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3051_, v___x_3047_, v_env_3046_, v_asyncMode_3050_);
v_kinds_3053_ = lean_ctor_get(v___x_3052_, 1);
lean_inc_ref(v_kinds_3053_);
lean_dec(v___x_3052_);
v___f_3054_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKinds___closed__0));
v___x_3055_ = lean_box(0);
v___x_3056_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_kinds_3053_, v___f_3054_, v___x_3055_);
lean_dec_ref(v_kinds_3053_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object* v_00_u03c3_3057_, lean_object* v_00_u03b2_3058_, lean_object* v_map_3059_, lean_object* v_f_3060_, lean_object* v_init_3061_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3059_, v_f_3060_, v_init_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object* v_00_u03c3_3063_, lean_object* v_00_u03b2_3064_, lean_object* v_map_3065_, lean_object* v_f_3066_, lean_object* v_init_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(v_00_u03c3_3063_, v_00_u03b2_3064_, v_map_3065_, v_f_3066_, v_init_3067_);
lean_dec_ref(v_map_3065_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object* v_map_3069_, lean_object* v_f_3070_, lean_object* v_init_3071_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3070_, v_map_3069_, v_init_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object* v_map_3073_, lean_object* v_f_3074_, lean_object* v_init_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(v_map_3073_, v_f_3074_, v_init_3075_);
lean_dec_ref(v_map_3073_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object* v_00_u03c3_3077_, lean_object* v_00_u03b2_3078_, lean_object* v_map_3079_, lean_object* v_f_3080_, lean_object* v_init_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3080_, v_map_3079_, v_init_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3083_, lean_object* v_00_u03b2_3084_, lean_object* v_map_3085_, lean_object* v_f_3086_, lean_object* v_init_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(v_00_u03c3_3083_, v_00_u03b2_3084_, v_map_3085_, v_f_3086_, v_init_3087_);
lean_dec_ref(v_map_3085_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3089_, lean_object* v_00_u03b1_3090_, lean_object* v_00_u03b2_3091_, lean_object* v_f_3092_, lean_object* v_x_3093_, lean_object* v_x_3094_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3092_, v_x_3093_, v_x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3096_, lean_object* v_00_u03b1_3097_, lean_object* v_00_u03b2_3098_, lean_object* v_f_3099_, lean_object* v_x_3100_, lean_object* v_x_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(v_00_u03c3_3096_, v_00_u03b1_3097_, v_00_u03b2_3098_, v_f_3099_, v_x_3100_, v_x_3101_);
lean_dec_ref(v_x_3100_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3103_, lean_object* v_00_u03b2_3104_, lean_object* v_00_u03c3_3105_, lean_object* v_f_3106_, lean_object* v_as_3107_, size_t v_i_3108_, size_t v_stop_3109_, lean_object* v_b_3110_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3106_, v_as_3107_, v_i_3108_, v_stop_3109_, v_b_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3112_, lean_object* v_00_u03b2_3113_, lean_object* v_00_u03c3_3114_, lean_object* v_f_3115_, lean_object* v_as_3116_, lean_object* v_i_3117_, lean_object* v_stop_3118_, lean_object* v_b_3119_){
_start:
{
size_t v_i_boxed_3120_; size_t v_stop_boxed_3121_; lean_object* v_res_3122_; 
v_i_boxed_3120_ = lean_unbox_usize(v_i_3117_);
lean_dec(v_i_3117_);
v_stop_boxed_3121_ = lean_unbox_usize(v_stop_3118_);
lean_dec(v_stop_3118_);
v_res_3122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3112_, v_00_u03b2_3113_, v_00_u03c3_3114_, v_f_3115_, v_as_3116_, v_i_boxed_3120_, v_stop_boxed_3121_, v_b_3119_);
lean_dec_ref(v_as_3116_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3123_, lean_object* v_00_u03b1_3124_, lean_object* v_00_u03b2_3125_, lean_object* v_f_3126_, lean_object* v_keys_3127_, lean_object* v_vals_3128_, lean_object* v_heq_3129_, lean_object* v_i_3130_, lean_object* v_acc_3131_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3126_, v_keys_3127_, v_vals_3128_, v_i_3130_, v_acc_3131_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3133_, lean_object* v_00_u03b1_3134_, lean_object* v_00_u03b2_3135_, lean_object* v_f_3136_, lean_object* v_keys_3137_, lean_object* v_vals_3138_, lean_object* v_heq_3139_, lean_object* v_i_3140_, lean_object* v_acc_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3133_, v_00_u03b1_3134_, v_00_u03b2_3135_, v_f_3136_, v_keys_3137_, v_vals_3138_, v_heq_3139_, v_i_3140_, v_acc_3141_);
lean_dec_ref(v_vals_3138_);
lean_dec_ref(v_keys_3137_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* v_env_3143_){
_start:
{
lean_object* v___x_3144_; lean_object* v_ext_3145_; lean_object* v_toEnvExtension_3146_; lean_object* v_asyncMode_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v_tokens_3150_; 
v___x_3144_ = l_Lean_Parser_parserExtension;
v_ext_3145_ = lean_ctor_get(v___x_3144_, 1);
v_toEnvExtension_3146_ = lean_ctor_get(v_ext_3145_, 0);
v_asyncMode_3147_ = lean_ctor_get(v_toEnvExtension_3146_, 2);
v___x_3148_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3149_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3148_, v___x_3144_, v_env_3143_, v_asyncMode_3147_);
v_tokens_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc_ref(v_tokens_3150_);
lean_dec(v___x_3149_);
return v_tokens_3150_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__8));
v___x_3176_ = l_Lean_mkAtom(v___x_3175_);
return v___x_3176_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__10, &l_Lean_Parser_mkInputContext___auto__1___closed__10_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__10);
v___x_3178_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3179_ = lean_array_push(v___x_3178_, v___x_3177_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3190_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3191_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3192_ = lean_array_push(v___x_3191_, v___x_3190_);
return v___x_3192_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3193_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__15, &l_Lean_Parser_mkInputContext___auto__1___closed__15_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__15);
v___x_3194_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__13));
v___x_3195_ = lean_box(2);
v___x_3196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
lean_ctor_set(v___x_3196_, 1, v___x_3194_);
lean_ctor_set(v___x_3196_, 2, v___x_3193_);
return v___x_3196_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__16, &l_Lean_Parser_mkInputContext___auto__1___closed__16_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__16);
v___x_3198_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__11, &l_Lean_Parser_mkInputContext___auto__1___closed__11_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__11);
v___x_3199_ = lean_array_push(v___x_3198_, v___x_3197_);
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3200_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3201_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__17, &l_Lean_Parser_mkInputContext___auto__1___closed__17_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__17);
v___x_3202_ = lean_array_push(v___x_3201_, v___x_3200_);
return v___x_3202_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3203_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3204_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__18, &l_Lean_Parser_mkInputContext___auto__1___closed__18_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__18);
v___x_3205_ = lean_array_push(v___x_3204_, v___x_3203_);
return v___x_3205_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3207_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__19, &l_Lean_Parser_mkInputContext___auto__1___closed__19_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__19);
v___x_3208_ = lean_array_push(v___x_3207_, v___x_3206_);
return v___x_3208_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3209_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3210_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__20, &l_Lean_Parser_mkInputContext___auto__1___closed__20_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__20);
v___x_3211_ = lean_array_push(v___x_3210_, v___x_3209_);
return v___x_3211_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3212_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__21, &l_Lean_Parser_mkInputContext___auto__1___closed__21_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__21);
v___x_3213_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__9));
v___x_3214_ = lean_box(2);
v___x_3215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
lean_ctor_set(v___x_3215_, 1, v___x_3213_);
lean_ctor_set(v___x_3215_, 2, v___x_3212_);
return v___x_3215_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__22, &l_Lean_Parser_mkInputContext___auto__1___closed__22_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__22);
v___x_3217_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3218_ = lean_array_push(v___x_3217_, v___x_3216_);
return v___x_3218_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3219_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__23, &l_Lean_Parser_mkInputContext___auto__1___closed__23_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__23);
v___x_3220_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3221_ = lean_box(2);
v___x_3222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
lean_ctor_set(v___x_3222_, 1, v___x_3220_);
lean_ctor_set(v___x_3222_, 2, v___x_3219_);
return v___x_3222_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__24, &l_Lean_Parser_mkInputContext___auto__1___closed__24_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__24);
v___x_3224_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3225_ = lean_array_push(v___x_3224_, v___x_3223_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3226_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__25, &l_Lean_Parser_mkInputContext___auto__1___closed__25_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__25);
v___x_3227_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3228_ = lean_box(2);
v___x_3229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
lean_ctor_set(v___x_3229_, 1, v___x_3227_);
lean_ctor_set(v___x_3229_, 2, v___x_3226_);
return v___x_3229_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__26, &l_Lean_Parser_mkInputContext___auto__1___closed__26_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__26);
v___x_3231_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3232_ = lean_array_push(v___x_3231_, v___x_3230_);
return v___x_3232_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3233_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__27, &l_Lean_Parser_mkInputContext___auto__1___closed__27_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__27);
v___x_3234_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3235_ = lean_box(2);
v___x_3236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
lean_ctor_set(v___x_3236_, 1, v___x_3234_);
lean_ctor_set(v___x_3236_, 2, v___x_3233_);
return v___x_3236_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1(void){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__28, &l_Lean_Parser_mkInputContext___auto__1___closed__28_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__28);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object* v_input_3238_, lean_object* v_fileName_3239_, uint8_t v_normalizeLineEndings_3240_, lean_object* v_endPos_3241_){
_start:
{
lean_object* v_fst_3243_; lean_object* v_snd_3244_; lean_object* v_text_3250_; 
v_text_3250_ = l_Lean_FileMap_ofString(v_input_3238_);
if (v_normalizeLineEndings_3240_ == 0)
{
v_fst_3243_ = v_text_3250_;
v_snd_3244_ = v_endPos_3241_;
goto v___jp_3242_;
}
else
{
lean_object* v_source_3251_; lean_object* v_endPos_x27_3252_; lean_object* v___x_3253_; lean_object* v_text_3254_; lean_object* v___x_3255_; 
v_source_3251_ = lean_ctor_get(v_text_3250_, 0);
lean_inc_ref(v_source_3251_);
v_endPos_x27_3252_ = l_Lean_FileMap_toPosition(v_text_3250_, v_endPos_3241_);
lean_dec(v_endPos_3241_);
v___x_3253_ = l_String_crlfToLf(v_source_3251_);
lean_dec_ref(v_source_3251_);
v_text_3254_ = l_Lean_FileMap_ofString(v___x_3253_);
v___x_3255_ = l_Lean_FileMap_ofPosition(v_text_3254_, v_endPos_x27_3252_);
v_fst_3243_ = v_text_3254_;
v_snd_3244_ = v___x_3255_;
goto v___jp_3242_;
}
v___jp_3242_:
{
lean_object* v_source_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
v_source_3245_ = lean_ctor_get(v_fst_3243_, 0);
lean_inc_ref(v_source_3245_);
v___x_3246_ = lean_string_utf8_byte_size(v_source_3245_);
v___x_3247_ = lean_nat_dec_le(v_snd_3244_, v___x_3246_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; 
lean_dec(v_snd_3244_);
v___x_3248_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3248_, 0, v_source_3245_);
lean_ctor_set(v___x_3248_, 1, v_fileName_3239_);
lean_ctor_set(v___x_3248_, 2, v_fst_3243_);
lean_ctor_set(v___x_3248_, 3, v___x_3246_);
return v___x_3248_;
}
else
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3249_, 0, v_source_3245_);
lean_ctor_set(v___x_3249_, 1, v_fileName_3239_);
lean_ctor_set(v___x_3249_, 2, v_fst_3243_);
lean_ctor_set(v___x_3249_, 3, v_snd_3244_);
return v___x_3249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object* v_input_3256_, lean_object* v_fileName_3257_, lean_object* v_normalizeLineEndings_3258_, lean_object* v_endPos_3259_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3260_; lean_object* v_res_3261_; 
v_normalizeLineEndings_boxed_3260_ = lean_unbox(v_normalizeLineEndings_3258_);
v_res_3261_ = l_Lean_Parser_mkInputContext___redArg(v_input_3256_, v_fileName_3257_, v_normalizeLineEndings_boxed_3260_, v_endPos_3259_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object* v_input_3262_, lean_object* v_fileName_3263_, uint8_t v_normalizeLineEndings_3264_, lean_object* v_endPos_3265_, lean_object* v_endPos__valid_3266_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Lean_Parser_mkInputContext___redArg(v_input_3262_, v_fileName_3263_, v_normalizeLineEndings_3264_, v_endPos_3265_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object* v_input_3268_, lean_object* v_fileName_3269_, lean_object* v_normalizeLineEndings_3270_, lean_object* v_endPos_3271_, lean_object* v_endPos__valid_3272_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3273_; lean_object* v_res_3274_; 
v_normalizeLineEndings_boxed_3273_ = lean_unbox(v_normalizeLineEndings_3270_);
v_res_3274_ = l_Lean_Parser_mkInputContext(v_input_3268_, v_fileName_3269_, v_normalizeLineEndings_boxed_3273_, v_endPos_3271_, v_endPos__valid_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* v_input_3277_){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3278_ = l_Lean_Parser_SyntaxStack_empty;
v___x_3279_ = lean_unsigned_to_nat(0u);
v___x_3280_ = l_Lean_Parser_initCacheForInput(v_input_3277_);
v___x_3281_ = lean_box(0);
v___x_3282_ = ((lean_object*)(l_Lean_Parser_mkParserState___closed__0));
v___x_3283_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3278_);
lean_ctor_set(v___x_3283_, 1, v___x_3279_);
lean_ctor_set(v___x_3283_, 2, v___x_3279_);
lean_ctor_set(v___x_3283_, 3, v___x_3280_);
lean_ctor_set(v___x_3283_, 4, v___x_3281_);
lean_ctor_set(v___x_3283_, 5, v___x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* v_input_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Parser_mkParserState(v_input_3284_);
lean_dec_ref(v_input_3284_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* v_env_3288_, lean_object* v_catName_3289_, lean_object* v_input_3290_, lean_object* v_fileName_3291_){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v_p_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v_ictx_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v_s_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; uint8_t v___x_3308_; 
v___x_3292_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__0));
v___x_3293_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 1);
lean_closure_set(v___x_3293_, 0, v_catName_3289_);
v_p_3294_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_3294_, 0, v___x_3292_);
lean_closure_set(v_p_3294_, 1, v___x_3293_);
v___x_3295_ = 1;
v___x_3296_ = lean_string_utf8_byte_size(v_input_3290_);
lean_inc_ref(v_input_3290_);
v_ictx_3297_ = l_Lean_Parser_mkInputContext___redArg(v_input_3290_, v_fileName_3291_, v___x_3295_, v___x_3296_);
v___x_3298_ = l_Lean_Options_empty;
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_box(0);
lean_inc_ref(v_env_3288_);
v___x_3301_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3301_, 0, v_env_3288_);
lean_ctor_set(v___x_3301_, 1, v___x_3298_);
lean_ctor_set(v___x_3301_, 2, v___x_3299_);
lean_ctor_set(v___x_3301_, 3, v___x_3300_);
v___x_3302_ = l_Lean_Parser_getTokenTable(v_env_3288_);
v___x_3303_ = l_Lean_Parser_mkParserState(v_input_3290_);
lean_dec_ref(v_input_3290_);
lean_inc_ref(v_ictx_3297_);
v_s_3304_ = l_Lean_Parser_ParserFn_run(v_p_3294_, v_ictx_3297_, v___x_3301_, v___x_3302_, v___x_3303_);
lean_inc_ref(v_s_3304_);
v___x_3305_ = l_Lean_Parser_ParserState_allErrors(v_s_3304_);
v___x_3306_ = lean_array_get_size(v___x_3305_);
lean_dec_ref(v___x_3305_);
v___x_3307_ = lean_unsigned_to_nat(0u);
v___x_3308_ = lean_nat_dec_eq(v___x_3306_, v___x_3307_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3297_, v_s_3304_);
v___x_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
return v___x_3310_;
}
else
{
lean_object* v_stxStack_3311_; lean_object* v_pos_3312_; uint8_t v___x_3313_; 
v_stxStack_3311_ = lean_ctor_get(v_s_3304_, 0);
lean_inc_ref(v_stxStack_3311_);
v_pos_3312_ = lean_ctor_get(v_s_3304_, 2);
lean_inc(v_pos_3312_);
v___x_3313_ = l_Lean_Parser_InputContext_atEnd(v_ictx_3297_, v_pos_3312_);
lean_dec(v_pos_3312_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
lean_dec_ref(v_stxStack_3311_);
v___x_3314_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__1));
v___x_3315_ = l_Lean_Parser_ParserState_mkError(v_s_3304_, v___x_3314_);
v___x_3316_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3297_, v___x_3315_);
v___x_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
return v___x_3317_;
}
else
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_dec_ref(v_s_3304_);
lean_dec_ref(v_ictx_3297_);
v___x_3318_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3311_);
lean_dec_ref(v_stxStack_3311_);
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
return v___x_3319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* v_addFnName_3320_, lean_object* v_catName_3321_, lean_object* v_declName_3322_, lean_object* v_prio_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v_val_3339_; lean_object* v___x_3340_; 
v___x_3327_ = lean_box(0);
v___x_3328_ = l_Lean_mkConst(v_addFnName_3320_, v___x_3327_);
v___x_3329_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_catName_3321_);
lean_inc_n(v_declName_3322_, 2);
v___x_3330_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3322_);
v___x_3331_ = l_Lean_mkConst(v_declName_3322_, v___x_3327_);
v___x_3332_ = l_Lean_mkRawNatLit(v_prio_3323_);
v___x_3333_ = lean_unsigned_to_nat(4u);
v___x_3334_ = lean_mk_empty_array_with_capacity(v___x_3333_);
v___x_3335_ = lean_array_push(v___x_3334_, v___x_3329_);
v___x_3336_ = lean_array_push(v___x_3335_, v___x_3330_);
v___x_3337_ = lean_array_push(v___x_3336_, v___x_3331_);
v___x_3338_ = lean_array_push(v___x_3337_, v___x_3332_);
v_val_3339_ = l_Lean_mkAppN(v___x_3328_, v___x_3338_);
lean_dec_ref(v___x_3338_);
v___x_3340_ = l_Lean_declareBuiltin(v_declName_3322_, v_val_3339_, v_a_3324_, v_a_3325_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object* v_addFnName_3341_, lean_object* v_catName_3342_, lean_object* v_declName_3343_, lean_object* v_prio_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3341_, v_catName_3342_, v_declName_3343_, v_prio_3344_, v_a_3345_, v_a_3346_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* v_catName_3354_, lean_object* v_declName_3355_, lean_object* v_prio_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = ((lean_object*)(l_Lean_Parser_declareLeadingBuiltinParser___closed__1));
v___x_3361_ = l_Lean_Parser_declareBuiltinParser(v___x_3360_, v_catName_3354_, v_declName_3355_, v_prio_3356_, v_a_3357_, v_a_3358_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object* v_catName_3362_, lean_object* v_declName_3363_, lean_object* v_prio_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3362_, v_declName_3363_, v_prio_3364_, v_a_3365_, v_a_3366_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* v_catName_3374_, lean_object* v_declName_3375_, lean_object* v_prio_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = ((lean_object*)(l_Lean_Parser_declareTrailingBuiltinParser___closed__1));
v___x_3381_ = l_Lean_Parser_declareBuiltinParser(v___x_3380_, v_catName_3374_, v_declName_3375_, v_prio_3376_, v_a_3377_, v_a_3378_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object* v_catName_3382_, lean_object* v_declName_3383_, lean_object* v_prio_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3382_, v_declName_3383_, v_prio_3384_, v_a_3385_, v_a_3386_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* v_args_3395_){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; uint8_t v___x_3398_; 
v___x_3396_ = l_Lean_Syntax_getNumArgs(v_args_3395_);
v___x_3397_ = lean_unsigned_to_nat(0u);
v___x_3398_ = lean_nat_dec_eq(v___x_3396_, v___x_3397_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; uint8_t v___x_3400_; 
v___x_3399_ = lean_unsigned_to_nat(1u);
v___x_3400_ = lean_nat_dec_eq(v___x_3396_, v___x_3399_);
lean_dec(v___x_3396_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; 
v___x_3401_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__1));
return v___x_3401_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = l_Lean_Syntax_getArg(v_args_3395_, v___x_3397_);
v___x_3403_ = l_Lean_Syntax_isNatLit_x3f(v___x_3402_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3404_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__2));
v___x_3405_ = l_Lean_Syntax_formatStx(v___x_3402_, v___x_3403_, v___x_3398_);
v___x_3406_ = l_Std_Format_defWidth;
v___x_3407_ = l_Std_Format_pretty(v___x_3405_, v___x_3406_, v___x_3397_, v___x_3397_);
v___x_3408_ = lean_string_append(v___x_3404_, v___x_3407_);
lean_dec_ref(v___x_3407_);
v___x_3409_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3410_ = lean_string_append(v___x_3408_, v___x_3409_);
v___x_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
return v___x_3411_;
}
else
{
lean_object* v_val_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec(v___x_3402_);
v_val_3412_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3403_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_val_3412_);
lean_dec(v___x_3403_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_val_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
}
else
{
lean_object* v___x_3420_; 
lean_dec(v___x_3396_);
v___x_3420_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__3));
return v___x_3420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* v_args_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_Parser_getParserPriority(v_args_3421_);
lean_dec(v_args_3421_);
return v_res_3422_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0));
v___x_3425_ = l_Lean_stringToMessageData(v___x_3424_);
return v___x_3425_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2));
v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
return v___x_3428_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3430_ = l_Lean_stringToMessageData(v___x_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object* v_name_3434_, uint8_t v_kind_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___y_3445_; 
v___x_3439_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1);
v___x_3440_ = l_Lean_MessageData_ofName(v_name_3434_);
v___x_3441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3439_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3);
v___x_3443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3441_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
switch(v_kind_3435_)
{
case 0:
{
lean_object* v___x_3452_; 
v___x_3452_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5));
v___y_3445_ = v___x_3452_;
goto v___jp_3444_;
}
case 1:
{
lean_object* v___x_3453_; 
v___x_3453_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6));
v___y_3445_ = v___x_3453_;
goto v___jp_3444_;
}
default: 
{
lean_object* v___x_3454_; 
v___x_3454_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7));
v___y_3445_ = v___x_3454_;
goto v___jp_3444_;
}
}
v___jp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
lean_inc_ref(v___y_3445_);
v___x_3446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___y_3445_);
v___x_3447_ = l_Lean_MessageData_ofFormat(v___x_3446_);
v___x_3448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3443_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___x_3449_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3448_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3450_, v___y_3436_, v___y_3437_);
return v___x_3451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object* v_name_3455_, lean_object* v_kind_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
uint8_t v_kind_boxed_3460_; lean_object* v_res_3461_; 
v_kind_boxed_3460_ = lean_unbox(v_kind_3456_);
v_res_3461_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3455_, v_kind_boxed_3460_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3462_, lean_object* v_msg_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
lean_object* v_fileName_3467_; lean_object* v_fileMap_3468_; lean_object* v_options_3469_; lean_object* v_currRecDepth_3470_; lean_object* v_maxRecDepth_3471_; lean_object* v_ref_3472_; lean_object* v_currNamespace_3473_; lean_object* v_openDecls_3474_; lean_object* v_initHeartbeats_3475_; lean_object* v_maxHeartbeats_3476_; lean_object* v_quotContext_3477_; lean_object* v_currMacroScope_3478_; uint8_t v_diag_3479_; lean_object* v_cancelTk_x3f_3480_; uint8_t v_suppressElabErrors_3481_; lean_object* v_inheritedTraceOptions_3482_; lean_object* v_ref_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_fileName_3467_ = lean_ctor_get(v___y_3464_, 0);
v_fileMap_3468_ = lean_ctor_get(v___y_3464_, 1);
v_options_3469_ = lean_ctor_get(v___y_3464_, 2);
v_currRecDepth_3470_ = lean_ctor_get(v___y_3464_, 3);
v_maxRecDepth_3471_ = lean_ctor_get(v___y_3464_, 4);
v_ref_3472_ = lean_ctor_get(v___y_3464_, 5);
v_currNamespace_3473_ = lean_ctor_get(v___y_3464_, 6);
v_openDecls_3474_ = lean_ctor_get(v___y_3464_, 7);
v_initHeartbeats_3475_ = lean_ctor_get(v___y_3464_, 8);
v_maxHeartbeats_3476_ = lean_ctor_get(v___y_3464_, 9);
v_quotContext_3477_ = lean_ctor_get(v___y_3464_, 10);
v_currMacroScope_3478_ = lean_ctor_get(v___y_3464_, 11);
v_diag_3479_ = lean_ctor_get_uint8(v___y_3464_, sizeof(void*)*14);
v_cancelTk_x3f_3480_ = lean_ctor_get(v___y_3464_, 12);
v_suppressElabErrors_3481_ = lean_ctor_get_uint8(v___y_3464_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3482_ = lean_ctor_get(v___y_3464_, 13);
v_ref_3483_ = l_Lean_replaceRef(v_ref_3462_, v_ref_3472_);
lean_inc_ref(v_inheritedTraceOptions_3482_);
lean_inc(v_cancelTk_x3f_3480_);
lean_inc(v_currMacroScope_3478_);
lean_inc(v_quotContext_3477_);
lean_inc(v_maxHeartbeats_3476_);
lean_inc(v_initHeartbeats_3475_);
lean_inc(v_openDecls_3474_);
lean_inc(v_currNamespace_3473_);
lean_inc(v_maxRecDepth_3471_);
lean_inc(v_currRecDepth_3470_);
lean_inc_ref(v_options_3469_);
lean_inc_ref(v_fileMap_3468_);
lean_inc_ref(v_fileName_3467_);
v___x_3484_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3484_, 0, v_fileName_3467_);
lean_ctor_set(v___x_3484_, 1, v_fileMap_3468_);
lean_ctor_set(v___x_3484_, 2, v_options_3469_);
lean_ctor_set(v___x_3484_, 3, v_currRecDepth_3470_);
lean_ctor_set(v___x_3484_, 4, v_maxRecDepth_3471_);
lean_ctor_set(v___x_3484_, 5, v_ref_3483_);
lean_ctor_set(v___x_3484_, 6, v_currNamespace_3473_);
lean_ctor_set(v___x_3484_, 7, v_openDecls_3474_);
lean_ctor_set(v___x_3484_, 8, v_initHeartbeats_3475_);
lean_ctor_set(v___x_3484_, 9, v_maxHeartbeats_3476_);
lean_ctor_set(v___x_3484_, 10, v_quotContext_3477_);
lean_ctor_set(v___x_3484_, 11, v_currMacroScope_3478_);
lean_ctor_set(v___x_3484_, 12, v_cancelTk_x3f_3480_);
lean_ctor_set(v___x_3484_, 13, v_inheritedTraceOptions_3482_);
lean_ctor_set_uint8(v___x_3484_, sizeof(void*)*14, v_diag_3479_);
lean_ctor_set_uint8(v___x_3484_, sizeof(void*)*14 + 1, v_suppressElabErrors_3481_);
v___x_3485_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_3463_, v___x_3484_, v___y_3465_);
lean_dec_ref_known(v___x_3484_, 14);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3486_, lean_object* v_msg_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3486_, v_msg_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v_ref_3486_);
return v_res_3491_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_3494_ = l_Lean_stringToMessageData(v___x_3493_);
return v___x_3494_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_3497_ = l_Lean_stringToMessageData(v___x_3496_);
return v___x_3497_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_3500_ = l_Lean_stringToMessageData(v___x_3499_);
return v___x_3500_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_3503_ = l_Lean_stringToMessageData(v___x_3502_);
return v___x_3503_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_3506_ = l_Lean_stringToMessageData(v___x_3505_);
return v___x_3506_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_3509_ = l_Lean_stringToMessageData(v___x_3508_);
return v___x_3509_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_3512_ = l_Lean_stringToMessageData(v___x_3511_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_3513_, lean_object* v_declHint_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; lean_object* v_env_3518_; uint8_t v___x_3519_; 
v___x_3517_ = lean_st_ref_get(v___y_3515_);
v_env_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc_ref(v_env_3518_);
lean_dec(v___x_3517_);
v___x_3519_ = l_Lean_Name_isAnonymous(v_declHint_3514_);
if (v___x_3519_ == 0)
{
uint8_t v_isExporting_3520_; 
v_isExporting_3520_ = lean_ctor_get_uint8(v_env_3518_, sizeof(void*)*8);
if (v_isExporting_3520_ == 0)
{
lean_object* v___x_3521_; 
lean_dec_ref(v_env_3518_);
lean_dec(v_declHint_3514_);
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v_msg_3513_);
return v___x_3521_;
}
else
{
lean_object* v___x_3522_; uint8_t v___x_3523_; 
lean_inc_ref(v_env_3518_);
v___x_3522_ = l_Lean_Environment_setExporting(v_env_3518_, v___x_3519_);
lean_inc(v_declHint_3514_);
lean_inc_ref(v___x_3522_);
v___x_3523_ = l_Lean_Environment_contains(v___x_3522_, v_declHint_3514_, v_isExporting_3520_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3524_; 
lean_dec_ref(v___x_3522_);
lean_dec_ref(v_env_3518_);
lean_dec(v_declHint_3514_);
v___x_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3524_, 0, v_msg_3513_);
return v___x_3524_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_c_3530_; lean_object* v___x_3531_; 
v___x_3525_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_3526_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_3527_ = l_Lean_Options_empty;
v___x_3528_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3522_);
lean_ctor_set(v___x_3528_, 1, v___x_3525_);
lean_ctor_set(v___x_3528_, 2, v___x_3526_);
lean_ctor_set(v___x_3528_, 3, v___x_3527_);
lean_inc(v_declHint_3514_);
v___x_3529_ = l_Lean_MessageData_ofConstName(v_declHint_3514_, v___x_3519_);
v_c_3530_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3530_, 0, v___x_3528_);
lean_ctor_set(v_c_3530_, 1, v___x_3529_);
v___x_3531_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3518_, v_declHint_3514_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
lean_dec_ref(v_env_3518_);
lean_dec(v_declHint_3514_);
v___x_3532_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
lean_ctor_set(v___x_3533_, 1, v_c_3530_);
v___x_3534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = l_Lean_MessageData_note(v___x_3535_);
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v_msg_3513_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
v___x_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
return v___x_3538_;
}
else
{
lean_object* v_val_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3574_; 
v_val_3539_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3541_ = v___x_3531_;
v_isShared_3542_ = v_isSharedCheck_3574_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_val_3539_);
lean_dec(v___x_3531_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3574_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v_mod_3546_; uint8_t v___x_3547_; 
v___x_3543_ = lean_box(0);
v___x_3544_ = l_Lean_Environment_header(v_env_3518_);
lean_dec_ref(v_env_3518_);
v___x_3545_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3544_);
v_mod_3546_ = lean_array_get(v___x_3543_, v___x_3545_, v_val_3539_);
lean_dec(v_val_3539_);
lean_dec_ref(v___x_3545_);
v___x_3547_ = l_Lean_isPrivateName(v_declHint_3514_);
lean_dec(v_declHint_3514_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3548_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v_c_3530_);
v___x_3550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_3551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3549_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = l_Lean_MessageData_ofName(v_mod_3546_);
v___x_3553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3551_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
v___x_3554_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3553_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
v___x_3556_ = l_Lean_MessageData_note(v___x_3555_);
v___x_3557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3557_, 0, v_msg_3513_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set_tag(v___x_3541_, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3557_);
v___x_3559_ = v___x_3541_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
else
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3561_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
lean_ctor_set(v___x_3562_, 1, v_c_3530_);
v___x_3563_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_3564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3562_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
v___x_3565_ = l_Lean_MessageData_ofName(v_mod_3546_);
v___x_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = l_Lean_MessageData_note(v___x_3568_);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_msg_3513_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set_tag(v___x_3541_, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3570_);
v___x_3572_ = v___x_3541_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3575_; 
lean_dec_ref(v_env_3518_);
lean_dec(v_declHint_3514_);
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v_msg_3513_);
return v___x_3575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_3576_, lean_object* v_declHint_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3576_, v_declHint_3577_, v___y_3578_);
lean_dec(v___y_3578_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_3581_, lean_object* v_declHint_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v___x_3586_; lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3596_; 
v___x_3586_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3581_, v_declHint_3582_, v___y_3584_);
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3589_ = v___x_3586_;
v_isShared_3590_ = v_isSharedCheck_3596_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3586_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3596_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3591_ = l_Lean_unknownIdentifierMessageTag;
v___x_3592_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
lean_ctor_set(v___x_3592_, 1, v_a_3587_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 0, v___x_3592_);
v___x_3594_ = v___x_3589_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_3597_, lean_object* v_declHint_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3597_, v_declHint_3598_, v___y_3599_, v___y_3600_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3603_, lean_object* v_msg_3604_, lean_object* v_declHint_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; lean_object* v_a_3610_; lean_object* v___x_3611_; 
v___x_3609_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3604_, v_declHint_3605_, v___y_3606_, v___y_3607_);
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref(v___x_3609_);
v___x_3611_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3603_, v_a_3610_, v___y_3606_, v___y_3607_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3612_, lean_object* v_msg_3613_, lean_object* v_declHint_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3612_, v_msg_3613_, v_declHint_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v_ref_3612_);
return v_res_3618_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_3620_ = l_Lean_stringToMessageData(v___x_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3621_, lean_object* v_constName_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v___x_3626_; uint8_t v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3626_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3627_ = 0;
lean_inc(v_constName_3622_);
v___x_3628_ = l_Lean_MessageData_ofConstName(v_constName_3622_, v___x_3627_);
v___x_3629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3626_);
lean_ctor_set(v___x_3629_, 1, v___x_3628_);
v___x_3630_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3629_);
lean_ctor_set(v___x_3631_, 1, v___x_3630_);
v___x_3632_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3621_, v___x_3631_, v_constName_3622_, v___y_3623_, v___y_3624_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3633_, lean_object* v_constName_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3633_, v_constName_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v_ref_3633_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object* v_constName_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v_ref_3643_; lean_object* v___x_3644_; 
v_ref_3643_ = lean_ctor_get(v___y_3640_, 5);
v___x_3644_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3643_, v_constName_3639_, v___y_3640_, v___y_3641_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3645_, v___y_3646_, v___y_3647_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object* v_constName_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; lean_object* v_env_3655_; uint8_t v___x_3656_; lean_object* v___x_3657_; 
v___x_3654_ = lean_st_ref_get(v___y_3652_);
v_env_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc_ref(v_env_3655_);
lean_dec(v___x_3654_);
v___x_3656_ = 0;
lean_inc(v_constName_3650_);
v___x_3657_ = l_Lean_Environment_find_x3f(v_env_3655_, v_constName_3650_, v___x_3656_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v___x_3658_; 
v___x_3658_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3650_, v___y_3651_, v___y_3652_);
return v___x_3658_;
}
else
{
lean_object* v_val_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec(v_constName_3650_);
v_val_3659_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3657_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_val_3659_);
lean_dec(v___x_3657_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
lean_ctor_set_tag(v___x_3661_, 0);
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_val_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object* v_constName_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
return v_res_3671_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1(void){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0));
v___x_3674_ = l_Lean_stringToMessageData(v___x_3673_);
return v___x_3674_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2));
v___x_3677_ = l_Lean_stringToMessageData(v___x_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* v_attrName_3678_, lean_object* v_catName_3679_, lean_object* v_declName_3680_, lean_object* v_stx_3681_, uint8_t v_kind_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___x_3706_; 
v___x_3706_ = l_Lean_Attribute_Builtin_getPrio(v_stx_3681_, v_a_3683_, v_a_3684_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___y_3709_; lean_object* v___y_3710_; uint8_t v___x_3738_; uint8_t v___x_3739_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3706_, 1);
v___x_3738_ = 0;
v___x_3739_ = l_Lean_instBEqAttributeKind_beq(v_kind_3682_, v___x_3738_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; 
lean_dec(v_a_3707_);
lean_dec(v_declName_3680_);
lean_dec(v_catName_3679_);
v___x_3740_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_attrName_3678_, v_kind_3682_, v_a_3683_, v_a_3684_);
return v___x_3740_;
}
else
{
lean_dec(v_attrName_3678_);
v___y_3709_ = v_a_3683_;
v___y_3710_ = v_a_3684_;
goto v___jp_3708_;
}
v___jp_3708_:
{
lean_object* v___x_3711_; 
lean_inc(v_declName_3680_);
v___x_3711_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_declName_3680_, v___y_3709_, v___y_3710_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3713_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3711_, 1);
v___x_3713_ = l_Lean_ConstantInfo_type(v_a_3712_);
if (lean_obj_tag(v___x_3713_) == 4)
{
lean_object* v_declName_3714_; 
v_declName_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_declName_3714_);
lean_dec_ref_known(v___x_3713_, 2);
if (lean_obj_tag(v_declName_3714_) == 1)
{
lean_object* v_pre_3715_; 
v_pre_3715_ = lean_ctor_get(v_declName_3714_, 0);
lean_inc(v_pre_3715_);
if (lean_obj_tag(v_pre_3715_) == 1)
{
lean_object* v_pre_3716_; 
v_pre_3716_ = lean_ctor_get(v_pre_3715_, 0);
lean_inc(v_pre_3716_);
if (lean_obj_tag(v_pre_3716_) == 1)
{
lean_object* v_pre_3717_; 
v_pre_3717_ = lean_ctor_get(v_pre_3716_, 0);
if (lean_obj_tag(v_pre_3717_) == 0)
{
lean_object* v_str_3718_; lean_object* v_str_3719_; lean_object* v_str_3720_; lean_object* v___x_3721_; uint8_t v___x_3722_; 
v_str_3718_ = lean_ctor_get(v_declName_3714_, 1);
lean_inc_ref(v_str_3718_);
lean_dec_ref_known(v_declName_3714_, 2);
v_str_3719_ = lean_ctor_get(v_pre_3715_, 1);
lean_inc_ref(v_str_3719_);
lean_dec_ref_known(v_pre_3715_, 2);
v_str_3720_ = lean_ctor_get(v_pre_3716_, 1);
lean_inc_ref(v_str_3720_);
lean_dec_ref_known(v_pre_3716_, 2);
v___x_3721_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3722_ = lean_string_dec_eq(v_str_3720_, v___x_3721_);
lean_dec_ref(v_str_3720_);
if (v___x_3722_ == 0)
{
lean_dec_ref(v_str_3719_);
lean_dec_ref(v_str_3718_);
lean_dec(v_a_3707_);
lean_dec(v_catName_3679_);
v___y_3693_ = v_a_3712_;
v___y_3694_ = v___y_3709_;
v___y_3695_ = v___y_3710_;
goto v___jp_3692_;
}
else
{
lean_object* v___x_3723_; uint8_t v___x_3724_; 
v___x_3723_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3724_ = lean_string_dec_eq(v_str_3719_, v___x_3723_);
lean_dec_ref(v_str_3719_);
if (v___x_3724_ == 0)
{
lean_dec_ref(v_str_3718_);
lean_dec(v_a_3707_);
lean_dec(v_catName_3679_);
v___y_3693_ = v_a_3712_;
v___y_3694_ = v___y_3709_;
v___y_3695_ = v___y_3710_;
goto v___jp_3692_;
}
else
{
lean_object* v___x_3725_; uint8_t v___x_3726_; 
v___x_3725_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_3726_ = lean_string_dec_eq(v_str_3718_, v___x_3725_);
if (v___x_3726_ == 0)
{
uint8_t v___x_3727_; 
v___x_3727_ = lean_string_dec_eq(v_str_3718_, v___x_3723_);
lean_dec_ref(v_str_3718_);
if (v___x_3727_ == 0)
{
lean_dec(v_a_3707_);
lean_dec(v_catName_3679_);
v___y_3693_ = v_a_3712_;
v___y_3694_ = v___y_3709_;
v___y_3695_ = v___y_3710_;
goto v___jp_3692_;
}
else
{
lean_object* v___x_3728_; 
lean_dec(v_a_3712_);
lean_inc(v_declName_3680_);
lean_inc(v_catName_3679_);
v___x_3728_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3679_, v_declName_3680_, v_a_3707_, v___y_3709_, v___y_3710_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_dec_ref_known(v___x_3728_, 1);
v___y_3687_ = v___y_3709_;
v___y_3688_ = v___y_3710_;
goto v___jp_3686_;
}
else
{
lean_dec(v_declName_3680_);
lean_dec(v_catName_3679_);
return v___x_3728_;
}
}
}
else
{
lean_object* v___x_3729_; 
lean_dec_ref(v_str_3718_);
lean_dec(v_a_3712_);
lean_inc(v_declName_3680_);
lean_inc(v_catName_3679_);
v___x_3729_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3679_, v_declName_3680_, v_a_3707_, v___y_3709_, v___y_3710_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_dec_ref_known(v___x_3729_, 1);
v___y_3687_ = v___y_3709_;
v___y_3688_ = v___y_3710_;
goto v___jp_3686_;
}
else
{
lean_dec(v_declName_3680_);
lean_dec(v_catName_3679_);
return v___x_3729_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3716_, 2);
lean_dec_ref_known(v_pre_3715_, 2);
lean_dec_ref_known(v_declName_3714_, 2);
lean_dec(v_a_3707_);
lean_dec(v_catName_3679_);
v___y_3693_ = v_a_3712_;
v___y_3694_ = v___y_3709_;
v___y_3695_ = v___y_3710_;
goto v___jp_3692_;
}
}
else
{
lean_dec(v_pre_3716_);
lean_dec_ref_known(v_pre_3715_, 2);
lean_dec_ref_known(v_declName_3714_, 2);
lean_dec(v_a_3707_);
lean_dec(v_catName_3679_);
v___y_3693_ = v_a_3712_;
v___y_3694_ = v___y_3709_;
v___y_3695_ = v___y_3710_;
goto v___jp_3692_;
}
}
else
{
lean_dec_ref_known(v_declName_3714_, 2);
lean_dec(v_pre_3715_);
lean_dec(v_a_3707_);
lean_dec(v_catName_3679_);
v___y_3693_ = v_a_3712_;
v___y_3694_ = v___y_3709_;
v___y_3695_ = v___y_3710_;
goto v___jp_3692_;
}
}
else
{
lean_dec(v_declName_3714_);
lean_dec(v_a_3707_);
lean_dec(v_catName_3679_);
v___y_3693_ = v_a_3712_;
v___y_3694_ = v___y_3709_;
v___y_3695_ = v___y_3710_;
goto v___jp_3692_;
}
}
else
{
lean_dec_ref(v___x_3713_);
lean_dec(v_a_3707_);
lean_dec(v_catName_3679_);
v___y_3693_ = v_a_3712_;
v___y_3694_ = v___y_3709_;
v___y_3695_ = v___y_3710_;
goto v___jp_3692_;
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec(v_a_3707_);
lean_dec(v_declName_3680_);
lean_dec(v_catName_3679_);
v_a_3730_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3711_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3711_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec(v_declName_3680_);
lean_dec(v_catName_3679_);
lean_dec(v_attrName_3678_);
v_a_3741_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3706_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3706_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
v___jp_3686_:
{
lean_object* v___x_3689_; 
lean_inc(v_declName_3680_);
v___x_3689_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_3680_, v___y_3687_, v___y_3688_);
if (lean_obj_tag(v___x_3689_) == 0)
{
uint8_t v___x_3690_; lean_object* v___x_3691_; 
lean_dec_ref_known(v___x_3689_, 1);
v___x_3690_ = 1;
v___x_3691_ = l_Lean_Parser_runParserAttributeHooks(v_catName_3679_, v_declName_3680_, v___x_3690_, v___y_3687_, v___y_3688_);
return v___x_3691_;
}
else
{
lean_dec(v_declName_3680_);
lean_dec(v_catName_3679_);
return v___x_3689_;
}
}
v___jp_3692_:
{
lean_object* v___x_3696_; uint8_t v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3696_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
v___x_3697_ = 0;
v___x_3698_ = l_Lean_MessageData_ofConstName(v_declName_3680_, v___x_3697_);
v___x_3699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3696_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
v___x_3700_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
v___x_3701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3699_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = l_Lean_ConstantInfo_type(v___y_3693_);
lean_dec_ref(v___y_3693_);
v___x_3703_ = l_Lean_indentExpr(v___x_3702_);
v___x_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3701_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3704_, v___y_3694_, v___y_3695_);
return v___x_3705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* v_attrName_3749_, lean_object* v_catName_3750_, lean_object* v_declName_3751_, lean_object* v_stx_3752_, lean_object* v_kind_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_){
_start:
{
uint8_t v_kind_boxed_3757_; lean_object* v_res_3758_; 
v_kind_boxed_3757_ = lean_unbox(v_kind_3753_);
v_res_3758_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3749_, v_catName_3750_, v_declName_3751_, v_stx_3752_, v_kind_boxed_3757_, v_a_3754_, v_a_3755_);
lean_dec(v_a_3755_);
lean_dec_ref(v_a_3754_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object* v_00_u03b1_3759_, lean_object* v_name_3760_, uint8_t v_kind_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3760_, v_kind_3761_, v___y_3762_, v___y_3763_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b1_3766_, lean_object* v_name_3767_, lean_object* v_kind_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
uint8_t v_kind_boxed_3772_; lean_object* v_res_3773_; 
v_kind_boxed_3772_ = lean_unbox(v_kind_3768_);
v_res_3773_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(v_00_u03b1_3766_, v_name_3767_, v_kind_boxed_3772_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object* v_00_u03b1_3774_, lean_object* v_constName_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3775_, v___y_3776_, v___y_3777_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3780_, lean_object* v_constName_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(v_00_u03b1_3780_, v_constName_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3786_, lean_object* v_ref_3787_, lean_object* v_constName_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v___x_3792_; 
v___x_3792_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3787_, v_constName_3788_, v___y_3789_, v___y_3790_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3793_, lean_object* v_ref_3794_, lean_object* v_constName_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(v_00_u03b1_3793_, v_ref_3794_, v_constName_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v_ref_3794_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3800_, lean_object* v_ref_3801_, lean_object* v_msg_3802_, lean_object* v_declHint_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v___x_3807_; 
v___x_3807_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3801_, v_msg_3802_, v_declHint_3803_, v___y_3804_, v___y_3805_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3808_, lean_object* v_ref_3809_, lean_object* v_msg_3810_, lean_object* v_declHint_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3808_, v_ref_3809_, v_msg_3810_, v_declHint_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v_ref_3809_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_3816_, lean_object* v_declHint_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3816_, v_declHint_3817_, v___y_3819_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_3822_, lean_object* v_declHint_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_3822_, v_declHint_3823_, v___y_3824_, v___y_3825_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3828_, lean_object* v_ref_3829_, lean_object* v_msg_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3829_, v_msg_3830_, v___y_3831_, v___y_3832_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3835_, lean_object* v_ref_3836_, lean_object* v_msg_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3835_, v_ref_3836_, v_msg_3837_, v___y_3838_, v___y_3839_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v_ref_3836_);
return v_res_3841_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2(void){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0));
v___x_3849_ = l_Lean_mkAtom(v___x_3848_);
return v___x_3849_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3850_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2);
v___x_3851_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3852_ = lean_array_push(v___x_3851_, v___x_3850_);
return v___x_3852_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7));
v___x_3862_ = l_Lean_mkAtom(v___x_3861_);
return v___x_3862_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3863_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8);
v___x_3864_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3865_ = lean_array_push(v___x_3864_, v___x_3863_);
return v___x_3865_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3866_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9);
v___x_3867_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6));
v___x_3868_ = lean_box(2);
v___x_3869_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
lean_ctor_set(v___x_3869_, 1, v___x_3867_);
lean_ctor_set(v___x_3869_, 2, v___x_3866_);
return v___x_3869_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3870_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10);
v___x_3871_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3);
v___x_3872_ = lean_array_push(v___x_3871_, v___x_3870_);
return v___x_3872_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3873_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11);
v___x_3874_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1));
v___x_3875_ = lean_box(2);
v___x_3876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
lean_ctor_set(v___x_3876_, 1, v___x_3874_);
lean_ctor_set(v___x_3876_, 2, v___x_3873_);
return v___x_3876_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3877_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12);
v___x_3878_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3879_ = lean_array_push(v___x_3878_, v___x_3877_);
return v___x_3879_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14(void){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3880_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13);
v___x_3881_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3882_ = lean_box(2);
v___x_3883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
lean_ctor_set(v___x_3883_, 1, v___x_3881_);
lean_ctor_set(v___x_3883_, 2, v___x_3880_);
return v___x_3883_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3884_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14);
v___x_3885_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3886_ = lean_array_push(v___x_3885_, v___x_3884_);
return v___x_3886_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3887_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15);
v___x_3888_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3889_ = lean_box(2);
v___x_3890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
lean_ctor_set(v___x_3890_, 1, v___x_3888_);
lean_ctor_set(v___x_3890_, 2, v___x_3887_);
return v___x_3890_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3891_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16);
v___x_3892_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3893_ = lean_array_push(v___x_3892_, v___x_3891_);
return v___x_3893_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3894_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17);
v___x_3895_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3896_ = lean_box(2);
v___x_3897_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
lean_ctor_set(v___x_3897_, 1, v___x_3895_);
lean_ctor_set(v___x_3897_, 2, v___x_3894_);
return v___x_3897_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object* v_attrName_3899_, lean_object* v_decl_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3904_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3905_ = l_Lean_MessageData_ofName(v_attrName_3899_);
v___x_3906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3904_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
v___x_3907_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3906_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
v___x_3909_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3908_, v___y_3901_, v___y_3902_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object* v_attrName_3910_, lean_object* v_decl_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_3910_, v_decl_3911_, v___y_3912_, v___y_3913_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v_decl_3911_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object* v_attrName_3916_, lean_object* v_catName_3917_, lean_object* v_declName_3918_, lean_object* v_stx_3919_, uint8_t v_kind_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
lean_object* v___x_3924_; 
v___x_3924_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3916_, v_catName_3917_, v_declName_3918_, v_stx_3919_, v_kind_3920_, v___y_3921_, v___y_3922_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object* v_attrName_3925_, lean_object* v_catName_3926_, lean_object* v_declName_3927_, lean_object* v_stx_3928_, lean_object* v_kind_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
uint8_t v_kind_boxed_3933_; lean_object* v_res_3934_; 
v_kind_boxed_3933_ = lean_unbox(v_kind_3929_);
v_res_3934_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_3925_, v_catName_3926_, v_declName_3927_, v_stx_3928_, v_kind_boxed_3933_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
return v_res_3934_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1(void){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__0));
v___x_3937_ = lean_mk_io_user_error(v___x_3936_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* v_attrName_3940_, lean_object* v_declName_3941_, uint8_t v_behavior_3942_, lean_object* v_ref_3943_){
_start:
{
if (lean_obj_tag(v_declName_3941_) == 1)
{
lean_object* v_pre_3948_; 
v_pre_3948_ = lean_ctor_get(v_declName_3941_, 0);
if (lean_obj_tag(v_pre_3948_) == 1)
{
lean_object* v_pre_3949_; 
v_pre_3949_ = lean_ctor_get(v_pre_3948_, 0);
if (lean_obj_tag(v_pre_3949_) == 1)
{
lean_object* v_pre_3950_; 
v_pre_3950_ = lean_ctor_get(v_pre_3949_, 0);
if (lean_obj_tag(v_pre_3950_) == 1)
{
lean_object* v_pre_3951_; 
v_pre_3951_ = lean_ctor_get(v_pre_3950_, 0);
if (lean_obj_tag(v_pre_3951_) == 0)
{
lean_object* v_str_3952_; lean_object* v_str_3953_; lean_object* v_str_3954_; lean_object* v_str_3955_; lean_object* v___x_3956_; uint8_t v___x_3957_; 
v_str_3952_ = lean_ctor_get(v_declName_3941_, 1);
v_str_3953_ = lean_ctor_get(v_pre_3948_, 1);
v_str_3954_ = lean_ctor_get(v_pre_3949_, 1);
v_str_3955_ = lean_ctor_get(v_pre_3950_, 1);
v___x_3956_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3957_ = lean_string_dec_eq(v_str_3955_, v___x_3956_);
if (v___x_3957_ == 0)
{
lean_dec_ref_known(v_declName_3941_, 2);
lean_dec(v_ref_3943_);
lean_dec(v_attrName_3940_);
goto v___jp_3945_;
}
else
{
lean_object* v___x_3958_; uint8_t v___x_3959_; 
v___x_3958_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3959_ = lean_string_dec_eq(v_str_3954_, v___x_3958_);
if (v___x_3959_ == 0)
{
lean_dec_ref_known(v_declName_3941_, 2);
lean_dec(v_ref_3943_);
lean_dec(v_attrName_3940_);
goto v___jp_3945_;
}
else
{
lean_object* v___x_3960_; uint8_t v___x_3961_; 
v___x_3960_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__2));
v___x_3961_ = lean_string_dec_eq(v_str_3953_, v___x_3960_);
if (v___x_3961_ == 0)
{
lean_dec_ref_known(v_declName_3941_, 2);
lean_dec(v_ref_3943_);
lean_dec(v_attrName_3940_);
goto v___jp_3945_;
}
else
{
lean_object* v___x_3962_; lean_object* v_catName_3963_; lean_object* v___x_3964_; 
v___x_3962_ = lean_box(0);
lean_inc_ref(v_str_3952_);
v_catName_3963_ = l_Lean_Name_str___override(v___x_3962_, v_str_3952_);
lean_inc(v_catName_3963_);
v___x_3964_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_3963_, v_declName_3941_, v_behavior_3942_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v___f_3965_; lean_object* v___f_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
lean_dec_ref_known(v___x_3964_, 1);
lean_inc_n(v_attrName_3940_, 2);
v___f_3965_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3965_, 0, v_attrName_3940_);
v___f_3966_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3966_, 0, v_attrName_3940_);
lean_closure_set(v___f_3966_, 1, v_catName_3963_);
v___x_3967_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__3));
v___x_3968_ = 1;
v___x_3969_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3969_, 0, v_ref_3943_);
lean_ctor_set(v___x_3969_, 1, v_attrName_3940_);
lean_ctor_set(v___x_3969_, 2, v___x_3967_);
lean_ctor_set_uint8(v___x_3969_, sizeof(void*)*3, v___x_3968_);
v___x_3970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
lean_ctor_set(v___x_3970_, 1, v___f_3966_);
lean_ctor_set(v___x_3970_, 2, v___f_3965_);
v___x_3971_ = l_Lean_registerBuiltinAttribute(v___x_3970_);
return v___x_3971_;
}
else
{
lean_dec(v_catName_3963_);
lean_dec(v_ref_3943_);
lean_dec(v_attrName_3940_);
return v___x_3964_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_declName_3941_, 2);
lean_dec(v_ref_3943_);
lean_dec(v_attrName_3940_);
goto v___jp_3945_;
}
}
else
{
lean_dec_ref_known(v_declName_3941_, 2);
lean_dec(v_ref_3943_);
lean_dec(v_attrName_3940_);
goto v___jp_3945_;
}
}
else
{
lean_dec_ref_known(v_declName_3941_, 2);
lean_dec(v_ref_3943_);
lean_dec(v_attrName_3940_);
goto v___jp_3945_;
}
}
else
{
lean_dec_ref_known(v_declName_3941_, 2);
lean_dec(v_ref_3943_);
lean_dec(v_attrName_3940_);
goto v___jp_3945_;
}
}
else
{
lean_dec(v_ref_3943_);
lean_dec(v_declName_3941_);
lean_dec(v_attrName_3940_);
goto v___jp_3945_;
}
v___jp_3945_:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3946_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___closed__1, &l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
v___x_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
return v___x_3947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* v_attrName_3972_, lean_object* v_declName_3973_, lean_object* v_behavior_3974_, lean_object* v_ref_3975_, lean_object* v_a_3976_){
_start:
{
uint8_t v_behavior_boxed_3977_; lean_object* v_res_3978_; 
v_behavior_boxed_3977_ = lean_unbox(v_behavior_3974_);
v_res_3978_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_3972_, v_declName_3973_, v_behavior_boxed_3977_, v_ref_3975_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object* v_kind_3979_, lean_object* v_x_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v___x_3984_; lean_object* v_env_3985_; lean_object* v_nextMacroScope_3986_; lean_object* v_ngen_3987_; lean_object* v_auxDeclNGen_3988_; lean_object* v_traceState_3989_; lean_object* v_messages_3990_; lean_object* v_infoState_3991_; lean_object* v_snapshotTasks_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4004_; 
v___x_3984_ = lean_st_ref_take(v___y_3982_);
v_env_3985_ = lean_ctor_get(v___x_3984_, 0);
v_nextMacroScope_3986_ = lean_ctor_get(v___x_3984_, 1);
v_ngen_3987_ = lean_ctor_get(v___x_3984_, 2);
v_auxDeclNGen_3988_ = lean_ctor_get(v___x_3984_, 3);
v_traceState_3989_ = lean_ctor_get(v___x_3984_, 4);
v_messages_3990_ = lean_ctor_get(v___x_3984_, 6);
v_infoState_3991_ = lean_ctor_get(v___x_3984_, 7);
v_snapshotTasks_3992_ = lean_ctor_get(v___x_3984_, 8);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4004_ == 0)
{
lean_object* v_unused_4005_; 
v_unused_4005_ = lean_ctor_get(v___x_3984_, 5);
lean_dec(v_unused_4005_);
v___x_3994_ = v___x_3984_;
v_isShared_3995_ = v_isSharedCheck_4004_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_snapshotTasks_3992_);
lean_inc(v_infoState_3991_);
lean_inc(v_messages_3990_);
lean_inc(v_traceState_3989_);
lean_inc(v_auxDeclNGen_3988_);
lean_inc(v_ngen_3987_);
lean_inc(v_nextMacroScope_3986_);
lean_inc(v_env_3985_);
lean_dec(v___x_3984_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4004_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3999_; 
v___x_3996_ = l_Lean_Parser_addSyntaxNodeKind(v_env_3985_, v_kind_3979_);
v___x_3997_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 5, v___x_3997_);
lean_ctor_set(v___x_3994_, 0, v___x_3996_);
v___x_3999_ = v___x_3994_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_3996_);
lean_ctor_set(v_reuseFailAlloc_4003_, 1, v_nextMacroScope_3986_);
lean_ctor_set(v_reuseFailAlloc_4003_, 2, v_ngen_3987_);
lean_ctor_set(v_reuseFailAlloc_4003_, 3, v_auxDeclNGen_3988_);
lean_ctor_set(v_reuseFailAlloc_4003_, 4, v_traceState_3989_);
lean_ctor_set(v_reuseFailAlloc_4003_, 5, v___x_3997_);
lean_ctor_set(v_reuseFailAlloc_4003_, 6, v_messages_3990_);
lean_ctor_set(v_reuseFailAlloc_4003_, 7, v_infoState_3991_);
lean_ctor_set(v_reuseFailAlloc_4003_, 8, v_snapshotTasks_3992_);
v___x_3999_ = v_reuseFailAlloc_4003_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4000_ = lean_st_ref_set(v___y_3982_, v___x_3999_);
v___x_4001_ = lean_box(0);
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
return v___x_4002_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object* v_kind_4006_, lean_object* v_x_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_4006_, v_x_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_4012_, lean_object* v_keys_4013_, lean_object* v_vals_4014_, lean_object* v_i_4015_, lean_object* v_acc_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v___x_4020_; uint8_t v___x_4021_; 
v___x_4020_ = lean_array_get_size(v_keys_4013_);
v___x_4021_ = lean_nat_dec_lt(v_i_4015_, v___x_4020_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4022_; 
lean_dec(v_i_4015_);
lean_dec_ref(v_f_4012_);
v___x_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4022_, 0, v_acc_4016_);
return v___x_4022_;
}
else
{
lean_object* v_k_4023_; lean_object* v_v_4024_; lean_object* v___x_4025_; 
v_k_4023_ = lean_array_fget_borrowed(v_keys_4013_, v_i_4015_);
v_v_4024_ = lean_array_fget_borrowed(v_vals_4014_, v_i_4015_);
lean_inc_ref(v_f_4012_);
lean_inc(v___y_4018_);
lean_inc_ref(v___y_4017_);
lean_inc(v_v_4024_);
lean_inc(v_k_4023_);
v___x_4025_ = lean_apply_6(v_f_4012_, v_acc_4016_, v_k_4023_, v_v_4024_, v___y_4017_, v___y_4018_, lean_box(0));
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_a_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v___x_4025_, 1);
v___x_4027_ = lean_unsigned_to_nat(1u);
v___x_4028_ = lean_nat_add(v_i_4015_, v___x_4027_);
lean_dec(v_i_4015_);
v_i_4015_ = v___x_4028_;
v_acc_4016_ = v_a_4026_;
goto _start;
}
else
{
lean_dec(v_i_4015_);
lean_dec_ref(v_f_4012_);
return v___x_4025_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_4030_, lean_object* v_keys_4031_, lean_object* v_vals_4032_, lean_object* v_i_4033_, lean_object* v_acc_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4030_, v_keys_4031_, v_vals_4032_, v_i_4033_, v_acc_4034_, v___y_4035_, v___y_4036_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec_ref(v_vals_4032_);
lean_dec_ref(v_keys_4031_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object* v_f_4039_, lean_object* v_x_4040_, lean_object* v_x_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
if (lean_obj_tag(v_x_4040_) == 0)
{
lean_object* v_es_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4065_; 
v_es_4045_ = lean_ctor_get(v_x_4040_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_x_4040_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4047_ = v_x_4040_;
v_isShared_4048_ = v_isSharedCheck_4065_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_es_4045_);
lean_dec(v_x_4040_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4065_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; 
v___x_4049_ = lean_unsigned_to_nat(0u);
v___x_4050_ = lean_array_get_size(v_es_4045_);
v___x_4051_ = lean_nat_dec_lt(v___x_4049_, v___x_4050_);
if (v___x_4051_ == 0)
{
lean_object* v___x_4053_; 
lean_dec_ref(v_es_4045_);
lean_dec_ref(v_f_4039_);
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 0, v_x_4041_);
v___x_4053_ = v___x_4047_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_x_4041_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
else
{
uint8_t v___x_4055_; 
v___x_4055_ = lean_nat_dec_le(v___x_4050_, v___x_4050_);
if (v___x_4055_ == 0)
{
if (v___x_4051_ == 0)
{
lean_object* v___x_4057_; 
lean_dec_ref(v_es_4045_);
lean_dec_ref(v_f_4039_);
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 0, v_x_4041_);
v___x_4057_ = v___x_4047_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_x_4041_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
else
{
size_t v___x_4059_; size_t v___x_4060_; lean_object* v___x_4061_; 
lean_del_object(v___x_4047_);
v___x_4059_ = ((size_t)0ULL);
v___x_4060_ = lean_usize_of_nat(v___x_4050_);
v___x_4061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4039_, v_es_4045_, v___x_4059_, v___x_4060_, v_x_4041_, v___y_4042_, v___y_4043_);
lean_dec_ref(v_es_4045_);
return v___x_4061_;
}
}
else
{
size_t v___x_4062_; size_t v___x_4063_; lean_object* v___x_4064_; 
lean_del_object(v___x_4047_);
v___x_4062_ = ((size_t)0ULL);
v___x_4063_ = lean_usize_of_nat(v___x_4050_);
v___x_4064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4039_, v_es_4045_, v___x_4062_, v___x_4063_, v_x_4041_, v___y_4042_, v___y_4043_);
lean_dec_ref(v_es_4045_);
return v___x_4064_;
}
}
}
}
else
{
lean_object* v_ks_4066_; lean_object* v_vs_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v_ks_4066_ = lean_ctor_get(v_x_4040_, 0);
lean_inc_ref(v_ks_4066_);
v_vs_4067_ = lean_ctor_get(v_x_4040_, 1);
lean_inc_ref(v_vs_4067_);
lean_dec_ref_known(v_x_4040_, 2);
v___x_4068_ = lean_unsigned_to_nat(0u);
v___x_4069_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4039_, v_ks_4066_, v_vs_4067_, v___x_4068_, v_x_4041_, v___y_4042_, v___y_4043_);
lean_dec_ref(v_vs_4067_);
lean_dec_ref(v_ks_4066_);
return v___x_4069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_4070_, lean_object* v_as_4071_, size_t v_i_4072_, size_t v_stop_4073_, lean_object* v_b_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v_a_4079_; lean_object* v___y_4084_; uint8_t v___x_4086_; 
v___x_4086_ = lean_usize_dec_eq(v_i_4072_, v_stop_4073_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4087_; 
v___x_4087_ = lean_array_uget_borrowed(v_as_4071_, v_i_4072_);
switch(lean_obj_tag(v___x_4087_))
{
case 0:
{
lean_object* v_key_4088_; lean_object* v_val_4089_; lean_object* v___x_4090_; 
v_key_4088_ = lean_ctor_get(v___x_4087_, 0);
v_val_4089_ = lean_ctor_get(v___x_4087_, 1);
lean_inc_ref(v_f_4070_);
lean_inc(v___y_4076_);
lean_inc_ref(v___y_4075_);
lean_inc(v_val_4089_);
lean_inc(v_key_4088_);
v___x_4090_ = lean_apply_6(v_f_4070_, v_b_4074_, v_key_4088_, v_val_4089_, v___y_4075_, v___y_4076_, lean_box(0));
v___y_4084_ = v___x_4090_;
goto v___jp_4083_;
}
case 1:
{
lean_object* v_node_4091_; lean_object* v___x_4092_; 
v_node_4091_ = lean_ctor_get(v___x_4087_, 0);
lean_inc(v_node_4091_);
lean_inc_ref(v_f_4070_);
v___x_4092_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4070_, v_node_4091_, v_b_4074_, v___y_4075_, v___y_4076_);
v___y_4084_ = v___x_4092_;
goto v___jp_4083_;
}
default: 
{
v_a_4079_ = v_b_4074_;
goto v___jp_4078_;
}
}
}
else
{
lean_object* v___x_4093_; 
lean_dec_ref(v_f_4070_);
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v_b_4074_);
return v___x_4093_;
}
v___jp_4078_:
{
size_t v___x_4080_; size_t v___x_4081_; 
v___x_4080_ = ((size_t)1ULL);
v___x_4081_ = lean_usize_add(v_i_4072_, v___x_4080_);
v_i_4072_ = v___x_4081_;
v_b_4074_ = v_a_4079_;
goto _start;
}
v___jp_4083_:
{
if (lean_obj_tag(v___y_4084_) == 0)
{
lean_object* v_a_4085_; 
v_a_4085_ = lean_ctor_get(v___y_4084_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v___y_4084_, 1);
v_a_4079_ = v_a_4085_;
goto v___jp_4078_;
}
else
{
lean_dec_ref(v_f_4070_);
return v___y_4084_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_4094_, lean_object* v_as_4095_, lean_object* v_i_4096_, lean_object* v_stop_4097_, lean_object* v_b_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
size_t v_i_boxed_4102_; size_t v_stop_boxed_4103_; lean_object* v_res_4104_; 
v_i_boxed_4102_ = lean_unbox_usize(v_i_4096_);
lean_dec(v_i_4096_);
v_stop_boxed_4103_ = lean_unbox_usize(v_stop_4097_);
lean_dec(v_stop_4097_);
v_res_4104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4094_, v_as_4095_, v_i_boxed_4102_, v_stop_boxed_4103_, v_b_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec_ref(v_as_4095_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_4105_, lean_object* v_x_4106_, lean_object* v_x_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4105_, v_x_4106_, v_x_4107_, v___y_4108_, v___y_4109_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object* v_f_4112_, lean_object* v_x_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4119_; 
lean_inc(v___y_4117_);
lean_inc_ref(v___y_4116_);
v___x_4119_ = lean_apply_5(v_f_4112_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, lean_box(0));
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object* v_f_4120_, lean_object* v_x_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4120_, v_x_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object* v_map_4128_, lean_object* v_f_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v___f_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___f_4133_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4133_, 0, v_f_4129_);
v___x_4134_ = lean_box(0);
v___x_4135_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v___f_4133_, v_map_4128_, v___x_4134_, v___y_4130_, v___y_4131_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object* v_map_4136_, lean_object* v_f_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4136_, v_f_4137_, v___y_4138_, v___y_4139_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
return v_res_4141_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4143_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0));
v___x_4144_ = l_Lean_stringToMessageData(v___x_4143_);
return v___x_4144_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4145_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_4146_ = l_Lean_stringToMessageData(v___x_4145_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t v_attrKind_4147_, lean_object* v_declName_4148_, lean_object* v_as_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
if (lean_obj_tag(v_as_4149_) == 0)
{
lean_object* v___x_4153_; lean_object* v___x_4154_; 
lean_dec(v_declName_4148_);
v___x_4153_ = lean_box(0);
v___x_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4153_);
return v___x_4154_;
}
else
{
lean_object* v_head_4155_; lean_object* v_tail_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4186_; 
v_head_4155_ = lean_ctor_get(v_as_4149_, 0);
v_tail_4156_ = lean_ctor_get(v_as_4149_, 1);
v_isSharedCheck_4186_ = !lean_is_exclusive(v_as_4149_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4158_ = v_as_4149_;
v_isShared_4159_ = v_isSharedCheck_4186_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_tail_4156_);
lean_inc(v_head_4155_);
lean_dec(v_as_4149_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4186_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___y_4161_; lean_object* v___x_4163_; 
v___x_4163_ = l_Lean_Parser_addToken(v_head_4155_, v_attrKind_4147_, v___y_4150_, v___y_4151_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_del_object(v___x_4158_);
v___y_4161_ = v___x_4163_;
goto v___jp_4160_;
}
else
{
lean_object* v_a_4164_; uint8_t v___y_4166_; uint8_t v___x_4184_; 
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_a_4164_);
v___x_4184_ = l_Lean_Exception_isInterrupt(v_a_4164_);
if (v___x_4184_ == 0)
{
uint8_t v___x_4185_; 
lean_inc(v_a_4164_);
v___x_4185_ = l_Lean_Exception_isRuntime(v_a_4164_);
v___y_4166_ = v___x_4185_;
goto v___jp_4165_;
}
else
{
v___y_4166_ = v___x_4184_;
goto v___jp_4165_;
}
v___jp_4165_:
{
if (v___y_4166_ == 0)
{
if (lean_obj_tag(v_a_4164_) == 0)
{
lean_object* v_msg_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4182_; 
lean_dec_ref_known(v___x_4163_, 1);
v_msg_4167_ = lean_ctor_get(v_a_4164_, 1);
v_isSharedCheck_4182_ = !lean_is_exclusive(v_a_4164_);
if (v_isSharedCheck_4182_ == 0)
{
lean_object* v_unused_4183_; 
v_unused_4183_ = lean_ctor_get(v_a_4164_, 0);
lean_dec(v_unused_4183_);
v___x_4169_ = v_a_4164_;
v_isShared_4170_ = v_isSharedCheck_4182_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_msg_4167_);
lean_dec(v_a_4164_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4182_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4174_; 
v___x_4171_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1);
lean_inc(v_declName_4148_);
v___x_4172_ = l_Lean_MessageData_ofConstName(v_declName_4148_, v___y_4166_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set_tag(v___x_4169_, 7);
lean_ctor_set(v___x_4169_, 1, v___x_4172_);
lean_ctor_set(v___x_4169_, 0, v___x_4171_);
v___x_4174_ = v___x_4169_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4171_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v___x_4172_);
v___x_4174_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
lean_object* v___x_4175_; lean_object* v___x_4177_; 
v___x_4175_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2);
if (v_isShared_4159_ == 0)
{
lean_ctor_set_tag(v___x_4158_, 7);
lean_ctor_set(v___x_4158_, 1, v___x_4175_);
lean_ctor_set(v___x_4158_, 0, v___x_4174_);
v___x_4177_ = v___x_4158_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4174_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v___x_4175_);
v___x_4177_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
lean_ctor_set(v___x_4178_, 1, v_msg_4167_);
v___x_4179_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4178_, v___y_4150_, v___y_4151_);
v___y_4161_ = v___x_4179_;
goto v___jp_4160_;
}
}
}
}
else
{
lean_dec(v_a_4164_);
lean_del_object(v___x_4158_);
v___y_4161_ = v___x_4163_;
goto v___jp_4160_;
}
}
else
{
lean_dec(v_a_4164_);
lean_del_object(v___x_4158_);
v___y_4161_ = v___x_4163_;
goto v___jp_4160_;
}
}
}
v___jp_4160_:
{
if (lean_obj_tag(v___y_4161_) == 0)
{
lean_dec_ref_known(v___y_4161_, 1);
v_as_4149_ = v_tail_4156_;
goto _start;
}
else
{
lean_dec(v_tail_4156_);
lean_dec(v_declName_4148_);
return v___y_4161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object* v_attrKind_4187_, lean_object* v_declName_4188_, lean_object* v_as_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
uint8_t v_attrKind_boxed_4193_; lean_object* v_res_4194_; 
v_attrKind_boxed_4193_ = lean_unbox(v_attrKind_4187_);
v_res_4194_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_boxed_4193_, v_declName_4188_, v_as_4189_, v___y_4190_, v___y_4191_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object* v_catName_4196_, lean_object* v_declName_4197_, lean_object* v_stx_4198_, uint8_t v_attrKind_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_){
_start:
{
lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___x_4208_; 
v___x_4208_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4198_, v_a_4200_, v_a_4201_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v_env_4212_; lean_object* v___x_4213_; lean_object* v_ext_4214_; lean_object* v_toEnvExtension_4215_; lean_object* v_asyncMode_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v_categories_4219_; lean_object* v_env_4220_; lean_object* v_options_4221_; lean_object* v_ref_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref_known(v___x_4208_, 1);
v___x_4210_ = lean_st_ref_get(v_a_4201_);
v___x_4211_ = lean_st_ref_get(v_a_4201_);
v_env_4212_ = lean_ctor_get(v___x_4210_, 0);
lean_inc_ref(v_env_4212_);
lean_dec(v___x_4210_);
v___x_4213_ = l_Lean_Parser_parserExtension;
v_ext_4214_ = lean_ctor_get(v___x_4213_, 1);
v_toEnvExtension_4215_ = lean_ctor_get(v_ext_4214_, 0);
v_asyncMode_4216_ = lean_ctor_get(v_toEnvExtension_4215_, 2);
v___x_4217_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4218_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4217_, v___x_4213_, v_env_4212_, v_asyncMode_4216_);
v_categories_4219_ = lean_ctor_get(v___x_4218_, 2);
lean_inc_ref_n(v_categories_4219_, 2);
lean_dec(v___x_4218_);
v_env_4220_ = lean_ctor_get(v___x_4211_, 0);
lean_inc_ref(v_env_4220_);
lean_dec(v___x_4211_);
v_options_4221_ = lean_ctor_get(v_a_4200_, 2);
v_ref_4222_ = lean_ctor_get(v_a_4200_, 5);
lean_inc_ref(v_options_4221_);
v___x_4223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4223_, 0, v_env_4220_);
lean_ctor_set(v___x_4223_, 1, v_options_4221_);
lean_inc(v_declName_4197_);
v___x_4224_ = l_Lean_Parser_mkParserOfConstant(v_categories_4219_, v_declName_4197_, v___x_4223_);
lean_dec_ref_known(v___x_4223_, 2);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v_snd_4226_; lean_object* v_info_4227_; lean_object* v_fst_4228_; lean_object* v_collectTokens_4229_; lean_object* v_collectKinds_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
lean_dec_ref_known(v___x_4224_, 1);
v_snd_4226_ = lean_ctor_get(v_a_4225_, 1);
lean_inc(v_snd_4226_);
v_info_4227_ = lean_ctor_get(v_snd_4226_, 0);
v_fst_4228_ = lean_ctor_get(v_a_4225_, 0);
lean_inc(v_fst_4228_);
lean_dec(v_a_4225_);
v_collectTokens_4229_ = lean_ctor_get(v_info_4227_, 0);
v_collectKinds_4230_ = lean_ctor_get(v_info_4227_, 1);
v___x_4231_ = lean_box(0);
lean_inc_ref(v_collectTokens_4229_);
v___x_4232_ = lean_apply_1(v_collectTokens_4229_, v___x_4231_);
lean_inc(v_declName_4197_);
v___x_4233_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4199_, v_declName_4197_, v___x_4232_, v_a_4200_, v_a_4201_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v___f_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
lean_dec_ref_known(v___x_4233_, 1);
v___f_4234_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0));
v___x_4235_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
lean_inc_ref(v_collectKinds_4230_);
v___x_4236_ = lean_apply_1(v_collectKinds_4230_, v___x_4235_);
v___x_4237_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v___x_4236_, v___f_4234_, v_a_4200_, v_a_4201_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v___x_4238_; uint8_t v___x_4239_; uint8_t v___x_4240_; lean_object* v___x_4241_; 
lean_dec_ref_known(v___x_4237_, 1);
lean_inc(v_a_4209_);
lean_inc(v_snd_4226_);
lean_inc_n(v_declName_4197_, 2);
lean_inc_n(v_catName_4196_, 2);
v___x_4238_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_4238_, 0, v_catName_4196_);
lean_ctor_set(v___x_4238_, 1, v_declName_4197_);
lean_ctor_set(v___x_4238_, 2, v_snd_4226_);
lean_ctor_set(v___x_4238_, 3, v_a_4209_);
v___x_4239_ = lean_unbox(v_fst_4228_);
lean_ctor_set_uint8(v___x_4238_, sizeof(void*)*4, v___x_4239_);
v___x_4240_ = lean_unbox(v_fst_4228_);
lean_dec(v_fst_4228_);
v___x_4241_ = l_Lean_Parser_addParser(v_categories_4219_, v_catName_4196_, v_declName_4197_, v___x_4240_, v_snd_4226_, v_a_4209_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4251_; 
lean_dec_ref_known(v___x_4238_, 4);
lean_dec(v_declName_4197_);
lean_dec(v_catName_4196_);
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4244_ = v___x_4241_;
v_isShared_4245_ = v_isSharedCheck_4251_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4241_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4251_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
lean_ctor_set_tag(v___x_4244_, 3);
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4248_ = l_Lean_MessageData_ofFormat(v___x_4247_);
v___x_4249_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4248_, v_a_4200_, v_a_4201_);
return v___x_4249_;
}
}
}
else
{
lean_object* v___x_4252_; 
lean_dec_ref_known(v___x_4241_, 1);
v___x_4252_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_4213_, v___x_4238_, v_attrKind_4199_, v_a_4200_, v_a_4201_);
lean_dec_ref(v___x_4252_);
v___y_4204_ = v_a_4200_;
v___y_4205_ = v_a_4201_;
goto v___jp_4203_;
}
}
else
{
lean_dec(v_fst_4228_);
lean_dec(v_snd_4226_);
lean_dec_ref(v_categories_4219_);
lean_dec(v_a_4209_);
lean_dec(v_declName_4197_);
lean_dec(v_catName_4196_);
return v___x_4237_;
}
}
else
{
lean_dec(v_fst_4228_);
lean_dec(v_snd_4226_);
lean_dec_ref(v_categories_4219_);
lean_dec(v_a_4209_);
lean_dec(v_declName_4197_);
lean_dec(v_catName_4196_);
return v___x_4233_;
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4264_; 
lean_dec_ref(v_categories_4219_);
lean_dec(v_a_4209_);
lean_dec(v_declName_4197_);
lean_dec(v_catName_4196_);
v_a_4253_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4255_ = v___x_4224_;
v_isShared_4256_ = v_isSharedCheck_4264_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4224_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4264_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4262_; 
v___x_4257_ = lean_io_error_to_string(v_a_4253_);
v___x_4258_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4257_);
v___x_4259_ = l_Lean_MessageData_ofFormat(v___x_4258_);
lean_inc(v_ref_4222_);
v___x_4260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4260_, 0, v_ref_4222_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v___x_4260_);
v___x_4262_ = v___x_4255_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_dec(v_declName_4197_);
lean_dec(v_catName_4196_);
v_a_4265_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4208_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4208_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
v___jp_4203_:
{
uint8_t v___x_4206_; lean_object* v___x_4207_; 
v___x_4206_ = 0;
v___x_4207_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4196_, v_declName_4197_, v___x_4206_, v___y_4204_, v___y_4205_);
return v___x_4207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object* v_catName_4273_, lean_object* v_declName_4274_, lean_object* v_stx_4275_, lean_object* v_attrKind_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_){
_start:
{
uint8_t v_attrKind_boxed_4280_; lean_object* v_res_4281_; 
v_attrKind_boxed_4280_ = lean_unbox(v_attrKind_4276_);
v_res_4281_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4273_, v_declName_4274_, v_stx_4275_, v_attrKind_boxed_4280_, v_a_4277_, v_a_4278_);
lean_dec(v_a_4278_);
lean_dec_ref(v_a_4277_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* v___attrName_4282_, lean_object* v_catName_4283_, lean_object* v_declName_4284_, lean_object* v_stx_4285_, uint8_t v_attrKind_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4283_, v_declName_4284_, v_stx_4285_, v_attrKind_4286_, v_a_4287_, v_a_4288_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* v___attrName_4291_, lean_object* v_catName_4292_, lean_object* v_declName_4293_, lean_object* v_stx_4294_, lean_object* v_attrKind_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_){
_start:
{
uint8_t v_attrKind_boxed_4299_; lean_object* v_res_4300_; 
v_attrKind_boxed_4299_ = lean_unbox(v_attrKind_4295_);
v_res_4300_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4291_, v_catName_4292_, v_declName_4293_, v_stx_4294_, v_attrKind_boxed_4299_, v_a_4296_, v_a_4297_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec(v___attrName_4291_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object* v_00_u03b2_4301_, lean_object* v_map_4302_, lean_object* v_f_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v___x_4307_; 
v___x_4307_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4302_, v_f_4303_, v___y_4304_, v___y_4305_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b2_4308_, lean_object* v_map_4309_, lean_object* v_f_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(v_00_u03b2_4308_, v_map_4309_, v_f_4310_, v___y_4311_, v___y_4312_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object* v_map_4315_, lean_object* v_f_4316_, lean_object* v_init_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4316_, v_map_4315_, v_init_4317_, v___y_4318_, v___y_4319_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object* v_map_4322_, lean_object* v_f_4323_, lean_object* v_init_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
lean_object* v_res_4328_; 
v_res_4328_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4322_, v_f_4323_, v_init_4324_, v___y_4325_, v___y_4326_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object* v_00_u03c3_4329_, lean_object* v_00_u03b2_4330_, lean_object* v_map_4331_, lean_object* v_f_4332_, lean_object* v_init_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; 
v___x_4337_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4332_, v_map_4331_, v_init_4333_, v___y_4334_, v___y_4335_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object* v_00_u03c3_4338_, lean_object* v_00_u03b2_4339_, lean_object* v_map_4340_, lean_object* v_f_4341_, lean_object* v_init_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(v_00_u03c3_4338_, v_00_u03b2_4339_, v_map_4340_, v_f_4341_, v_init_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_4347_, lean_object* v_00_u03b1_4348_, lean_object* v_00_u03b2_4349_, lean_object* v_f_4350_, lean_object* v_x_4351_, lean_object* v_x_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4350_, v_x_4351_, v_x_4352_, v___y_4353_, v___y_4354_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03c3_4357_, lean_object* v_00_u03b1_4358_, lean_object* v_00_u03b2_4359_, lean_object* v_f_4360_, lean_object* v_x_4361_, lean_object* v_x_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(v_00_u03c3_4357_, v_00_u03b1_4358_, v_00_u03b2_4359_, v_f_4360_, v_x_4361_, v_x_4362_, v___y_4363_, v___y_4364_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4367_, lean_object* v_00_u03b2_4368_, lean_object* v_00_u03c3_4369_, lean_object* v_f_4370_, lean_object* v_as_4371_, size_t v_i_4372_, size_t v_stop_4373_, lean_object* v_b_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v___x_4378_; 
v___x_4378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4370_, v_as_4371_, v_i_4372_, v_stop_4373_, v_b_4374_, v___y_4375_, v___y_4376_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4379_, lean_object* v_00_u03b2_4380_, lean_object* v_00_u03c3_4381_, lean_object* v_f_4382_, lean_object* v_as_4383_, lean_object* v_i_4384_, lean_object* v_stop_4385_, lean_object* v_b_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
size_t v_i_boxed_4390_; size_t v_stop_boxed_4391_; lean_object* v_res_4392_; 
v_i_boxed_4390_ = lean_unbox_usize(v_i_4384_);
lean_dec(v_i_4384_);
v_stop_boxed_4391_ = lean_unbox_usize(v_stop_4385_);
lean_dec(v_stop_4385_);
v_res_4392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4379_, v_00_u03b2_4380_, v_00_u03c3_4381_, v_f_4382_, v_as_4383_, v_i_boxed_4390_, v_stop_boxed_4391_, v_b_4386_, v___y_4387_, v___y_4388_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
lean_dec_ref(v_as_4383_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_4393_, lean_object* v_00_u03b1_4394_, lean_object* v_00_u03b2_4395_, lean_object* v_f_4396_, lean_object* v_keys_4397_, lean_object* v_vals_4398_, lean_object* v_heq_4399_, lean_object* v_i_4400_, lean_object* v_acc_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v___x_4405_; 
v___x_4405_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4396_, v_keys_4397_, v_vals_4398_, v_i_4400_, v_acc_4401_, v___y_4402_, v___y_4403_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_4406_, lean_object* v_00_u03b1_4407_, lean_object* v_00_u03b2_4408_, lean_object* v_f_4409_, lean_object* v_keys_4410_, lean_object* v_vals_4411_, lean_object* v_heq_4412_, lean_object* v_i_4413_, lean_object* v_acc_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4406_, v_00_u03b1_4407_, v_00_u03b2_4408_, v_f_4409_, v_keys_4410_, v_vals_4411_, v_heq_4412_, v_i_4413_, v_acc_4414_, v___y_4415_, v___y_4416_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec_ref(v_vals_4411_);
lean_dec_ref(v_keys_4410_);
return v_res_4418_;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___auto__1(void){
_start:
{
lean_object* v___x_4419_; 
v___x_4419_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object* v_catName_4420_, lean_object* v_declName_4421_, lean_object* v_stx_4422_, uint8_t v_attrKind_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4420_, v_declName_4421_, v_stx_4422_, v_attrKind_4423_, v___y_4424_, v___y_4425_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object* v_catName_4428_, lean_object* v_declName_4429_, lean_object* v_stx_4430_, lean_object* v_attrKind_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
uint8_t v_attrKind_boxed_4435_; lean_object* v_res_4436_; 
v_attrKind_boxed_4435_ = lean_unbox(v_attrKind_4431_);
v_res_4436_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4428_, v_declName_4429_, v_stx_4430_, v_attrKind_boxed_4435_, v___y_4432_, v___y_4433_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* v_attrName_4438_, lean_object* v_catName_4439_, lean_object* v_ref_4440_){
_start:
{
lean_object* v___f_4441_; lean_object* v___f_4442_; lean_object* v___x_4443_; uint8_t v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___f_4441_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4441_, 0, v_catName_4439_);
lean_inc(v_attrName_4438_);
v___f_4442_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4442_, 0, v_attrName_4438_);
v___x_4443_ = ((lean_object*)(l_Lean_Parser_mkParserAttributeImpl___closed__0));
v___x_4444_ = 1;
v___x_4445_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4445_, 0, v_ref_4440_);
lean_ctor_set(v___x_4445_, 1, v_attrName_4438_);
lean_ctor_set(v___x_4445_, 2, v___x_4443_);
lean_ctor_set_uint8(v___x_4445_, sizeof(void*)*3, v___x_4444_);
v___x_4446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4445_);
lean_ctor_set(v___x_4446_, 1, v___f_4441_);
lean_ctor_set(v___x_4446_, 2, v___f_4442_);
return v___x_4446_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4447_; 
v___x_4447_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* v_attrName_4448_, lean_object* v_catName_4449_, lean_object* v_ref_4450_){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4452_ = l_Lean_Parser_mkParserAttributeImpl(v_attrName_4448_, v_catName_4449_, v_ref_4450_);
v___x_4453_ = l_Lean_registerBuiltinAttribute(v___x_4452_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object* v_attrName_4454_, lean_object* v_catName_4455_, lean_object* v_ref_4456_, lean_object* v_a_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4454_, v_catName_4455_, v_ref_4456_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object* v_ref_4462_, lean_object* v_args_4463_){
_start:
{
if (lean_obj_tag(v_args_4463_) == 1)
{
lean_object* v_head_4466_; 
v_head_4466_ = lean_ctor_get(v_args_4463_, 0);
lean_inc(v_head_4466_);
if (lean_obj_tag(v_head_4466_) == 2)
{
lean_object* v_tail_4467_; 
v_tail_4467_ = lean_ctor_get(v_args_4463_, 1);
lean_inc(v_tail_4467_);
lean_dec_ref_known(v_args_4463_, 2);
if (lean_obj_tag(v_tail_4467_) == 1)
{
lean_object* v_head_4468_; 
v_head_4468_ = lean_ctor_get(v_tail_4467_, 0);
lean_inc(v_head_4468_);
if (lean_obj_tag(v_head_4468_) == 2)
{
lean_object* v_tail_4469_; 
v_tail_4469_ = lean_ctor_get(v_tail_4467_, 1);
lean_inc(v_tail_4469_);
lean_dec_ref_known(v_tail_4467_, 2);
if (lean_obj_tag(v_tail_4469_) == 0)
{
lean_object* v_v_4470_; lean_object* v_v_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4479_; 
v_v_4470_ = lean_ctor_get(v_head_4466_, 0);
lean_inc(v_v_4470_);
lean_dec_ref_known(v_head_4466_, 1);
v_v_4471_ = lean_ctor_get(v_head_4468_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v_head_4468_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4473_ = v_head_4468_;
v_isShared_4474_ = v_isSharedCheck_4479_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_v_4471_);
lean_dec(v_head_4468_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4479_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4475_; lean_object* v___x_4477_; 
v___x_4475_ = l_Lean_Parser_mkParserAttributeImpl(v_v_4470_, v_v_4471_, v_ref_4462_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set_tag(v___x_4473_, 1);
lean_ctor_set(v___x_4473_, 0, v___x_4475_);
v___x_4477_ = v___x_4473_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4475_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
else
{
lean_dec_ref_known(v_head_4468_, 1);
lean_dec(v_tail_4469_);
lean_dec_ref_known(v_head_4466_, 1);
lean_dec(v_ref_4462_);
goto v___jp_4464_;
}
}
else
{
lean_dec(v_head_4468_);
lean_dec_ref_known(v_tail_4467_, 2);
lean_dec_ref_known(v_head_4466_, 1);
lean_dec(v_ref_4462_);
goto v___jp_4464_;
}
}
else
{
lean_dec(v_tail_4467_);
lean_dec_ref_known(v_head_4466_, 1);
lean_dec(v_ref_4462_);
goto v___jp_4464_;
}
}
else
{
lean_dec(v_head_4466_);
lean_dec_ref_known(v_args_4463_, 2);
lean_dec(v_ref_4462_);
goto v___jp_4464_;
}
}
else
{
lean_dec(v_args_4463_);
lean_dec(v_ref_4462_);
goto v___jp_4464_;
}
v___jp_4464_:
{
lean_object* v___x_4465_; 
v___x_4465_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
return v___x_4465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___f_4485_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4486_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4487_ = l_Lean_registerAttributeImplBuilder(v___x_4486_, v___f_4485_);
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object* v_a_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
return v_res_4489_;
}
}
static lean_object* _init_l_Lean_Parser_registerParserCategory___auto__1(void){
_start:
{
lean_object* v___x_4490_; 
v___x_4490_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object* v_env_4491_, lean_object* v_attrName_4492_, lean_object* v_catName_4493_, uint8_t v_behavior_4494_, lean_object* v_ref_4495_){
_start:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
lean_inc(v_ref_4495_);
lean_inc(v_catName_4493_);
v___x_4497_ = l_Lean_Parser_addParserCategory(v_env_4491_, v_catName_4493_, v_ref_4495_, v_behavior_4494_);
v___x_4498_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_4497_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4512_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4501_ = v___x_4498_;
v_isShared_4502_ = v_isSharedCheck_4512_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_a_4499_);
lean_dec(v___x_4498_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4512_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4503_; lean_object* v___x_4505_; 
v___x_4503_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
if (v_isShared_4502_ == 0)
{
lean_ctor_set_tag(v___x_4501_, 2);
lean_ctor_set(v___x_4501_, 0, v_attrName_4492_);
v___x_4505_ = v___x_4501_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_attrName_4492_);
v___x_4505_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4506_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4506_, 0, v_catName_4493_);
v___x_4507_ = lean_box(0);
v___x_4508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4506_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
v___x_4509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4505_);
lean_ctor_set(v___x_4509_, 1, v___x_4508_);
v___x_4510_ = l_Lean_registerAttributeOfBuilder(v_a_4499_, v___x_4503_, v_ref_4495_, v___x_4509_);
return v___x_4510_;
}
}
}
else
{
lean_dec(v_ref_4495_);
lean_dec(v_catName_4493_);
lean_dec(v_attrName_4492_);
return v___x_4498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* v_env_4513_, lean_object* v_attrName_4514_, lean_object* v_catName_4515_, lean_object* v_behavior_4516_, lean_object* v_ref_4517_, lean_object* v_a_4518_){
_start:
{
uint8_t v_behavior_boxed_4519_; lean_object* v_res_4520_; 
v_behavior_boxed_4519_ = lean_unbox(v_behavior_4516_);
v_res_4520_ = l_Lean_Parser_registerParserCategory(v_env_4513_, v_attrName_4514_, v_catName_4515_, v_behavior_boxed_4519_, v_ref_4517_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; uint8_t v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4543_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4544_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4545_ = 0;
v___x_4546_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4547_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4543_, v___x_4544_, v___x_4545_, v___x_4546_);
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object* v_a_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
return v_res_4549_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4555_ = lean_unsigned_to_nat(3431364690u);
v___x_4556_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4557_ = l_Lean_Name_num___override(v___x_4556_, v___x_4555_);
return v___x_4557_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4558_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4559_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4560_ = l_Lean_Name_str___override(v___x_4559_, v___x_4558_);
return v___x_4560_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4561_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4562_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4563_ = l_Lean_Name_str___override(v___x_4562_, v___x_4561_);
return v___x_4563_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4564_ = lean_unsigned_to_nat(2u);
v___x_4565_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4566_ = l_Lean_Name_num___override(v___x_4565_, v___x_4564_);
return v___x_4566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4568_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4569_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4570_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4571_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4568_, v___x_4569_, v___x_4570_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object* v_a_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
return v_res_4573_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4583_ = lean_unsigned_to_nat(2342493449u);
v___x_4584_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4585_ = l_Lean_Name_num___override(v___x_4584_, v___x_4583_);
return v___x_4585_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4586_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4587_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4588_ = l_Lean_Name_str___override(v___x_4587_, v___x_4586_);
return v___x_4588_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4589_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4590_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4591_ = l_Lean_Name_str___override(v___x_4590_, v___x_4589_);
return v___x_4591_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4592_ = lean_unsigned_to_nat(2u);
v___x_4593_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4594_ = l_Lean_Name_num___override(v___x_4593_, v___x_4592_);
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; uint8_t v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4596_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4597_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4598_ = 0;
v___x_4599_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4600_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4596_, v___x_4597_, v___x_4598_, v___x_4599_);
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object* v_a_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
return v_res_4602_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4608_ = lean_unsigned_to_nat(3226070615u);
v___x_4609_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4610_ = l_Lean_Name_num___override(v___x_4609_, v___x_4608_);
return v___x_4610_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___x_4611_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4612_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4613_ = l_Lean_Name_str___override(v___x_4612_, v___x_4611_);
return v___x_4613_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4614_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4615_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4616_ = l_Lean_Name_str___override(v___x_4615_, v___x_4614_);
return v___x_4616_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4617_ = lean_unsigned_to_nat(2u);
v___x_4618_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4619_ = l_Lean_Name_num___override(v___x_4618_, v___x_4617_);
return v___x_4619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4621_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4622_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4623_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4624_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4621_, v___x_4622_, v___x_4623_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object* v_a_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* v_rbp_4627_){
_start:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4628_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4629_ = l_Lean_Parser_categoryParser(v___x_4628_, v_rbp_4627_);
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t v_addOpenSimple_4630_, lean_object* v_x_4631_, lean_object* v_x_4632_){
_start:
{
if (lean_obj_tag(v_x_4632_) == 0)
{
return v_x_4631_;
}
else
{
lean_object* v_head_4633_; lean_object* v_tail_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4657_; 
v_head_4633_ = lean_ctor_get(v_x_4632_, 0);
v_tail_4634_ = lean_ctor_get(v_x_4632_, 1);
v_isSharedCheck_4657_ = !lean_is_exclusive(v_x_4632_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4636_ = v_x_4632_;
v_isShared_4637_ = v_isSharedCheck_4657_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_tail_4634_);
lean_inc(v_head_4633_);
lean_dec(v_x_4632_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4657_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v_fst_4638_; lean_object* v_snd_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4656_; 
v_fst_4638_ = lean_ctor_get(v_x_4631_, 0);
v_snd_4639_ = lean_ctor_get(v_x_4631_, 1);
v_isSharedCheck_4656_ = !lean_is_exclusive(v_x_4631_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4641_ = v_x_4631_;
v_isShared_4642_ = v_isSharedCheck_4656_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_snd_4639_);
lean_inc(v_fst_4638_);
lean_dec(v_x_4631_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4656_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___y_4644_; 
if (v_addOpenSimple_4630_ == 0)
{
lean_del_object(v___x_4636_);
v___y_4644_ = v_snd_4639_;
goto v___jp_4643_;
}
else
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4654_; 
v___x_4651_ = lean_box(0);
lean_inc(v_head_4633_);
v___x_4652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4652_, 0, v_head_4633_);
lean_ctor_set(v___x_4652_, 1, v___x_4651_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set(v___x_4636_, 1, v_snd_4639_);
lean_ctor_set(v___x_4636_, 0, v___x_4652_);
v___x_4654_ = v___x_4636_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4655_, 1, v_snd_4639_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
v___y_4644_ = v___x_4654_;
goto v___jp_4643_;
}
}
v___jp_4643_:
{
lean_object* v___x_4645_; lean_object* v_env_4646_; lean_object* v___x_4648_; 
v___x_4645_ = l_Lean_Parser_parserExtension;
v_env_4646_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v___x_4645_, v_fst_4638_, v_head_4633_);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 1, v___y_4644_);
lean_ctor_set(v___x_4641_, 0, v_env_4646_);
v___x_4648_ = v___x_4641_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_env_4646_);
lean_ctor_set(v_reuseFailAlloc_4650_, 1, v___y_4644_);
v___x_4648_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
v_x_4631_ = v___x_4648_;
v_x_4632_ = v_tail_4634_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object* v_addOpenSimple_4658_, lean_object* v_x_4659_, lean_object* v_x_4660_){
_start:
{
uint8_t v_addOpenSimple_boxed_4661_; lean_object* v_res_4662_; 
v_addOpenSimple_boxed_4661_ = lean_unbox(v_addOpenSimple_4658_);
v_res_4662_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_boxed_4661_, v_x_4659_, v_x_4660_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t v_addOpenSimple_4663_, lean_object* v_as_4664_, size_t v_i_4665_, size_t v_stop_4666_, lean_object* v_b_4667_){
_start:
{
uint8_t v___x_4668_; 
v___x_4668_ = lean_usize_dec_eq(v_i_4665_, v_stop_4666_);
if (v___x_4668_ == 0)
{
lean_object* v_toParserModuleContext_4669_; lean_object* v_toInputContext_4670_; lean_object* v_toCacheableParserContext_4671_; lean_object* v_tokens_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4699_; 
v_toParserModuleContext_4669_ = lean_ctor_get(v_b_4667_, 1);
v_toInputContext_4670_ = lean_ctor_get(v_b_4667_, 0);
v_toCacheableParserContext_4671_ = lean_ctor_get(v_b_4667_, 2);
v_tokens_4672_ = lean_ctor_get(v_b_4667_, 3);
v_isSharedCheck_4699_ = !lean_is_exclusive(v_b_4667_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4674_ = v_b_4667_;
v_isShared_4675_ = v_isSharedCheck_4699_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_tokens_4672_);
lean_inc(v_toCacheableParserContext_4671_);
lean_inc(v_toParserModuleContext_4669_);
lean_inc(v_toInputContext_4670_);
lean_dec(v_b_4667_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4699_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v_env_4676_; lean_object* v_options_4677_; lean_object* v_currNamespace_4678_; lean_object* v_openDecls_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4698_; 
v_env_4676_ = lean_ctor_get(v_toParserModuleContext_4669_, 0);
v_options_4677_ = lean_ctor_get(v_toParserModuleContext_4669_, 1);
v_currNamespace_4678_ = lean_ctor_get(v_toParserModuleContext_4669_, 2);
v_openDecls_4679_ = lean_ctor_get(v_toParserModuleContext_4669_, 3);
v_isSharedCheck_4698_ = !lean_is_exclusive(v_toParserModuleContext_4669_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4681_ = v_toParserModuleContext_4669_;
v_isShared_4682_ = v_isSharedCheck_4698_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_openDecls_4679_);
lean_inc(v_currNamespace_4678_);
lean_inc(v_options_4677_);
lean_inc(v_env_4676_);
lean_dec(v_toParserModuleContext_4669_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4698_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4683_; lean_object* v_nss_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v_fst_4687_; lean_object* v_snd_4688_; lean_object* v___x_4690_; 
v___x_4683_ = lean_array_uget_borrowed(v_as_4664_, v_i_4665_);
lean_inc(v___x_4683_);
lean_inc(v_openDecls_4679_);
lean_inc(v_currNamespace_4678_);
lean_inc_ref(v_env_4676_);
v_nss_4684_ = l_Lean_ResolveName_resolveNamespace(v_env_4676_, v_currNamespace_4678_, v_openDecls_4679_, v___x_4683_);
v___x_4685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4685_, 0, v_env_4676_);
lean_ctor_set(v___x_4685_, 1, v_openDecls_4679_);
v___x_4686_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4663_, v___x_4685_, v_nss_4684_);
v_fst_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_fst_4687_);
v_snd_4688_ = lean_ctor_get(v___x_4686_, 1);
lean_inc(v_snd_4688_);
lean_dec_ref(v___x_4686_);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 3, v_snd_4688_);
lean_ctor_set(v___x_4681_, 0, v_fst_4687_);
v___x_4690_ = v___x_4681_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_fst_4687_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v_options_4677_);
lean_ctor_set(v_reuseFailAlloc_4697_, 2, v_currNamespace_4678_);
lean_ctor_set(v_reuseFailAlloc_4697_, 3, v_snd_4688_);
v___x_4690_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
lean_object* v___x_4692_; 
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 1, v___x_4690_);
v___x_4692_ = v___x_4674_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_toInputContext_4670_);
lean_ctor_set(v_reuseFailAlloc_4696_, 1, v___x_4690_);
lean_ctor_set(v_reuseFailAlloc_4696_, 2, v_toCacheableParserContext_4671_);
lean_ctor_set(v_reuseFailAlloc_4696_, 3, v_tokens_4672_);
v___x_4692_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
size_t v___x_4693_; size_t v___x_4694_; 
v___x_4693_ = ((size_t)1ULL);
v___x_4694_ = lean_usize_add(v_i_4665_, v___x_4693_);
v_i_4665_ = v___x_4694_;
v_b_4667_ = v___x_4692_;
goto _start;
}
}
}
}
}
else
{
return v_b_4667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object* v_addOpenSimple_4700_, lean_object* v_as_4701_, lean_object* v_i_4702_, lean_object* v_stop_4703_, lean_object* v_b_4704_){
_start:
{
uint8_t v_addOpenSimple_boxed_4705_; size_t v_i_boxed_4706_; size_t v_stop_boxed_4707_; lean_object* v_res_4708_; 
v_addOpenSimple_boxed_4705_ = lean_unbox(v_addOpenSimple_4700_);
v_i_boxed_4706_ = lean_unbox_usize(v_i_4702_);
lean_dec(v_i_4702_);
v_stop_boxed_4707_ = lean_unbox_usize(v_stop_4703_);
lean_dec(v_stop_4703_);
v_res_4708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_boxed_4705_, v_as_4701_, v_i_boxed_4706_, v_stop_boxed_4707_, v_b_4704_);
lean_dec_ref(v_as_4701_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object* v___x_4709_, lean_object* v_ids_4710_, uint8_t v_addOpenSimple_4711_, lean_object* v_c_4712_){
_start:
{
lean_object* v___y_4714_; lean_object* v___x_4733_; lean_object* v___x_4734_; uint8_t v___x_4735_; 
v___x_4733_ = lean_unsigned_to_nat(0u);
v___x_4734_ = lean_array_get_size(v_ids_4710_);
v___x_4735_ = lean_nat_dec_lt(v___x_4733_, v___x_4734_);
if (v___x_4735_ == 0)
{
v___y_4714_ = v_c_4712_;
goto v___jp_4713_;
}
else
{
uint8_t v___x_4736_; 
v___x_4736_ = lean_nat_dec_le(v___x_4734_, v___x_4734_);
if (v___x_4736_ == 0)
{
if (v___x_4735_ == 0)
{
v___y_4714_ = v_c_4712_;
goto v___jp_4713_;
}
else
{
size_t v___x_4737_; size_t v___x_4738_; lean_object* v___x_4739_; 
v___x_4737_ = ((size_t)0ULL);
v___x_4738_ = lean_usize_of_nat(v___x_4734_);
v___x_4739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4711_, v_ids_4710_, v___x_4737_, v___x_4738_, v_c_4712_);
v___y_4714_ = v___x_4739_;
goto v___jp_4713_;
}
}
else
{
size_t v___x_4740_; size_t v___x_4741_; lean_object* v___x_4742_; 
v___x_4740_ = ((size_t)0ULL);
v___x_4741_ = lean_usize_of_nat(v___x_4734_);
v___x_4742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4711_, v_ids_4710_, v___x_4740_, v___x_4741_, v_c_4712_);
v___y_4714_ = v___x_4742_;
goto v___jp_4713_;
}
}
v___jp_4713_:
{
lean_object* v_toParserModuleContext_4715_; lean_object* v_toInputContext_4716_; lean_object* v_toCacheableParserContext_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4731_; 
v_toParserModuleContext_4715_ = lean_ctor_get(v___y_4714_, 1);
v_toInputContext_4716_ = lean_ctor_get(v___y_4714_, 0);
v_toCacheableParserContext_4717_ = lean_ctor_get(v___y_4714_, 2);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___y_4714_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; 
v_unused_4732_ = lean_ctor_get(v___y_4714_, 3);
lean_dec(v_unused_4732_);
v___x_4719_ = v___y_4714_;
v_isShared_4720_ = v_isSharedCheck_4731_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_toCacheableParserContext_4717_);
lean_inc(v_toParserModuleContext_4715_);
lean_inc(v_toInputContext_4716_);
lean_dec(v___y_4714_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4731_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v_env_4721_; lean_object* v___x_4722_; lean_object* v_ext_4723_; lean_object* v_toEnvExtension_4724_; lean_object* v_asyncMode_4725_; lean_object* v___x_4726_; lean_object* v_tokens_4727_; lean_object* v___x_4729_; 
v_env_4721_ = lean_ctor_get(v_toParserModuleContext_4715_, 0);
v___x_4722_ = l_Lean_Parser_parserExtension;
v_ext_4723_ = lean_ctor_get(v___x_4722_, 1);
v_toEnvExtension_4724_ = lean_ctor_get(v_ext_4723_, 0);
v_asyncMode_4725_ = lean_ctor_get(v_toEnvExtension_4724_, 2);
lean_inc_ref(v_env_4721_);
v___x_4726_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4709_, v___x_4722_, v_env_4721_, v_asyncMode_4725_);
v_tokens_4727_ = lean_ctor_get(v___x_4726_, 0);
lean_inc_ref(v_tokens_4727_);
lean_dec(v___x_4726_);
if (v_isShared_4720_ == 0)
{
lean_ctor_set(v___x_4719_, 3, v_tokens_4727_);
v___x_4729_ = v___x_4719_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_toInputContext_4716_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_toParserModuleContext_4715_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_toCacheableParserContext_4717_);
lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_tokens_4727_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object* v___x_4743_, lean_object* v_ids_4744_, lean_object* v_addOpenSimple_4745_, lean_object* v_c_4746_){
_start:
{
uint8_t v_addOpenSimple_boxed_4747_; lean_object* v_res_4748_; 
v_addOpenSimple_boxed_4747_ = lean_unbox(v_addOpenSimple_4745_);
v_res_4748_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_4743_, v_ids_4744_, v_addOpenSimple_boxed_4747_, v_c_4746_);
lean_dec_ref(v_ids_4744_);
lean_dec_ref(v___x_4743_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* v_ids_4749_, uint8_t v_addOpenSimple_4750_, lean_object* v_p_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___f_4756_; lean_object* v___x_4757_; 
v___x_4754_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4755_ = lean_box(v_addOpenSimple_4750_);
v___f_4756_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4756_, 0, v___x_4754_);
lean_closure_set(v___f_4756_, 1, v_ids_4749_);
lean_closure_set(v___f_4756_, 2, v___x_4755_);
v___x_4757_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_4756_, v_p_4751_, v_a_4752_, v_a_4753_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* v_ids_4758_, lean_object* v_addOpenSimple_4759_, lean_object* v_p_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_){
_start:
{
uint8_t v_addOpenSimple_boxed_4763_; lean_object* v_res_4764_; 
v_addOpenSimple_boxed_4763_ = lean_unbox(v_addOpenSimple_4759_);
v_res_4764_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_4758_, v_addOpenSimple_boxed_4763_, v_p_4760_, v_a_4761_, v_a_4762_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t v_sz_4765_, size_t v_i_4766_, lean_object* v_bs_4767_){
_start:
{
uint8_t v___x_4768_; 
v___x_4768_ = lean_usize_dec_lt(v_i_4766_, v_sz_4765_);
if (v___x_4768_ == 0)
{
return v_bs_4767_;
}
else
{
lean_object* v_v_4769_; lean_object* v___x_4770_; lean_object* v_bs_x27_4771_; lean_object* v___x_4772_; size_t v___x_4773_; size_t v___x_4774_; lean_object* v___x_4775_; 
v_v_4769_ = lean_array_uget(v_bs_4767_, v_i_4766_);
v___x_4770_ = lean_unsigned_to_nat(0u);
v_bs_x27_4771_ = lean_array_uset(v_bs_4767_, v_i_4766_, v___x_4770_);
v___x_4772_ = l_Lean_Syntax_getId(v_v_4769_);
lean_dec(v_v_4769_);
v___x_4773_ = ((size_t)1ULL);
v___x_4774_ = lean_usize_add(v_i_4766_, v___x_4773_);
v___x_4775_ = lean_array_uset(v_bs_x27_4771_, v_i_4766_, v___x_4772_);
v_i_4766_ = v___x_4774_;
v_bs_4767_ = v___x_4775_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object* v_sz_4777_, lean_object* v_i_4778_, lean_object* v_bs_4779_){
_start:
{
size_t v_sz_boxed_4780_; size_t v_i_boxed_4781_; lean_object* v_res_4782_; 
v_sz_boxed_4780_ = lean_unbox_usize(v_sz_4777_);
lean_dec(v_sz_4777_);
v_i_boxed_4781_ = lean_unbox_usize(v_i_4778_);
lean_dec(v_i_4778_);
v_res_4782_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_boxed_4780_, v_i_boxed_4781_, v_bs_4779_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* v_openDeclStx_4796_, lean_object* v_p_4797_, lean_object* v_c_4798_, lean_object* v_s_4799_){
_start:
{
lean_object* v___x_4800_; lean_object* v___x_4801_; uint8_t v___x_4802_; 
lean_inc(v_openDeclStx_4796_);
v___x_4800_ = l_Lean_Syntax_getKind(v_openDeclStx_4796_);
v___x_4801_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__2));
v___x_4802_ = lean_name_eq(v___x_4800_, v___x_4801_);
if (v___x_4802_ == 0)
{
lean_object* v___x_4803_; uint8_t v___x_4804_; 
v___x_4803_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__4));
v___x_4804_ = lean_name_eq(v___x_4800_, v___x_4803_);
lean_dec(v___x_4800_);
if (v___x_4804_ == 0)
{
lean_object* v___x_4805_; 
lean_dec(v_openDeclStx_4796_);
v___x_4805_ = lean_apply_2(v_p_4797_, v_c_4798_, v_s_4799_);
return v___x_4805_;
}
else
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; size_t v_sz_4809_; size_t v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4806_ = lean_unsigned_to_nat(1u);
v___x_4807_ = l_Lean_Syntax_getArg(v_openDeclStx_4796_, v___x_4806_);
lean_dec(v_openDeclStx_4796_);
v___x_4808_ = l_Lean_Syntax_getArgs(v___x_4807_);
lean_dec(v___x_4807_);
v_sz_4809_ = lean_array_size(v___x_4808_);
v___x_4810_ = ((size_t)0ULL);
v___x_4811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4809_, v___x_4810_, v___x_4808_);
v___x_4812_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4811_, v___x_4802_, v_p_4797_, v_c_4798_, v_s_4799_);
return v___x_4812_;
}
}
else
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; size_t v_sz_4816_; size_t v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
lean_dec(v___x_4800_);
v___x_4813_ = lean_unsigned_to_nat(0u);
v___x_4814_ = l_Lean_Syntax_getArg(v_openDeclStx_4796_, v___x_4813_);
lean_dec(v_openDeclStx_4796_);
v___x_4815_ = l_Lean_Syntax_getArgs(v___x_4814_);
lean_dec(v___x_4814_);
v_sz_4816_ = lean_array_size(v___x_4815_);
v___x_4817_ = ((size_t)0ULL);
v___x_4818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4816_, v___x_4817_, v___x_4815_);
v___x_4819_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4818_, v___x_4802_, v_p_4797_, v_c_4798_, v_s_4799_);
return v___x_4819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* v_p_4826_, lean_object* v_c_4827_, lean_object* v_s_4828_){
_start:
{
lean_object* v_stxStack_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; uint8_t v___x_4832_; 
v_stxStack_4829_ = lean_ctor_get(v_s_4828_, 0);
v___x_4830_ = lean_unsigned_to_nat(0u);
v___x_4831_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4829_);
v___x_4832_ = lean_nat_dec_lt(v___x_4830_, v___x_4831_);
lean_dec(v___x_4831_);
if (v___x_4832_ == 0)
{
lean_object* v___x_4833_; 
v___x_4833_ = lean_apply_2(v_p_4826_, v_c_4827_, v_s_4828_);
return v___x_4833_;
}
else
{
lean_object* v_stx_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; uint8_t v___x_4837_; 
v_stx_4834_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4829_);
lean_inc(v_stx_4834_);
v___x_4835_ = l_Lean_Syntax_getKind(v_stx_4834_);
v___x_4836_ = ((lean_object*)(l_Lean_Parser_withOpenFn___closed__1));
v___x_4837_ = lean_name_eq(v___x_4835_, v___x_4836_);
lean_dec(v___x_4835_);
if (v___x_4837_ == 0)
{
lean_object* v___x_4838_; 
lean_dec(v_stx_4834_);
v___x_4838_ = lean_apply_2(v_p_4826_, v_c_4827_, v_s_4828_);
return v___x_4838_;
}
else
{
lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4839_ = lean_unsigned_to_nat(1u);
v___x_4840_ = l_Lean_Syntax_getArg(v_stx_4834_, v___x_4839_);
lean_dec(v_stx_4834_);
v___x_4841_ = l_Lean_Parser_withOpenDeclFnCore(v___x_4840_, v_p_4826_, v_c_4827_, v_s_4828_);
return v___x_4841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* v_p_4842_){
_start:
{
lean_object* v_info_4843_; lean_object* v_fn_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4852_; 
v_info_4843_ = lean_ctor_get(v_p_4842_, 0);
v_fn_4844_ = lean_ctor_get(v_p_4842_, 1);
v_isSharedCheck_4852_ = !lean_is_exclusive(v_p_4842_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4846_ = v_p_4842_;
v_isShared_4847_ = v_isSharedCheck_4852_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_fn_4844_);
lean_inc(v_info_4843_);
lean_dec(v_p_4842_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4852_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4848_; lean_object* v___x_4850_; 
v___x_4848_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(v___x_4848_, 0, v_fn_4844_);
if (v_isShared_4847_ == 0)
{
lean_ctor_set(v___x_4846_, 1, v___x_4848_);
v___x_4850_ = v___x_4846_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_info_4843_);
lean_ctor_set(v_reuseFailAlloc_4851_, 1, v___x_4848_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* v_p_4853_, lean_object* v_c_4854_, lean_object* v_s_4855_){
_start:
{
lean_object* v_stxStack_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; uint8_t v___x_4859_; 
v_stxStack_4856_ = lean_ctor_get(v_s_4855_, 0);
v___x_4857_ = lean_unsigned_to_nat(0u);
v___x_4858_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4856_);
v___x_4859_ = lean_nat_dec_lt(v___x_4857_, v___x_4858_);
lean_dec(v___x_4858_);
if (v___x_4859_ == 0)
{
lean_object* v___x_4860_; 
v___x_4860_ = lean_apply_2(v_p_4853_, v_c_4854_, v_s_4855_);
return v___x_4860_;
}
else
{
lean_object* v_stx_4861_; lean_object* v___x_4862_; 
v_stx_4861_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4856_);
v___x_4862_ = l_Lean_Parser_withOpenDeclFnCore(v_stx_4861_, v_p_4853_, v_c_4854_, v_s_4855_);
return v___x_4862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* v_p_4863_){
_start:
{
lean_object* v_info_4864_; lean_object* v_fn_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4873_; 
v_info_4864_ = lean_ctor_get(v_p_4863_, 0);
v_fn_4865_ = lean_ctor_get(v_p_4863_, 1);
v_isSharedCheck_4873_ = !lean_is_exclusive(v_p_4863_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4867_ = v_p_4863_;
v_isShared_4868_ = v_isSharedCheck_4873_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_fn_4865_);
lean_inc(v_info_4864_);
lean_dec(v_p_4863_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4873_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4869_; lean_object* v___x_4871_; 
v___x_4869_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(v___x_4869_, 0, v_fn_4865_);
if (v_isShared_4868_ == 0)
{
lean_ctor_set(v___x_4867_, 1, v___x_4869_);
v___x_4871_ = v___x_4867_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_info_4864_);
lean_ctor_set(v_reuseFailAlloc_4872_, 1, v___x_4869_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object* v_val_4880_){
_start:
{
lean_object* v___x_4888_; 
v___x_4888_ = l_Lean_Syntax_isStrLit_x3f(v_val_4880_);
if (lean_obj_tag(v___x_4888_) == 1)
{
lean_object* v_val_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4897_; 
v_val_4889_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4891_ = v___x_4888_;
v_isShared_4892_ = v_isSharedCheck_4897_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_val_4889_);
lean_dec(v___x_4888_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4897_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4893_; lean_object* v___x_4895_; 
v___x_4893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4893_, 0, v_val_4889_);
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 0, v___x_4893_);
v___x_4895_ = v___x_4891_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
else
{
lean_object* v___x_4898_; 
lean_dec(v___x_4888_);
v___x_4898_ = l_Lean_Syntax_isNatLit_x3f(v_val_4880_);
if (lean_obj_tag(v___x_4898_) == 1)
{
lean_object* v_val_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4907_; 
v_val_4899_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4901_ = v___x_4898_;
v_isShared_4902_ = v_isSharedCheck_4907_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_val_4899_);
lean_dec(v___x_4898_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4907_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4903_; lean_object* v___x_4905_; 
v___x_4903_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4903_, 0, v_val_4899_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v___x_4903_);
v___x_4905_ = v___x_4901_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v___x_4903_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
else
{
lean_dec(v___x_4898_);
if (lean_obj_tag(v_val_4880_) == 2)
{
lean_object* v_val_4908_; lean_object* v___x_4909_; uint8_t v___x_4910_; 
v_val_4908_ = lean_ctor_get(v_val_4880_, 1);
v___x_4909_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3));
v___x_4910_ = lean_string_dec_eq(v_val_4908_, v___x_4909_);
if (v___x_4910_ == 0)
{
goto v___jp_4881_;
}
else
{
lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4911_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4911_, 0, v___x_4910_);
v___x_4912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4911_);
return v___x_4912_;
}
}
else
{
goto v___jp_4881_;
}
}
}
v___jp_4881_:
{
if (lean_obj_tag(v_val_4880_) == 2)
{
lean_object* v_val_4882_; lean_object* v___x_4883_; uint8_t v___x_4884_; 
v_val_4882_ = lean_ctor_get(v_val_4880_, 1);
v___x_4883_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0));
v___x_4884_ = lean_string_dec_eq(v_val_4882_, v___x_4883_);
if (v___x_4884_ == 0)
{
lean_object* v___x_4885_; 
v___x_4885_ = lean_box(0);
return v___x_4885_;
}
else
{
lean_object* v___x_4886_; 
v___x_4886_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2));
return v___x_4886_;
}
}
else
{
lean_object* v___x_4887_; 
v___x_4887_ = lean_box(0);
return v___x_4887_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object* v_val_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_val_4913_);
lean_dec(v_val_4913_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object* v_nameStx_4915_, lean_object* v_v_4916_, lean_object* v_c_4917_){
_start:
{
lean_object* v_toParserModuleContext_4918_; lean_object* v_toInputContext_4919_; lean_object* v_toCacheableParserContext_4920_; lean_object* v_tokens_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4958_; 
v_toParserModuleContext_4918_ = lean_ctor_get(v_c_4917_, 1);
v_toInputContext_4919_ = lean_ctor_get(v_c_4917_, 0);
v_toCacheableParserContext_4920_ = lean_ctor_get(v_c_4917_, 2);
v_tokens_4921_ = lean_ctor_get(v_c_4917_, 3);
v_isSharedCheck_4958_ = !lean_is_exclusive(v_c_4917_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4923_ = v_c_4917_;
v_isShared_4924_ = v_isSharedCheck_4958_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_tokens_4921_);
lean_inc(v_toCacheableParserContext_4920_);
lean_inc(v_toParserModuleContext_4918_);
lean_inc(v_toInputContext_4919_);
lean_dec(v_c_4917_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4958_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v_env_4925_; lean_object* v_options_4926_; lean_object* v_currNamespace_4927_; lean_object* v_openDecls_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4957_; 
v_env_4925_ = lean_ctor_get(v_toParserModuleContext_4918_, 0);
v_options_4926_ = lean_ctor_get(v_toParserModuleContext_4918_, 1);
v_currNamespace_4927_ = lean_ctor_get(v_toParserModuleContext_4918_, 2);
v_openDecls_4928_ = lean_ctor_get(v_toParserModuleContext_4918_, 3);
v_isSharedCheck_4957_ = !lean_is_exclusive(v_toParserModuleContext_4918_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4930_ = v_toParserModuleContext_4918_;
v_isShared_4931_ = v_isSharedCheck_4957_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_openDecls_4928_);
lean_inc(v_currNamespace_4927_);
lean_inc(v_options_4926_);
lean_inc(v_env_4925_);
lean_dec(v_toParserModuleContext_4918_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4957_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___y_4933_; lean_object* v_map_4940_; uint8_t v_hasTrace_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4956_; 
v_map_4940_ = lean_ctor_get(v_options_4926_, 0);
v_hasTrace_4941_ = lean_ctor_get_uint8(v_options_4926_, sizeof(void*)*1);
v_isSharedCheck_4956_ = !lean_is_exclusive(v_options_4926_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4943_ = v_options_4926_;
v_isShared_4944_ = v_isSharedCheck_4956_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_map_4940_);
lean_dec(v_options_4926_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4956_;
goto v_resetjp_4942_;
}
v___jp_4932_:
{
lean_object* v___x_4935_; 
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 1, v___y_4933_);
v___x_4935_ = v___x_4930_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_env_4925_);
lean_ctor_set(v_reuseFailAlloc_4939_, 1, v___y_4933_);
lean_ctor_set(v_reuseFailAlloc_4939_, 2, v_currNamespace_4927_);
lean_ctor_set(v_reuseFailAlloc_4939_, 3, v_openDecls_4928_);
v___x_4935_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4937_; 
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 1, v___x_4935_);
v___x_4937_ = v___x_4923_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_toInputContext_4919_);
lean_ctor_set(v_reuseFailAlloc_4938_, 1, v___x_4935_);
lean_ctor_set(v_reuseFailAlloc_4938_, 2, v_toCacheableParserContext_4920_);
lean_ctor_set(v_reuseFailAlloc_4938_, 3, v_tokens_4921_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
v_resetjp_4942_:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4945_ = l_Lean_Syntax_getId(v_nameStx_4915_);
v___x_4946_ = l_Lean_Name_eraseMacroScopes(v___x_4945_);
lean_dec(v___x_4945_);
lean_inc(v___x_4946_);
v___x_4947_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_4946_, v_v_4916_, v_map_4940_);
if (v_hasTrace_4941_ == 0)
{
lean_object* v___x_4948_; uint8_t v___x_4949_; lean_object* v___x_4951_; 
v___x_4948_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_4949_ = l_Lean_Name_isPrefixOf(v___x_4948_, v___x_4946_);
lean_dec(v___x_4946_);
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 0, v___x_4947_);
v___x_4951_ = v___x_4943_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4947_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
lean_ctor_set_uint8(v___x_4951_, sizeof(void*)*1, v___x_4949_);
v___y_4933_ = v___x_4951_;
goto v___jp_4932_;
}
}
else
{
lean_object* v___x_4954_; 
lean_dec(v___x_4946_);
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 0, v___x_4947_);
v___x_4954_ = v___x_4943_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4947_);
lean_ctor_set_uint8(v_reuseFailAlloc_4955_, sizeof(void*)*1, v_hasTrace_4941_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
v___y_4933_ = v___x_4954_;
goto v___jp_4932_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object* v_nameStx_4959_, lean_object* v_v_4960_, lean_object* v_c_4961_){
_start:
{
lean_object* v_res_4962_; 
v_res_4962_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(v_nameStx_4959_, v_v_4960_, v_c_4961_);
lean_dec(v_nameStx_4959_);
return v_res_4962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object* v_nameStx_4963_, lean_object* v_valStx_4964_, lean_object* v_p_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_){
_start:
{
lean_object* v___x_4968_; 
v___x_4968_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_valStx_4964_);
if (lean_obj_tag(v___x_4968_) == 0)
{
lean_object* v___x_4969_; 
lean_dec(v_nameStx_4963_);
v___x_4969_ = lean_apply_2(v_p_4965_, v_a_4966_, v_a_4967_);
return v___x_4969_;
}
else
{
lean_object* v_val_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
v_val_4970_ = lean_ctor_get(v___x_4968_, 0);
lean_inc(v_val_4970_);
lean_dec_ref_known(v___x_4968_, 1);
v___x_4971_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed), 3, 2);
lean_closure_set(v___x_4971_, 0, v_nameStx_4963_);
lean_closure_set(v___x_4971_, 1, v_val_4970_);
v___x_4972_ = l_Lean_Parser_adaptUncacheableContextFn(v___x_4971_, v_p_4965_, v_a_4966_, v_a_4967_);
return v___x_4972_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object* v_nameStx_4973_, lean_object* v_valStx_4974_, lean_object* v_p_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_){
_start:
{
lean_object* v_res_4978_; 
v_res_4978_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v_nameStx_4973_, v_valStx_4974_, v_p_4975_, v_a_4976_, v_a_4977_);
lean_dec(v_valStx_4974_);
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object* v_p_4985_, lean_object* v_c_4986_, lean_object* v_s_4987_){
_start:
{
lean_object* v_stxStack_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; uint8_t v___x_4991_; 
v_stxStack_4988_ = lean_ctor_get(v_s_4987_, 0);
v___x_4989_ = lean_unsigned_to_nat(0u);
v___x_4990_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4988_);
v___x_4991_ = lean_nat_dec_lt(v___x_4989_, v___x_4990_);
lean_dec(v___x_4990_);
if (v___x_4991_ == 0)
{
lean_object* v___x_4992_; 
v___x_4992_ = lean_apply_2(v_p_4985_, v_c_4986_, v_s_4987_);
return v___x_4992_;
}
else
{
lean_object* v_stx_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; uint8_t v___x_4996_; 
v_stx_4993_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4988_);
lean_inc(v_stx_4993_);
v___x_4994_ = l_Lean_Syntax_getKind(v_stx_4993_);
v___x_4995_ = ((lean_object*)(l_Lean_Parser_withSetOptionFn___closed__1));
v___x_4996_ = lean_name_eq(v___x_4994_, v___x_4995_);
lean_dec(v___x_4994_);
if (v___x_4996_ == 0)
{
lean_object* v___x_4997_; 
lean_dec(v_stx_4993_);
v___x_4997_ = lean_apply_2(v_p_4985_, v_c_4986_, v_s_4987_);
return v___x_4997_;
}
else
{
lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_4998_ = lean_unsigned_to_nat(1u);
v___x_4999_ = l_Lean_Syntax_getArg(v_stx_4993_, v___x_4998_);
v___x_5000_ = lean_unsigned_to_nat(3u);
v___x_5001_ = l_Lean_Syntax_getArg(v_stx_4993_, v___x_5000_);
lean_dec(v_stx_4993_);
v___x_5002_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_4999_, v___x_5001_, v_p_4985_, v_c_4986_, v_s_4987_);
lean_dec(v___x_5001_);
return v___x_5002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object* v_p_5003_){
_start:
{
lean_object* v_info_5004_; lean_object* v_fn_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5013_; 
v_info_5004_ = lean_ctor_get(v_p_5003_, 0);
v_fn_5005_ = lean_ctor_get(v_p_5003_, 1);
v_isSharedCheck_5013_ = !lean_is_exclusive(v_p_5003_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5007_ = v_p_5003_;
v_isShared_5008_ = v_isSharedCheck_5013_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_fn_5005_);
lean_inc(v_info_5004_);
lean_dec(v_p_5003_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5013_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5009_; lean_object* v___x_5011_; 
v___x_5009_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionFn), 3, 1);
lean_closure_set(v___x_5009_, 0, v_fn_5005_);
if (v_isShared_5008_ == 0)
{
lean_ctor_set(v___x_5007_, 1, v___x_5009_);
v___x_5011_ = v___x_5007_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_info_5004_);
lean_ctor_set(v_reuseFailAlloc_5012_, 1, v___x_5009_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object* v_p_5014_, lean_object* v_c_5015_, lean_object* v_s_5016_){
_start:
{
lean_object* v_stxStack_5017_; lean_object* v_sz_5018_; lean_object* v___x_5019_; uint8_t v___x_5020_; 
v_stxStack_5017_ = lean_ctor_get(v_s_5016_, 0);
v_sz_5018_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5017_);
v___x_5019_ = lean_unsigned_to_nat(3u);
v___x_5020_ = lean_nat_dec_le(v___x_5019_, v_sz_5018_);
if (v___x_5020_ == 0)
{
lean_object* v___x_5021_; 
lean_dec(v_sz_5018_);
v___x_5021_ = lean_apply_2(v_p_5014_, v_c_5015_, v_s_5016_);
return v___x_5021_;
}
else
{
lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5022_ = lean_nat_sub(v_sz_5018_, v___x_5019_);
lean_dec(v_sz_5018_);
v___x_5023_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5017_, v___x_5022_);
lean_dec(v___x_5022_);
v___x_5024_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5017_);
v___x_5025_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5023_, v___x_5024_, v_p_5014_, v_c_5015_, v_s_5016_);
lean_dec(v___x_5024_);
return v___x_5025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object* v_p_5026_){
_start:
{
lean_object* v_info_5027_; lean_object* v_fn_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5036_; 
v_info_5027_ = lean_ctor_get(v_p_5026_, 0);
v_fn_5028_ = lean_ctor_get(v_p_5026_, 1);
v_isSharedCheck_5036_ = !lean_is_exclusive(v_p_5026_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5030_ = v_p_5026_;
v_isShared_5031_ = v_isSharedCheck_5036_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_fn_5028_);
lean_inc(v_info_5027_);
lean_dec(v_p_5026_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5036_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5032_; lean_object* v___x_5034_; 
v___x_5032_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionValueFn), 3, 1);
lean_closure_set(v___x_5032_, 0, v_fn_5028_);
if (v_isShared_5031_ == 0)
{
lean_ctor_set(v___x_5030_, 1, v___x_5032_);
v___x_5034_ = v___x_5030_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_info_5027_);
lean_ctor_set(v_reuseFailAlloc_5035_, 1, v___x_5032_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object* v___x_5037_){
_start:
{
lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5039_ = lean_st_ref_get(v___x_5037_);
v___x_5040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5039_);
return v___x_5040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v___x_5041_, lean_object* v___y_5042_){
_start:
{
lean_object* v_res_5043_; 
v_res_5043_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_5041_);
lean_dec(v___x_5041_);
return v_res_5043_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5044_; lean_object* v___f_5045_; 
v___x_5044_ = l_Lean_Parser_parserAliasesRef;
v___f_5045_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5045_, 0, v___x_5044_);
return v___f_5045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; 
v___f_5047_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_);
v___x_5048_ = lean_box(0);
v___x_5049_ = lean_box(2);
v___x_5050_ = l_Lean_registerEnvExtension___redArg(v___f_5047_, v___x_5048_, v___x_5049_);
return v___x_5050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v_a_5051_){
_start:
{
lean_object* v_res_5052_; 
v_res_5052_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
return v_res_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx(lean_object* v_x_5053_){
_start:
{
switch(lean_obj_tag(v_x_5053_))
{
case 0:
{
lean_object* v___x_5054_; 
v___x_5054_ = lean_unsigned_to_nat(0u);
return v___x_5054_;
}
case 1:
{
lean_object* v___x_5055_; 
v___x_5055_ = lean_unsigned_to_nat(1u);
return v___x_5055_;
}
default: 
{
lean_object* v___x_5056_; 
v___x_5056_ = lean_unsigned_to_nat(2u);
return v___x_5056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___boxed(lean_object* v_x_5057_){
_start:
{
lean_object* v_res_5058_; 
v_res_5058_ = l_Lean_Parser_ParserResolution_ctorIdx(v_x_5057_);
lean_dec_ref(v_x_5057_);
return v_res_5058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object* v_t_5059_, lean_object* v_k_5060_){
_start:
{
switch(lean_obj_tag(v_t_5059_))
{
case 0:
{
lean_object* v_cat_5061_; lean_object* v___x_5062_; 
v_cat_5061_ = lean_ctor_get(v_t_5059_, 0);
lean_inc(v_cat_5061_);
lean_dec_ref_known(v_t_5059_, 1);
v___x_5062_ = lean_apply_1(v_k_5060_, v_cat_5061_);
return v___x_5062_;
}
case 1:
{
lean_object* v_decl_5063_; uint8_t v_isDescr_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v_decl_5063_ = lean_ctor_get(v_t_5059_, 0);
lean_inc(v_decl_5063_);
v_isDescr_5064_ = lean_ctor_get_uint8(v_t_5059_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5059_, 1);
v___x_5065_ = lean_box(v_isDescr_5064_);
v___x_5066_ = lean_apply_2(v_k_5060_, v_decl_5063_, v___x_5065_);
return v___x_5066_;
}
default: 
{
lean_object* v_p_5067_; lean_object* v___x_5068_; 
v_p_5067_ = lean_ctor_get(v_t_5059_, 0);
lean_inc_ref(v_p_5067_);
lean_dec_ref_known(v_t_5059_, 1);
v___x_5068_ = lean_apply_1(v_k_5060_, v_p_5067_);
return v___x_5068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object* v_motive_5069_, lean_object* v_ctorIdx_5070_, lean_object* v_t_5071_, lean_object* v_h_5072_, lean_object* v_k_5073_){
_start:
{
lean_object* v___x_5074_; 
v___x_5074_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5071_, v_k_5073_);
return v___x_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object* v_motive_5075_, lean_object* v_ctorIdx_5076_, lean_object* v_t_5077_, lean_object* v_h_5078_, lean_object* v_k_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Lean_Parser_ParserResolution_ctorElim(v_motive_5075_, v_ctorIdx_5076_, v_t_5077_, v_h_5078_, v_k_5079_);
lean_dec(v_ctorIdx_5076_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object* v_t_5081_, lean_object* v_category_5082_){
_start:
{
lean_object* v___x_5083_; 
v___x_5083_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5081_, v_category_5082_);
return v___x_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object* v_motive_5084_, lean_object* v_t_5085_, lean_object* v_h_5086_, lean_object* v_category_5087_){
_start:
{
lean_object* v___x_5088_; 
v___x_5088_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5085_, v_category_5087_);
return v___x_5088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object* v_t_5089_, lean_object* v_parser_5090_){
_start:
{
lean_object* v___x_5091_; 
v___x_5091_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5089_, v_parser_5090_);
return v___x_5091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object* v_motive_5092_, lean_object* v_t_5093_, lean_object* v_h_5094_, lean_object* v_parser_5095_){
_start:
{
lean_object* v___x_5096_; 
v___x_5096_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5093_, v_parser_5095_);
return v___x_5096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object* v_t_5097_, lean_object* v_alias_5098_){
_start:
{
lean_object* v___x_5099_; 
v___x_5099_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5097_, v_alias_5098_);
return v___x_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object* v_motive_5100_, lean_object* v_t_5101_, lean_object* v_h_5102_, lean_object* v_alias_5103_){
_start:
{
lean_object* v___x_5104_; 
v___x_5104_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5101_, v_alias_5103_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object* v_env_5108_, lean_object* v_name_5109_){
_start:
{
uint8_t v___x_5110_; lean_object* v___x_5111_; 
v___x_5110_ = 0;
v___x_5111_ = l_Lean_Environment_find_x3f(v_env_5108_, v_name_5109_, v___x_5110_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v___x_5112_; 
v___x_5112_ = lean_box(0);
return v___x_5112_;
}
else
{
lean_object* v_val_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5160_; 
v_val_5113_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5115_ = v___x_5111_;
v_isShared_5116_ = v_isSharedCheck_5160_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_val_5113_);
lean_dec(v___x_5111_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5160_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5117_; 
v___x_5117_ = l_Lean_ConstantInfo_type(v_val_5113_);
lean_dec(v_val_5113_);
if (lean_obj_tag(v___x_5117_) == 4)
{
lean_object* v_declName_5118_; 
v_declName_5118_ = lean_ctor_get(v___x_5117_, 0);
lean_inc(v_declName_5118_);
lean_dec_ref_known(v___x_5117_, 2);
if (lean_obj_tag(v_declName_5118_) == 1)
{
lean_object* v_pre_5119_; 
v_pre_5119_ = lean_ctor_get(v_declName_5118_, 0);
lean_inc(v_pre_5119_);
if (lean_obj_tag(v_pre_5119_) == 1)
{
lean_object* v_pre_5120_; 
v_pre_5120_ = lean_ctor_get(v_pre_5119_, 0);
switch(lean_obj_tag(v_pre_5120_))
{
case 1:
{
lean_object* v_pre_5121_; 
lean_inc_ref(v_pre_5120_);
lean_del_object(v___x_5115_);
v_pre_5121_ = lean_ctor_get(v_pre_5120_, 0);
if (lean_obj_tag(v_pre_5121_) == 0)
{
lean_object* v_str_5122_; lean_object* v_str_5123_; lean_object* v_str_5124_; lean_object* v___x_5125_; uint8_t v___x_5126_; 
v_str_5122_ = lean_ctor_get(v_declName_5118_, 1);
lean_inc_ref(v_str_5122_);
lean_dec_ref_known(v_declName_5118_, 2);
v_str_5123_ = lean_ctor_get(v_pre_5119_, 1);
lean_inc_ref(v_str_5123_);
lean_dec_ref_known(v_pre_5119_, 2);
v_str_5124_ = lean_ctor_get(v_pre_5120_, 1);
lean_inc_ref(v_str_5124_);
lean_dec_ref_known(v_pre_5120_, 2);
v___x_5125_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5126_ = lean_string_dec_eq(v_str_5124_, v___x_5125_);
lean_dec_ref(v_str_5124_);
if (v___x_5126_ == 0)
{
lean_object* v___x_5127_; 
lean_dec_ref(v_str_5123_);
lean_dec_ref(v_str_5122_);
v___x_5127_ = lean_box(0);
return v___x_5127_;
}
else
{
lean_object* v___x_5128_; uint8_t v___x_5129_; 
v___x_5128_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_5129_ = lean_string_dec_eq(v_str_5123_, v___x_5128_);
lean_dec_ref(v_str_5123_);
if (v___x_5129_ == 0)
{
lean_object* v___x_5130_; 
lean_dec_ref(v_str_5122_);
v___x_5130_ = lean_box(0);
return v___x_5130_;
}
else
{
uint8_t v___x_5131_; 
v___x_5131_ = lean_string_dec_eq(v_str_5122_, v___x_5128_);
if (v___x_5131_ == 0)
{
lean_object* v___x_5132_; uint8_t v___x_5133_; 
v___x_5132_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_5133_ = lean_string_dec_eq(v_str_5122_, v___x_5132_);
lean_dec_ref(v_str_5122_);
if (v___x_5133_ == 0)
{
lean_object* v___x_5134_; 
v___x_5134_ = lean_box(0);
return v___x_5134_;
}
else
{
lean_object* v___x_5135_; 
v___x_5135_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5135_;
}
}
else
{
lean_object* v___x_5136_; 
lean_dec_ref(v_str_5122_);
v___x_5136_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5136_;
}
}
}
}
else
{
lean_object* v___x_5137_; 
lean_dec_ref_known(v_pre_5120_, 2);
lean_dec_ref_known(v_pre_5119_, 2);
lean_dec_ref_known(v_declName_5118_, 2);
v___x_5137_ = lean_box(0);
return v___x_5137_;
}
}
case 0:
{
lean_object* v_str_5138_; lean_object* v_str_5139_; lean_object* v___x_5140_; uint8_t v___x_5141_; 
v_str_5138_ = lean_ctor_get(v_declName_5118_, 1);
lean_inc_ref(v_str_5138_);
lean_dec_ref_known(v_declName_5118_, 2);
v_str_5139_ = lean_ctor_get(v_pre_5119_, 1);
lean_inc_ref(v_str_5139_);
lean_dec_ref_known(v_pre_5119_, 2);
v___x_5140_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5141_ = lean_string_dec_eq(v_str_5139_, v___x_5140_);
lean_dec_ref(v_str_5139_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; 
lean_dec_ref(v_str_5138_);
lean_del_object(v___x_5115_);
v___x_5142_ = lean_box(0);
return v___x_5142_;
}
else
{
lean_object* v___x_5143_; uint8_t v___x_5144_; 
v___x_5143_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_5144_ = lean_string_dec_eq(v_str_5138_, v___x_5143_);
if (v___x_5144_ == 0)
{
lean_object* v___x_5145_; uint8_t v___x_5146_; 
v___x_5145_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_5146_ = lean_string_dec_eq(v_str_5138_, v___x_5145_);
lean_dec_ref(v_str_5138_);
if (v___x_5146_ == 0)
{
lean_object* v___x_5147_; 
lean_del_object(v___x_5115_);
v___x_5147_ = lean_box(0);
return v___x_5147_;
}
else
{
lean_object* v___x_5148_; lean_object* v___x_5150_; 
v___x_5148_ = lean_box(v___x_5141_);
if (v_isShared_5116_ == 0)
{
lean_ctor_set(v___x_5115_, 0, v___x_5148_);
v___x_5150_ = v___x_5115_;
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
else
{
lean_object* v___x_5152_; lean_object* v___x_5154_; 
lean_dec_ref(v_str_5138_);
v___x_5152_ = lean_box(v___x_5141_);
if (v_isShared_5116_ == 0)
{
lean_ctor_set(v___x_5115_, 0, v___x_5152_);
v___x_5154_ = v___x_5115_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v___x_5152_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
default: 
{
lean_object* v___x_5156_; 
lean_dec_ref_known(v_pre_5119_, 2);
lean_dec_ref_known(v_declName_5118_, 2);
lean_del_object(v___x_5115_);
v___x_5156_ = lean_box(0);
return v___x_5156_;
}
}
}
else
{
lean_object* v___x_5157_; 
lean_dec(v_pre_5119_);
lean_dec_ref_known(v_declName_5118_, 2);
lean_del_object(v___x_5115_);
v___x_5157_ = lean_box(0);
return v___x_5157_;
}
}
else
{
lean_object* v___x_5158_; 
lean_dec(v_declName_5118_);
lean_del_object(v___x_5115_);
v___x_5158_ = lean_box(0);
return v___x_5158_;
}
}
else
{
lean_object* v___x_5159_; 
lean_dec_ref(v___x_5117_);
lean_del_object(v___x_5115_);
v___x_5159_ = lean_box(0);
return v___x_5159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object* v_env_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_){
_start:
{
if (lean_obj_tag(v_a_5162_) == 0)
{
lean_object* v___x_5164_; 
lean_dec_ref(v_env_5161_);
v___x_5164_ = lean_array_to_list(v_a_5163_);
return v___x_5164_;
}
else
{
lean_object* v_head_5165_; lean_object* v_snd_5166_; 
v_head_5165_ = lean_ctor_get(v_a_5162_, 0);
v_snd_5166_ = lean_ctor_get(v_head_5165_, 1);
if (lean_obj_tag(v_snd_5166_) == 0)
{
lean_object* v_tail_5167_; lean_object* v_fst_5168_; lean_object* v___x_5169_; 
lean_inc(v_head_5165_);
v_tail_5167_ = lean_ctor_get(v_a_5162_, 1);
lean_inc(v_tail_5167_);
lean_dec_ref_known(v_a_5162_, 2);
v_fst_5168_ = lean_ctor_get(v_head_5165_, 0);
lean_inc_n(v_fst_5168_, 2);
lean_dec(v_head_5165_);
lean_inc_ref(v_env_5161_);
v___x_5169_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5161_, v_fst_5168_);
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_dec(v_fst_5168_);
v_a_5162_ = v_tail_5167_;
goto _start;
}
else
{
lean_object* v_val_5171_; lean_object* v___x_5172_; uint8_t v___x_5173_; lean_object* v___x_5174_; 
v_val_5171_ = lean_ctor_get(v___x_5169_, 0);
lean_inc(v_val_5171_);
lean_dec_ref_known(v___x_5169_, 1);
v___x_5172_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5172_, 0, v_fst_5168_);
v___x_5173_ = lean_unbox(v_val_5171_);
lean_dec(v_val_5171_);
lean_ctor_set_uint8(v___x_5172_, sizeof(void*)*1, v___x_5173_);
v___x_5174_ = lean_array_push(v_a_5163_, v___x_5172_);
v_a_5162_ = v_tail_5167_;
v_a_5163_ = v___x_5174_;
goto _start;
}
}
else
{
lean_object* v_tail_5176_; 
v_tail_5176_ = lean_ctor_get(v_a_5162_, 1);
lean_inc(v_tail_5176_);
lean_dec_ref_known(v_a_5162_, 2);
v_a_5162_ = v_tail_5176_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object* v_env_5181_, lean_object* v_as_x27_5182_, lean_object* v_b_5183_){
_start:
{
if (lean_obj_tag(v_as_x27_5182_) == 0)
{
lean_dec_ref(v_env_5181_);
lean_inc_ref(v_b_5183_);
return v_b_5183_;
}
else
{
lean_object* v_head_5184_; lean_object* v_tail_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
v_head_5184_ = lean_ctor_get(v_as_x27_5182_, 0);
v_tail_5185_ = lean_ctor_get(v_as_x27_5182_, 1);
v___x_5186_ = lean_box(0);
v___x_5187_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_5184_) == 1)
{
lean_object* v_fields_5188_; 
v_fields_5188_ = lean_ctor_get(v_head_5184_, 1);
if (lean_obj_tag(v_fields_5188_) == 0)
{
lean_object* v_n_5189_; lean_object* v___x_5190_; 
v_n_5189_ = lean_ctor_get(v_head_5184_, 0);
lean_inc(v_n_5189_);
lean_inc_ref(v_env_5181_);
v___x_5190_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5181_, v_n_5189_);
if (lean_obj_tag(v___x_5190_) == 1)
{
lean_object* v_val_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5203_; 
lean_dec_ref(v_env_5181_);
v_val_5191_ = lean_ctor_get(v___x_5190_, 0);
v_isSharedCheck_5203_ = !lean_is_exclusive(v___x_5190_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5193_ = v___x_5190_;
v_isShared_5194_ = v_isSharedCheck_5203_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_val_5191_);
lean_dec(v___x_5190_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5203_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___x_5195_; uint8_t v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5200_; 
lean_inc(v_n_5189_);
v___x_5195_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5195_, 0, v_n_5189_);
v___x_5196_ = lean_unbox(v_val_5191_);
lean_dec(v_val_5191_);
lean_ctor_set_uint8(v___x_5195_, sizeof(void*)*1, v___x_5196_);
v___x_5197_ = lean_box(0);
v___x_5198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5195_);
lean_ctor_set(v___x_5198_, 1, v___x_5197_);
if (v_isShared_5194_ == 0)
{
lean_ctor_set(v___x_5193_, 0, v___x_5198_);
v___x_5200_ = v___x_5193_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v___x_5198_);
v___x_5200_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
lean_object* v___x_5201_; 
v___x_5201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5200_);
lean_ctor_set(v___x_5201_, 1, v___x_5186_);
return v___x_5201_;
}
}
}
else
{
lean_dec(v___x_5190_);
v_as_x27_5182_ = v_tail_5185_;
v_b_5183_ = v___x_5187_;
goto _start;
}
}
else
{
v_as_x27_5182_ = v_tail_5185_;
v_b_5183_ = v___x_5187_;
goto _start;
}
}
else
{
v_as_x27_5182_ = v_tail_5185_;
v_b_5183_ = v___x_5187_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object* v_env_5207_, lean_object* v_as_x27_5208_, lean_object* v_b_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5207_, v_as_x27_5208_, v_b_5209_);
lean_dec_ref(v_b_5209_);
lean_dec(v_as_x27_5208_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object* v_env_5213_, lean_object* v_opts_5214_, lean_object* v_currNamespace_5215_, lean_object* v_openDecls_5216_, lean_object* v_ident_5217_){
_start:
{
if (lean_obj_tag(v_ident_5217_) == 3)
{
lean_object* v_val_5218_; lean_object* v_preresolved_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v_fst_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5257_; 
v_val_5218_ = lean_ctor_get(v_ident_5217_, 2);
lean_inc(v_val_5218_);
v_preresolved_5219_ = lean_ctor_get(v_ident_5217_, 3);
lean_inc(v_preresolved_5219_);
lean_dec_ref_known(v_ident_5217_, 4);
v___x_5220_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
lean_inc_ref(v_env_5213_);
v___x_5221_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5213_, v_preresolved_5219_, v___x_5220_);
lean_dec(v_preresolved_5219_);
v_fst_5222_ = lean_ctor_get(v___x_5221_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5257_ == 0)
{
lean_object* v_unused_5258_; 
v_unused_5258_ = lean_ctor_get(v___x_5221_, 1);
lean_dec(v_unused_5258_);
v___x_5224_ = v___x_5221_;
v_isShared_5225_ = v_isSharedCheck_5257_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_fst_5222_);
lean_dec(v___x_5221_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5257_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
if (lean_obj_tag(v_fst_5222_) == 0)
{
lean_object* v___x_5226_; uint8_t v___x_5227_; 
v___x_5226_ = l_Lean_Name_eraseMacroScopes(v_val_5218_);
lean_inc_ref(v_env_5213_);
v___x_5227_ = l_Lean_Parser_isParserCategory(v_env_5213_, v___x_5226_);
if (v___x_5227_ == 0)
{
lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; uint8_t v___x_5231_; 
lean_inc_ref_n(v_env_5213_, 2);
v___x_5228_ = l_Lean_ResolveName_resolveGlobalName(v_env_5213_, v_opts_5214_, v_currNamespace_5215_, v_openDecls_5216_, v_val_5218_);
v___x_5229_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0));
v___x_5230_ = l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(v_env_5213_, v___x_5228_, v___x_5229_);
v___x_5231_ = l_List_isEmpty___redArg(v___x_5230_);
if (v___x_5231_ == 0)
{
lean_dec(v___x_5226_);
lean_del_object(v___x_5224_);
lean_dec_ref(v_env_5213_);
return v___x_5230_;
}
else
{
lean_object* v___x_5232_; lean_object* v_asyncMode_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; 
lean_dec(v___x_5230_);
v___x_5232_ = l_Lean_Parser_aliasExtension;
v_asyncMode_5233_ = lean_ctor_get(v___x_5232_, 2);
v___x_5234_ = lean_box(1);
v___x_5235_ = lean_box(0);
v___x_5236_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5234_, v___x_5232_, v_env_5213_, v_asyncMode_5233_, v___x_5235_);
v___x_5237_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5236_, v___x_5226_);
lean_dec(v___x_5226_);
lean_dec(v___x_5236_);
if (lean_obj_tag(v___x_5237_) == 1)
{
lean_object* v_val_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5249_; 
v_val_5238_ = lean_ctor_get(v___x_5237_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5237_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5240_ = v___x_5237_;
v_isShared_5241_ = v_isSharedCheck_5249_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_val_5238_);
lean_dec(v___x_5237_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5249_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5243_; 
if (v_isShared_5241_ == 0)
{
lean_ctor_set_tag(v___x_5240_, 2);
v___x_5243_ = v___x_5240_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_val_5238_);
v___x_5243_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
lean_object* v___x_5244_; lean_object* v___x_5246_; 
v___x_5244_ = lean_box(0);
if (v_isShared_5225_ == 0)
{
lean_ctor_set_tag(v___x_5224_, 1);
lean_ctor_set(v___x_5224_, 1, v___x_5244_);
lean_ctor_set(v___x_5224_, 0, v___x_5243_);
v___x_5246_ = v___x_5224_;
goto v_reusejp_5245_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5243_);
lean_ctor_set(v_reuseFailAlloc_5247_, 1, v___x_5244_);
v___x_5246_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5245_;
}
v_reusejp_5245_:
{
return v___x_5246_;
}
}
}
}
else
{
lean_object* v___x_5250_; 
lean_dec(v___x_5237_);
lean_del_object(v___x_5224_);
v___x_5250_ = lean_box(0);
return v___x_5250_;
}
}
}
else
{
lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5254_; 
lean_dec(v_val_5218_);
lean_dec(v_openDecls_5216_);
lean_dec(v_currNamespace_5215_);
lean_dec_ref(v_env_5213_);
v___x_5251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5251_, 0, v___x_5226_);
v___x_5252_ = lean_box(0);
if (v_isShared_5225_ == 0)
{
lean_ctor_set_tag(v___x_5224_, 1);
lean_ctor_set(v___x_5224_, 1, v___x_5252_);
lean_ctor_set(v___x_5224_, 0, v___x_5251_);
v___x_5254_ = v___x_5224_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v___x_5251_);
lean_ctor_set(v_reuseFailAlloc_5255_, 1, v___x_5252_);
v___x_5254_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
return v___x_5254_;
}
}
}
else
{
lean_object* v_val_5256_; 
lean_del_object(v___x_5224_);
lean_dec(v_val_5218_);
lean_dec(v_openDecls_5216_);
lean_dec(v_currNamespace_5215_);
lean_dec_ref(v_env_5213_);
v_val_5256_ = lean_ctor_get(v_fst_5222_, 0);
lean_inc(v_val_5256_);
lean_dec_ref_known(v_fst_5222_, 1);
return v_val_5256_;
}
}
}
else
{
lean_object* v___x_5259_; 
lean_dec(v_ident_5217_);
lean_dec(v_openDecls_5216_);
lean_dec(v_currNamespace_5215_);
lean_dec_ref(v_env_5213_);
v___x_5259_ = lean_box(0);
return v___x_5259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object* v_env_5260_, lean_object* v_opts_5261_, lean_object* v_currNamespace_5262_, lean_object* v_openDecls_5263_, lean_object* v_ident_5264_){
_start:
{
lean_object* v_res_5265_; 
v_res_5265_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5260_, v_opts_5261_, v_currNamespace_5262_, v_openDecls_5263_, v_ident_5264_);
lean_dec_ref(v_opts_5261_);
return v_res_5265_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object* v_env_5266_, lean_object* v_as_5267_, lean_object* v_as_x27_5268_, lean_object* v_b_5269_, lean_object* v_a_5270_){
_start:
{
lean_object* v___x_5271_; 
v___x_5271_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5266_, v_as_x27_5268_, v_b_5269_);
return v___x_5271_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object* v_env_5272_, lean_object* v_as_5273_, lean_object* v_as_x27_5274_, lean_object* v_b_5275_, lean_object* v_a_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(v_env_5272_, v_as_5273_, v_as_x27_5274_, v_b_5275_, v_a_5276_);
lean_dec_ref(v_b_5275_);
lean_dec(v_as_x27_5274_);
lean_dec(v_as_5273_);
return v_res_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object* v_ctx_5278_, lean_object* v_id_5279_, uint8_t v_unsetExporting_5280_){
_start:
{
lean_object* v___y_5282_; 
if (v_unsetExporting_5280_ == 0)
{
lean_object* v_toParserModuleContext_5288_; lean_object* v_env_5289_; 
v_toParserModuleContext_5288_ = lean_ctor_get(v_ctx_5278_, 1);
v_env_5289_ = lean_ctor_get(v_toParserModuleContext_5288_, 0);
lean_inc_ref(v_env_5289_);
v___y_5282_ = v_env_5289_;
goto v___jp_5281_;
}
else
{
lean_object* v_toParserModuleContext_5290_; lean_object* v_env_5291_; uint8_t v___x_5292_; lean_object* v___x_5293_; 
v_toParserModuleContext_5290_ = lean_ctor_get(v_ctx_5278_, 1);
v_env_5291_ = lean_ctor_get(v_toParserModuleContext_5290_, 0);
v___x_5292_ = 0;
lean_inc_ref(v_env_5291_);
v___x_5293_ = l_Lean_Environment_setExporting(v_env_5291_, v___x_5292_);
v___y_5282_ = v___x_5293_;
goto v___jp_5281_;
}
v___jp_5281_:
{
lean_object* v_toParserModuleContext_5283_; lean_object* v_options_5284_; lean_object* v_currNamespace_5285_; lean_object* v_openDecls_5286_; lean_object* v___x_5287_; 
v_toParserModuleContext_5283_ = lean_ctor_get(v_ctx_5278_, 1);
lean_inc_ref(v_toParserModuleContext_5283_);
lean_dec_ref(v_ctx_5278_);
v_options_5284_ = lean_ctor_get(v_toParserModuleContext_5283_, 1);
lean_inc_ref(v_options_5284_);
v_currNamespace_5285_ = lean_ctor_get(v_toParserModuleContext_5283_, 2);
lean_inc(v_currNamespace_5285_);
v_openDecls_5286_ = lean_ctor_get(v_toParserModuleContext_5283_, 3);
lean_inc(v_openDecls_5286_);
lean_dec_ref(v_toParserModuleContext_5283_);
v___x_5287_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v___y_5282_, v_options_5284_, v_currNamespace_5285_, v_openDecls_5286_, v_id_5279_);
lean_dec_ref(v_options_5284_);
return v___x_5287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object* v_ctx_5294_, lean_object* v_id_5295_, lean_object* v_unsetExporting_5296_){
_start:
{
uint8_t v_unsetExporting_boxed_5297_; lean_object* v_res_5298_; 
v_unsetExporting_boxed_5297_ = lean_unbox(v_unsetExporting_5296_);
v_res_5298_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5294_, v_id_5295_, v_unsetExporting_boxed_5297_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object* v_id_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_){
_start:
{
lean_object* v___x_5303_; lean_object* v_env_5304_; lean_object* v_options_5305_; lean_object* v_currNamespace_5306_; lean_object* v_openDecls_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; 
v___x_5303_ = lean_st_ref_get(v_a_5301_);
v_env_5304_ = lean_ctor_get(v___x_5303_, 0);
lean_inc_ref(v_env_5304_);
lean_dec(v___x_5303_);
v_options_5305_ = lean_ctor_get(v_a_5300_, 2);
v_currNamespace_5306_ = lean_ctor_get(v_a_5300_, 6);
v_openDecls_5307_ = lean_ctor_get(v_a_5300_, 7);
lean_inc(v_openDecls_5307_);
lean_inc(v_currNamespace_5306_);
v___x_5308_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5304_, v_options_5305_, v_currNamespace_5306_, v_openDecls_5307_, v_id_5299_);
v___x_5309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5309_, 0, v___x_5308_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object* v_id_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_){
_start:
{
lean_object* v_res_5314_; 
v_res_5314_ = l_Lean_Parser_resolveParserName(v_id_5310_, v_a_5311_, v_a_5312_);
lean_dec(v_a_5312_);
lean_dec_ref(v_a_5311_);
return v_res_5314_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object* v_x_5315_, lean_object* v_x_5316_){
_start:
{
if (lean_obj_tag(v_x_5315_) == 0)
{
if (lean_obj_tag(v_x_5316_) == 0)
{
uint8_t v___x_5317_; 
v___x_5317_ = 1;
return v___x_5317_;
}
else
{
uint8_t v___x_5318_; 
v___x_5318_ = 0;
return v___x_5318_;
}
}
else
{
if (lean_obj_tag(v_x_5316_) == 0)
{
uint8_t v___x_5319_; 
v___x_5319_ = 0;
return v___x_5319_;
}
else
{
lean_object* v_val_5320_; lean_object* v_val_5321_; uint8_t v___x_5322_; 
v_val_5320_ = lean_ctor_get(v_x_5315_, 0);
v_val_5321_ = lean_ctor_get(v_x_5316_, 0);
v___x_5322_ = l_Lean_Parser_instBEqError_beq(v_val_5320_, v_val_5321_);
return v___x_5322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object* v_x_5323_, lean_object* v_x_5324_){
_start:
{
uint8_t v_res_5325_; lean_object* v_r_5326_; 
v_res_5325_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5323_, v_x_5324_);
lean_dec(v_x_5324_);
lean_dec(v_x_5323_);
v_r_5326_ = lean_box(v_res_5325_);
return v_r_5326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t v___x_5327_, lean_object* v_ctx_5328_){
_start:
{
lean_object* v_toParserModuleContext_5329_; lean_object* v_toInputContext_5330_; lean_object* v_toCacheableParserContext_5331_; lean_object* v_tokens_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5357_; 
v_toParserModuleContext_5329_ = lean_ctor_get(v_ctx_5328_, 1);
v_toInputContext_5330_ = lean_ctor_get(v_ctx_5328_, 0);
v_toCacheableParserContext_5331_ = lean_ctor_get(v_ctx_5328_, 2);
v_tokens_5332_ = lean_ctor_get(v_ctx_5328_, 3);
v_isSharedCheck_5357_ = !lean_is_exclusive(v_ctx_5328_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5334_ = v_ctx_5328_;
v_isShared_5335_ = v_isSharedCheck_5357_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_tokens_5332_);
lean_inc(v_toCacheableParserContext_5331_);
lean_inc(v_toParserModuleContext_5329_);
lean_inc(v_toInputContext_5330_);
lean_dec(v_ctx_5328_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5357_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
lean_object* v_env_5336_; lean_object* v_options_5337_; lean_object* v_currNamespace_5338_; lean_object* v_openDecls_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5356_; 
v_env_5336_ = lean_ctor_get(v_toParserModuleContext_5329_, 0);
v_options_5337_ = lean_ctor_get(v_toParserModuleContext_5329_, 1);
v_currNamespace_5338_ = lean_ctor_get(v_toParserModuleContext_5329_, 2);
v_openDecls_5339_ = lean_ctor_get(v_toParserModuleContext_5329_, 3);
v_isSharedCheck_5356_ = !lean_is_exclusive(v_toParserModuleContext_5329_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5341_ = v_toParserModuleContext_5329_;
v_isShared_5342_ = v_isSharedCheck_5356_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_openDecls_5339_);
lean_inc(v_currNamespace_5338_);
lean_inc(v_options_5337_);
lean_inc(v_env_5336_);
lean_dec(v_toParserModuleContext_5329_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5356_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5343_; uint8_t v___y_5345_; lean_object* v___x_5353_; uint8_t v___x_5354_; 
v___x_5343_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_5353_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_5354_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_5337_, v___x_5353_);
if (v___x_5354_ == 0)
{
uint8_t v___x_5355_; 
v___x_5355_ = 1;
v___y_5345_ = v___x_5355_;
goto v___jp_5344_;
}
else
{
v___y_5345_ = v___x_5327_;
goto v___jp_5344_;
}
v___jp_5344_:
{
lean_object* v___x_5346_; lean_object* v___x_5348_; 
v___x_5346_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_5337_, v___x_5343_, v___y_5345_);
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 1, v___x_5346_);
v___x_5348_ = v___x_5341_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_env_5336_);
lean_ctor_set(v_reuseFailAlloc_5352_, 1, v___x_5346_);
lean_ctor_set(v_reuseFailAlloc_5352_, 2, v_currNamespace_5338_);
lean_ctor_set(v_reuseFailAlloc_5352_, 3, v_openDecls_5339_);
v___x_5348_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
lean_object* v___x_5350_; 
if (v_isShared_5335_ == 0)
{
lean_ctor_set(v___x_5334_, 1, v___x_5348_);
v___x_5350_ = v___x_5334_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_toInputContext_5330_);
lean_ctor_set(v_reuseFailAlloc_5351_, 1, v___x_5348_);
lean_ctor_set(v_reuseFailAlloc_5351_, 2, v_toCacheableParserContext_5331_);
lean_ctor_set(v_reuseFailAlloc_5351_, 3, v_tokens_5332_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object* v___x_5358_, lean_object* v_ctx_5359_){
_start:
{
uint8_t v___x_1088__boxed_5360_; lean_object* v_res_5361_; 
v___x_1088__boxed_5360_ = lean_unbox(v___x_5358_);
v_res_5361_ = l_Lean_Parser_parserOfStackFn___lam__0(v___x_1088__boxed_5360_, v_ctx_5359_);
return v_res_5361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* v_offset_5369_, lean_object* v_ctx_5370_, lean_object* v_s_5371_){
_start:
{
lean_object* v_stxStack_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; uint8_t v___x_5376_; 
v_stxStack_5372_ = lean_ctor_get(v_s_5371_, 0);
v___x_5373_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5372_);
v___x_5374_ = lean_unsigned_to_nat(1u);
v___x_5375_ = lean_nat_add(v_offset_5369_, v___x_5374_);
v___x_5376_ = lean_nat_dec_lt(v___x_5373_, v___x_5375_);
lean_dec(v___x_5375_);
if (v___x_5376_ == 0)
{
lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; 
v___x_5377_ = lean_nat_sub(v___x_5373_, v_offset_5369_);
lean_dec(v___x_5373_);
v___x_5378_ = lean_nat_sub(v___x_5377_, v___x_5374_);
lean_dec(v___x_5377_);
v___x_5379_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5372_, v___x_5378_);
lean_dec(v___x_5378_);
if (lean_obj_tag(v___x_5379_) == 3)
{
uint8_t v___x_5391_; lean_object* v___x_5392_; 
v___x_5391_ = 1;
lean_inc_ref(v___x_5379_);
lean_inc_ref(v_ctx_5370_);
v___x_5392_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5370_, v___x_5379_, v___x_5391_);
if (lean_obj_tag(v___x_5392_) == 0)
{
lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; 
lean_dec_ref(v_ctx_5370_);
v___x_5393_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__1));
v___x_5394_ = lean_box(0);
v___x_5395_ = l_Lean_Syntax_formatStx(v___x_5379_, v___x_5394_, v___x_5376_);
v___x_5396_ = l_Std_Format_defWidth;
v___x_5397_ = lean_unsigned_to_nat(0u);
v___x_5398_ = l_Std_Format_pretty(v___x_5395_, v___x_5396_, v___x_5397_, v___x_5397_);
v___x_5399_ = lean_string_append(v___x_5393_, v___x_5398_);
lean_dec_ref(v___x_5398_);
v___x_5400_ = lean_box(0);
v___x_5401_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5371_, v___x_5399_, v___x_5400_, v___x_5391_);
return v___x_5401_;
}
else
{
lean_object* v_head_5402_; lean_object* v_tail_5403_; lean_object* v_iniSz_5404_; lean_object* v_s_5406_; 
v_head_5402_ = lean_ctor_get(v___x_5392_, 0);
lean_inc(v_head_5402_);
v_tail_5403_ = lean_ctor_get(v___x_5392_, 1);
lean_inc(v_tail_5403_);
lean_dec_ref_known(v___x_5392_, 2);
v_iniSz_5404_ = l_Lean_Parser_ParserState_stackSize(v_s_5371_);
switch(lean_obj_tag(v_head_5402_))
{
case 0:
{
if (lean_obj_tag(v_tail_5403_) == 0)
{
lean_object* v_cat_5416_; lean_object* v___x_5417_; 
lean_dec_ref_known(v___x_5379_, 4);
v_cat_5416_ = lean_ctor_get(v_head_5402_, 0);
lean_inc(v_cat_5416_);
lean_dec_ref_known(v_head_5402_, 1);
v___x_5417_ = l_Lean_Parser_categoryParserFn(v_cat_5416_, v_ctx_5370_, v_s_5371_);
v_s_5406_ = v___x_5417_;
goto v___jp_5405_;
}
else
{
lean_dec_ref_known(v_tail_5403_, 2);
lean_dec_ref_known(v_head_5402_, 1);
lean_dec(v_iniSz_5404_);
lean_dec_ref(v_ctx_5370_);
goto v___jp_5380_;
}
}
case 1:
{
if (lean_obj_tag(v_tail_5403_) == 0)
{
lean_object* v_decl_5418_; lean_object* v___x_5419_; lean_object* v___f_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; 
lean_dec_ref_known(v___x_5379_, 4);
v_decl_5418_ = lean_ctor_get(v_head_5402_, 0);
lean_inc(v_decl_5418_);
lean_dec_ref_known(v_head_5402_, 1);
v___x_5419_ = lean_box(v___x_5376_);
v___f_5420_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5420_, 0, v___x_5419_);
v___x_5421_ = lean_box(0);
v___x_5422_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_5422_, 0, v_decl_5418_);
lean_closure_set(v___x_5422_, 1, v___x_5421_);
v___x_5423_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5420_, v___x_5422_, v_ctx_5370_, v_s_5371_);
v_s_5406_ = v___x_5423_;
goto v___jp_5405_;
}
else
{
lean_dec_ref_known(v_tail_5403_, 2);
lean_dec_ref_known(v_head_5402_, 1);
lean_dec(v_iniSz_5404_);
lean_dec_ref(v_ctx_5370_);
goto v___jp_5380_;
}
}
default: 
{
if (lean_obj_tag(v_tail_5403_) == 0)
{
lean_object* v_p_5424_; 
v_p_5424_ = lean_ctor_get(v_head_5402_, 0);
lean_inc_ref(v_p_5424_);
lean_dec_ref_known(v_head_5402_, 1);
if (lean_obj_tag(v_p_5424_) == 0)
{
lean_object* v_p_5425_; lean_object* v_fn_5426_; lean_object* v___x_5427_; 
lean_dec_ref_known(v___x_5379_, 4);
v_p_5425_ = lean_ctor_get(v_p_5424_, 0);
lean_inc(v_p_5425_);
lean_dec_ref_known(v_p_5424_, 1);
v_fn_5426_ = lean_ctor_get(v_p_5425_, 1);
lean_inc_ref(v_fn_5426_);
lean_dec(v_p_5425_);
v___x_5427_ = lean_apply_2(v_fn_5426_, v_ctx_5370_, v_s_5371_);
v_s_5406_ = v___x_5427_;
goto v___jp_5405_;
}
else
{
lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; 
lean_dec_ref(v_p_5424_);
lean_dec(v_iniSz_5404_);
lean_dec_ref(v_ctx_5370_);
v___x_5428_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__3));
v___x_5429_ = lean_box(0);
v___x_5430_ = l_Lean_Syntax_formatStx(v___x_5379_, v___x_5429_, v___x_5376_);
v___x_5431_ = l_Std_Format_defWidth;
v___x_5432_ = lean_unsigned_to_nat(0u);
v___x_5433_ = l_Std_Format_pretty(v___x_5430_, v___x_5431_, v___x_5432_, v___x_5432_);
v___x_5434_ = lean_string_append(v___x_5428_, v___x_5433_);
lean_dec_ref(v___x_5433_);
v___x_5435_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__4));
v___x_5436_ = lean_string_append(v___x_5434_, v___x_5435_);
v___x_5437_ = lean_box(0);
v___x_5438_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5371_, v___x_5436_, v___x_5437_, v___x_5391_);
return v___x_5438_;
}
}
else
{
lean_dec_ref_known(v_tail_5403_, 2);
lean_dec_ref_known(v_head_5402_, 1);
lean_dec(v_iniSz_5404_);
lean_dec_ref(v_ctx_5370_);
goto v___jp_5380_;
}
}
}
v___jp_5405_:
{
lean_object* v_errorMsg_5407_; lean_object* v___x_5408_; uint8_t v___x_5409_; 
v_errorMsg_5407_ = lean_ctor_get(v_s_5406_, 4);
v___x_5408_ = lean_box(0);
v___x_5409_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_errorMsg_5407_, v___x_5408_);
if (v___x_5409_ == 0)
{
lean_dec(v_iniSz_5404_);
return v_s_5406_;
}
else
{
lean_object* v___x_5410_; lean_object* v___x_5411_; uint8_t v___x_5412_; 
v___x_5410_ = l_Lean_Parser_ParserState_stackSize(v_s_5406_);
v___x_5411_ = lean_nat_add(v_iniSz_5404_, v___x_5374_);
lean_dec(v_iniSz_5404_);
v___x_5412_ = lean_nat_dec_eq(v___x_5410_, v___x_5411_);
lean_dec(v___x_5411_);
lean_dec(v___x_5410_);
if (v___x_5412_ == 0)
{
lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; 
v___x_5413_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__2));
v___x_5414_ = lean_box(0);
v___x_5415_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5406_, v___x_5413_, v___x_5414_, v___x_5409_);
return v___x_5415_;
}
else
{
return v_s_5406_;
}
}
}
}
}
else
{
lean_object* v___x_5439_; lean_object* v___x_5440_; uint8_t v___x_5441_; lean_object* v___x_5442_; 
lean_dec(v___x_5379_);
lean_dec_ref(v_ctx_5370_);
v___x_5439_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__5));
v___x_5440_ = lean_box(0);
v___x_5441_ = 1;
v___x_5442_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5371_, v___x_5439_, v___x_5440_, v___x_5441_);
return v___x_5442_;
}
v___jp_5380_:
{
lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; uint8_t v___x_5389_; lean_object* v___x_5390_; 
v___x_5381_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__0));
v___x_5382_ = lean_box(0);
v___x_5383_ = l_Lean_Syntax_formatStx(v___x_5379_, v___x_5382_, v___x_5376_);
v___x_5384_ = l_Std_Format_defWidth;
v___x_5385_ = lean_unsigned_to_nat(0u);
v___x_5386_ = l_Std_Format_pretty(v___x_5383_, v___x_5384_, v___x_5385_, v___x_5385_);
v___x_5387_ = lean_string_append(v___x_5381_, v___x_5386_);
lean_dec_ref(v___x_5386_);
v___x_5388_ = lean_box(0);
v___x_5389_ = 1;
v___x_5390_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5371_, v___x_5387_, v___x_5388_, v___x_5389_);
return v___x_5390_;
}
}
else
{
lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; 
lean_dec(v___x_5373_);
lean_dec_ref(v_ctx_5370_);
v___x_5443_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__6));
v___x_5444_ = lean_box(0);
v___x_5445_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5371_, v___x_5443_, v___x_5444_, v___x_5376_);
return v___x_5445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* v_offset_5446_, lean_object* v_ctx_5447_, lean_object* v_s_5448_){
_start:
{
lean_object* v_res_5449_; 
v_res_5449_ = l_Lean_Parser_parserOfStackFn(v_offset_5446_, v_ctx_5447_, v_s_5448_);
lean_dec(v_offset_5446_);
return v_res_5449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object* v_prec_5450_, lean_object* v_x_5451_){
_start:
{
lean_object* v_quotDepth_5452_; uint8_t v_suppressInsideQuot_5453_; lean_object* v_savedPos_x3f_5454_; lean_object* v_forbiddenTk_x3f_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5462_; 
v_quotDepth_5452_ = lean_ctor_get(v_x_5451_, 1);
v_suppressInsideQuot_5453_ = lean_ctor_get_uint8(v_x_5451_, sizeof(void*)*4);
v_savedPos_x3f_5454_ = lean_ctor_get(v_x_5451_, 2);
v_forbiddenTk_x3f_5455_ = lean_ctor_get(v_x_5451_, 3);
v_isSharedCheck_5462_ = !lean_is_exclusive(v_x_5451_);
if (v_isSharedCheck_5462_ == 0)
{
lean_object* v_unused_5463_; 
v_unused_5463_ = lean_ctor_get(v_x_5451_, 0);
lean_dec(v_unused_5463_);
v___x_5457_ = v_x_5451_;
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_forbiddenTk_x3f_5455_);
lean_inc(v_savedPos_x3f_5454_);
lean_inc(v_quotDepth_5452_);
lean_dec(v_x_5451_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v___x_5460_; 
if (v_isShared_5458_ == 0)
{
lean_ctor_set(v___x_5457_, 0, v_prec_5450_);
v___x_5460_ = v___x_5457_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_prec_5450_);
lean_ctor_set(v_reuseFailAlloc_5461_, 1, v_quotDepth_5452_);
lean_ctor_set(v_reuseFailAlloc_5461_, 2, v_savedPos_x3f_5454_);
lean_ctor_set(v_reuseFailAlloc_5461_, 3, v_forbiddenTk_x3f_5455_);
lean_ctor_set_uint8(v_reuseFailAlloc_5461_, sizeof(void*)*4, v_suppressInsideQuot_5453_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object* v___y_5464_){
_start:
{
lean_inc(v___y_5464_);
return v___y_5464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object* v___y_5465_){
_start:
{
lean_object* v_res_5466_; 
v_res_5466_ = l_Lean_Parser_parserOfStack___lam__1(v___y_5465_);
lean_dec(v___y_5465_);
return v_res_5466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object* v___y_5467_){
_start:
{
lean_inc_ref(v___y_5467_);
return v___y_5467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object* v___y_5468_){
_start:
{
lean_object* v_res_5469_; 
v_res_5469_ = l_Lean_Parser_parserOfStack___lam__2(v___y_5468_);
lean_dec_ref(v___y_5468_);
return v_res_5469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* v_offset_5476_, lean_object* v_prec_5477_){
_start:
{
lean_object* v___f_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; 
v___f_5478_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___lam__0), 2, 1);
lean_closure_set(v___f_5478_, 0, v_prec_5477_);
v___x_5479_ = ((lean_object*)(l_Lean_Parser_parserOfStack___closed__2));
v___x_5480_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___boxed), 3, 1);
lean_closure_set(v___x_5480_, 0, v_offset_5476_);
v___x_5481_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5481_, 0, v___f_5478_);
lean_closure_set(v___x_5481_, 1, v___x_5480_);
v___x_5482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5482_, 0, v___x_5479_);
lean_ctor_set(v___x_5482_, 1, v___x_5481_);
return v___x_5482_;
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
