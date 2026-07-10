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
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_SyntaxStack_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_categoryParserFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(lean_object*);
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "expected parser to return exactly one syntax object"};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__0 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__0_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ambiguous parser name "};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__1 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__1_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "unknown parser "};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__2 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__2_value;
static const lean_closure_object l_Lean_Parser_parserOfStackFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_parserOfStackFn___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__3 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__3_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parser alias "};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__4 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__4_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = ", must not take parameters"};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__5 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__5_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 103, .m_capacity = 103, .m_length = 102, .m_data = "failed to determine parser using syntax stack, the specified element on the stack is not an identifier"};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__6 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__6_value;
static const lean_string_object l_Lean_Parser_parserOfStackFn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "failed to determine parser using syntax stack, stack is too small"};
static const lean_object* l_Lean_Parser_parserOfStackFn___closed__7 = (const lean_object*)&l_Lean_Parser_parserOfStackFn___closed__7_value;
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
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1212_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1212_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1212_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_unbox(v_a_1186_);
lean_dec(v_a_1186_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
lean_dec_ref(v_value_1183_);
lean_dec(v_aliasName_1182_);
v___x_1191_ = lean_obj_once(&l_Lean_Parser_registerAliasCore___redArg___closed__1, &l_Lean_Parser_registerAliasCore___redArg___closed__1_once, _init_l_Lean_Parser_registerAliasCore___redArg___closed__1);
if (v_isShared_1189_ == 0)
{
lean_ctor_set_tag(v___x_1188_, 1);
lean_ctor_set(v___x_1188_, 0, v___x_1191_);
v___x_1193_ = v___x_1188_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
else
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = lean_st_ref_get(v_mapRef_1181_);
v___x_1196_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_aliasName_1182_, v___x_1195_);
lean_dec(v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1197_ = lean_st_ref_take(v_mapRef_1181_);
v___x_1198_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1182_, v_value_1183_, v___x_1197_);
v___x_1199_ = lean_st_ref_set(v_mapRef_1181_, v___x_1198_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1199_);
v___x_1201_ = v___x_1188_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
lean_dec_ref(v_value_1183_);
v___x_1203_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__2));
v___x_1204_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1182_, v___x_1196_);
v___x_1205_ = lean_string_append(v___x_1203_, v___x_1204_);
lean_dec_ref(v___x_1204_);
v___x_1206_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__3));
v___x_1207_ = lean_string_append(v___x_1205_, v___x_1206_);
v___x_1208_ = lean_mk_io_user_error(v___x_1207_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set_tag(v___x_1188_, 1);
lean_ctor_set(v___x_1188_, 0, v___x_1208_);
v___x_1210_ = v___x_1188_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec_ref(v_value_1183_);
lean_dec(v_aliasName_1182_);
v_a_1213_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1185_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1185_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg___boxed(lean_object* v_mapRef_1221_, lean_object* v_aliasName_1222_, lean_object* v_value_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1221_, v_aliasName_1222_, v_value_1223_);
lean_dec(v_mapRef_1221_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore(lean_object* v_00_u03b1_1226_, lean_object* v_mapRef_1227_, lean_object* v_aliasName_1228_, lean_object* v_value_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1227_, v_aliasName_1228_, v_value_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___boxed(lean_object* v_00_u03b1_1232_, lean_object* v_mapRef_1233_, lean_object* v_aliasName_1234_, lean_object* v_value_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Parser_registerAliasCore(v_00_u03b1_1232_, v_mapRef_1233_, v_aliasName_1234_, v_value_1235_);
lean_dec(v_mapRef_1233_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg(lean_object* v_mapRef_1238_, lean_object* v_aliasName_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_st_ref_get(v_mapRef_1238_);
v___x_1242_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1241_, v_aliasName_1239_);
lean_dec(v___x_1241_);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg___boxed(lean_object* v_mapRef_1244_, lean_object* v_aliasName_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1244_, v_aliasName_1245_);
lean_dec(v_aliasName_1245_);
lean_dec(v_mapRef_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias(lean_object* v_00_u03b1_1248_, lean_object* v_mapRef_1249_, lean_object* v_aliasName_1250_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1249_, v_aliasName_1250_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___boxed(lean_object* v_00_u03b1_1253_, lean_object* v_mapRef_1254_, lean_object* v_aliasName_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Parser_getAlias(v_00_u03b1_1253_, v_mapRef_1254_, v_aliasName_1255_);
lean_dec(v_aliasName_1255_);
lean_dec(v_mapRef_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object* v_mapRef_1262_, lean_object* v_aliasName_1263_){
_start:
{
lean_object* v___x_1265_; lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1305_; 
v___x_1265_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1262_, v_aliasName_1263_);
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1305_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1305_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
if (lean_obj_tag(v_a_1266_) == 0)
{
lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1270_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1271_ = 1;
v___x_1272_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1263_, v___x_1271_);
v___x_1273_ = lean_string_append(v___x_1270_, v___x_1272_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1275_ = lean_string_append(v___x_1273_, v___x_1274_);
v___x_1276_ = lean_mk_io_user_error(v___x_1275_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
lean_ctor_set(v___x_1268_, 0, v___x_1276_);
v___x_1278_ = v___x_1268_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
else
{
lean_object* v_val_1280_; 
v_val_1280_ = lean_ctor_get(v_a_1266_, 0);
lean_inc(v_val_1280_);
lean_dec_ref_known(v_a_1266_, 1);
switch(lean_obj_tag(v_val_1280_))
{
case 0:
{
lean_object* v_p_1281_; lean_object* v___x_1283_; 
lean_dec(v_aliasName_1263_);
v_p_1281_ = lean_ctor_get(v_val_1280_, 0);
lean_inc(v_p_1281_);
lean_dec_ref_known(v_val_1280_, 1);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v_p_1281_);
v___x_1283_ = v___x_1268_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_p_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
case 1:
{
lean_object* v___x_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
lean_dec_ref_known(v_val_1280_, 1);
v___x_1285_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1286_ = 1;
v___x_1287_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1263_, v___x_1286_);
v___x_1288_ = lean_string_append(v___x_1285_, v___x_1287_);
lean_dec_ref(v___x_1287_);
v___x_1289_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__2));
v___x_1290_ = lean_string_append(v___x_1288_, v___x_1289_);
v___x_1291_ = lean_mk_io_user_error(v___x_1290_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
lean_ctor_set(v___x_1268_, 0, v___x_1291_);
v___x_1293_ = v___x_1268_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
default: 
{
lean_object* v___x_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
lean_dec_ref_known(v_val_1280_, 1);
v___x_1295_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1296_ = 1;
v___x_1297_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1263_, v___x_1296_);
v___x_1298_ = lean_string_append(v___x_1295_, v___x_1297_);
lean_dec_ref(v___x_1297_);
v___x_1299_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__3));
v___x_1300_ = lean_string_append(v___x_1298_, v___x_1299_);
v___x_1301_ = lean_mk_io_user_error(v___x_1300_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
lean_ctor_set(v___x_1268_, 0, v___x_1301_);
v___x_1303_ = v___x_1268_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object* v_mapRef_1306_, lean_object* v_aliasName_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1306_, v_aliasName_1307_);
lean_dec(v_mapRef_1306_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object* v_00_u03b1_1310_, lean_object* v_mapRef_1311_, lean_object* v_aliasName_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1311_, v_aliasName_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object* v_00_u03b1_1315_, lean_object* v_mapRef_1316_, lean_object* v_aliasName_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Parser_getConstAlias(v_00_u03b1_1315_, v_mapRef_1316_, v_aliasName_1317_);
lean_dec(v_mapRef_1316_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object* v_mapRef_1321_, lean_object* v_aliasName_1322_){
_start:
{
lean_object* v___x_1324_; lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1354_; 
v___x_1324_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1321_, v_aliasName_1322_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1354_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1354_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
if (lean_obj_tag(v_a_1325_) == 0)
{
lean_object* v___x_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1329_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1330_ = 1;
v___x_1331_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1322_, v___x_1330_);
v___x_1332_ = lean_string_append(v___x_1329_, v___x_1331_);
lean_dec_ref(v___x_1331_);
v___x_1333_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1334_ = lean_string_append(v___x_1332_, v___x_1333_);
v___x_1335_ = lean_mk_io_user_error(v___x_1334_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 1);
lean_ctor_set(v___x_1327_, 0, v___x_1335_);
v___x_1337_ = v___x_1327_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
else
{
lean_object* v_val_1339_; 
v_val_1339_ = lean_ctor_get(v_a_1325_, 0);
lean_inc(v_val_1339_);
lean_dec_ref_known(v_a_1325_, 1);
if (lean_obj_tag(v_val_1339_) == 1)
{
lean_object* v_p_1340_; lean_object* v___x_1342_; 
lean_dec(v_aliasName_1322_);
v_p_1340_ = lean_ctor_get(v_val_1339_, 0);
lean_inc(v_p_1340_);
lean_dec_ref_known(v_val_1339_, 1);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v_p_1340_);
v___x_1342_ = v___x_1327_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_p_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
else
{
lean_object* v___x_1344_; uint8_t v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_dec(v_val_1339_);
v___x_1344_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1345_ = 1;
v___x_1346_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1322_, v___x_1345_);
v___x_1347_ = lean_string_append(v___x_1344_, v___x_1346_);
lean_dec_ref(v___x_1346_);
v___x_1348_ = ((lean_object*)(l_Lean_Parser_getUnaryAlias___redArg___closed__0));
v___x_1349_ = lean_string_append(v___x_1347_, v___x_1348_);
v___x_1350_ = lean_mk_io_user_error(v___x_1349_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 1);
lean_ctor_set(v___x_1327_, 0, v___x_1350_);
v___x_1352_ = v___x_1327_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object* v_mapRef_1355_, lean_object* v_aliasName_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1355_, v_aliasName_1356_);
lean_dec(v_mapRef_1355_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object* v_00_u03b1_1359_, lean_object* v_mapRef_1360_, lean_object* v_aliasName_1361_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1360_, v_aliasName_1361_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object* v_00_u03b1_1364_, lean_object* v_mapRef_1365_, lean_object* v_aliasName_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_Parser_getUnaryAlias(v_00_u03b1_1364_, v_mapRef_1365_, v_aliasName_1366_);
lean_dec(v_mapRef_1365_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object* v_mapRef_1370_, lean_object* v_aliasName_1371_){
_start:
{
lean_object* v___x_1373_; lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1403_; 
v___x_1373_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1370_, v_aliasName_1371_);
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1403_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1403_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
if (lean_obj_tag(v_a_1374_) == 0)
{
lean_object* v___x_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1378_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1379_ = 1;
v___x_1380_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1371_, v___x_1379_);
v___x_1381_ = lean_string_append(v___x_1378_, v___x_1380_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1383_ = lean_string_append(v___x_1381_, v___x_1382_);
v___x_1384_ = lean_mk_io_user_error(v___x_1383_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 1);
lean_ctor_set(v___x_1376_, 0, v___x_1384_);
v___x_1386_ = v___x_1376_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
else
{
lean_object* v_val_1388_; 
v_val_1388_ = lean_ctor_get(v_a_1374_, 0);
lean_inc(v_val_1388_);
lean_dec_ref_known(v_a_1374_, 1);
if (lean_obj_tag(v_val_1388_) == 2)
{
lean_object* v_p_1389_; lean_object* v___x_1391_; 
lean_dec(v_aliasName_1371_);
v_p_1389_ = lean_ctor_get(v_val_1388_, 0);
lean_inc(v_p_1389_);
lean_dec_ref_known(v_val_1388_, 1);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v_p_1389_);
v___x_1391_ = v___x_1376_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_p_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
else
{
lean_object* v___x_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
lean_dec(v_val_1388_);
v___x_1393_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1394_ = 1;
v___x_1395_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1371_, v___x_1394_);
v___x_1396_ = lean_string_append(v___x_1393_, v___x_1395_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = ((lean_object*)(l_Lean_Parser_getBinaryAlias___redArg___closed__0));
v___x_1398_ = lean_string_append(v___x_1396_, v___x_1397_);
v___x_1399_ = lean_mk_io_user_error(v___x_1398_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 1);
lean_ctor_set(v___x_1376_, 0, v___x_1399_);
v___x_1401_ = v___x_1376_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg___boxed(lean_object* v_mapRef_1404_, lean_object* v_aliasName_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1404_, v_aliasName_1405_);
lean_dec(v_mapRef_1404_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object* v_00_u03b1_1408_, lean_object* v_mapRef_1409_, lean_object* v_aliasName_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1409_, v_aliasName_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___boxed(lean_object* v_00_u03b1_1413_, lean_object* v_mapRef_1414_, lean_object* v_aliasName_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Parser_getBinaryAlias(v_00_u03b1_1413_, v_mapRef_1414_, v_aliasName_1415_);
lean_dec(v_mapRef_1414_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = lean_box(1);
v___x_1420_ = lean_st_mk_ref(v___x_1419_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_box(1);
v___x_1426_ = lean_st_mk_ref(v___x_1425_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_box(1);
v___x_1432_ = lean_st_mk_ref(v___x_1431_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object* v_a_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(lean_object* v_t_1436_, lean_object* v_k_1437_, lean_object* v_fallback_1438_){
_start:
{
if (lean_obj_tag(v_t_1436_) == 0)
{
lean_object* v_k_1439_; lean_object* v_v_1440_; lean_object* v_l_1441_; lean_object* v_r_1442_; uint8_t v___x_1443_; 
v_k_1439_ = lean_ctor_get(v_t_1436_, 1);
v_v_1440_ = lean_ctor_get(v_t_1436_, 2);
v_l_1441_ = lean_ctor_get(v_t_1436_, 3);
v_r_1442_ = lean_ctor_get(v_t_1436_, 4);
v___x_1443_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1437_, v_k_1439_);
switch(v___x_1443_)
{
case 0:
{
v_t_1436_ = v_l_1441_;
goto _start;
}
case 1:
{
lean_inc(v_v_1440_);
return v_v_1440_;
}
default: 
{
v_t_1436_ = v_r_1442_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_1438_);
return v_fallback_1438_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg___boxed(lean_object* v_t_1446_, lean_object* v_k_1447_, lean_object* v_fallback_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1446_, v_k_1447_, v_fallback_1448_);
lean_dec(v_fallback_1448_);
lean_dec(v_k_1447_);
lean_dec(v_t_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo(lean_object* v_aliasName_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1458_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1459_ = lean_st_ref_get(v___x_1458_);
v___x_1460_ = ((lean_object*)(l_Lean_Parser_getParserAliasInfo___closed__1));
v___x_1461_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v___x_1459_, v_aliasName_1456_, v___x_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo___boxed(lean_object* v_aliasName_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_Parser_getParserAliasInfo(v_aliasName_1463_);
lean_dec(v_aliasName_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(lean_object* v_00_u03b4_1466_, lean_object* v_t_1467_, lean_object* v_k_1468_, lean_object* v_fallback_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1467_, v_k_1468_, v_fallback_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___boxed(lean_object* v_00_u03b4_1471_, lean_object* v_t_1472_, lean_object* v_k_1473_, lean_object* v_fallback_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(v_00_u03b4_1471_, v_t_1472_, v_k_1473_, v_fallback_1474_);
lean_dec(v_fallback_1474_);
lean_dec(v_k_1473_);
lean_dec(v_t_1472_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object* v_aliasName_1476_, lean_object* v_declName_1477_, lean_object* v_p_1478_, lean_object* v_kind_x3f_1479_, lean_object* v_info_1480_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = l_Lean_Parser_parserAliasesRef;
lean_inc(v_aliasName_1476_);
v___x_1499_ = l_Lean_Parser_registerAliasCore___redArg(v___x_1498_, v_aliasName_1476_, v_p_1478_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_dec_ref_known(v___x_1499_, 1);
if (lean_obj_tag(v_kind_x3f_1479_) == 1)
{
lean_object* v_val_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_val_1500_ = lean_ctor_get(v_kind_x3f_1479_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v_kind_x3f_1479_, 1);
v___x_1501_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1502_ = lean_st_ref_take(v___x_1501_);
lean_inc(v_aliasName_1476_);
v___x_1503_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1476_, v_val_1500_, v___x_1502_);
v___x_1504_ = lean_st_ref_set(v___x_1501_, v___x_1503_);
goto v___jp_1482_;
}
else
{
lean_dec(v_kind_x3f_1479_);
goto v___jp_1482_;
}
}
else
{
lean_dec_ref(v_info_1480_);
lean_dec(v_kind_x3f_1479_);
lean_dec(v_declName_1477_);
lean_dec(v_aliasName_1476_);
return v___x_1499_;
}
v___jp_1482_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v_stackSz_x3f_1485_; uint8_t v_autoGroupArgs_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1496_; 
v___x_1483_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1484_ = lean_st_ref_take(v___x_1483_);
v_stackSz_x3f_1485_ = lean_ctor_get(v_info_1480_, 1);
v_autoGroupArgs_1486_ = lean_ctor_get_uint8(v_info_1480_, sizeof(void*)*2);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_info_1480_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v_info_1480_, 0);
lean_dec(v_unused_1497_);
v___x_1488_ = v_info_1480_;
v_isShared_1489_ = v_isSharedCheck_1496_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_stackSz_x3f_1485_);
lean_dec(v_info_1480_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1496_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v_declName_1477_);
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_declName_1477_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_stackSz_x3f_1485_);
lean_ctor_set_uint8(v_reuseFailAlloc_1495_, sizeof(void*)*2, v_autoGroupArgs_1486_);
v___x_1491_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1476_, v___x_1491_, v___x_1484_);
v___x_1493_ = lean_st_ref_set(v___x_1483_, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias___boxed(lean_object* v_aliasName_1505_, lean_object* v_declName_1506_, lean_object* v_p_1507_, lean_object* v_kind_x3f_1508_, lean_object* v_info_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_Parser_registerAlias(v_aliasName_1505_, v_declName_1506_, v_p_1507_, v_kind_x3f_1508_, v_info_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue___lam__0(lean_object* v_p_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_p_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0(lean_object* v_p_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_p_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0(lean_object* v_p_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1521_, 0, v_p_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object* v_aliasName_1524_){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1542_; 
v___x_1526_ = l_Lean_Parser_parserAliasesRef;
v___x_1527_ = l_Lean_Parser_getAlias___redArg(v___x_1526_, v_aliasName_1524_);
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1542_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1542_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
if (lean_obj_tag(v_a_1528_) == 1)
{
uint8_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
lean_dec_ref_known(v_a_1528_, 1);
v___x_1532_ = 1;
v___x_1533_ = lean_box(v___x_1532_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1533_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
else
{
uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
lean_dec(v_a_1528_);
v___x_1537_ = 0;
v___x_1538_ = lean_box(v___x_1537_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1538_);
v___x_1540_ = v___x_1530_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object* v_aliasName_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Parser_isParserAlias(v_aliasName_1543_);
lean_dec(v_aliasName_1543_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object* v_aliasName_1546_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1548_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1549_ = lean_st_ref_get(v___x_1548_);
v___x_1550_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1549_, v_aliasName_1546_);
lean_dec(v___x_1549_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f___boxed(lean_object* v_aliasName_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v_aliasName_1552_);
lean_dec(v_aliasName_1552_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object* v_aliasName_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = l_Lean_Parser_parserAliasesRef;
v___x_1558_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1557_, v_aliasName_1555_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1566_; 
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; 
v_unused_1567_ = lean_ctor_get(v___x_1558_, 0);
lean_dec(v_unused_1567_);
v___x_1560_ = v___x_1558_;
v_isShared_1561_ = v_isSharedCheck_1566_;
goto v_resetjp_1559_;
}
else
{
lean_dec(v___x_1558_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1566_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = lean_box(0);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1562_);
v___x_1564_ = v___x_1560_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
v_a_1568_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1558_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1558_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias___boxed(lean_object* v_aliasName_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_Parser_ensureUnaryParserAlias(v_aliasName_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object* v_aliasName_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = l_Lean_Parser_parserAliasesRef;
v___x_1582_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1581_, v_aliasName_1579_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1590_; 
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v___x_1582_, 0);
lean_dec(v_unused_1591_);
v___x_1584_ = v___x_1582_;
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v___x_1582_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = lean_box(0);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1586_);
v___x_1588_ = v___x_1584_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
v_a_1592_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1582_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1582_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias___boxed(lean_object* v_aliasName_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Parser_ensureBinaryParserAlias(v_aliasName_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object* v_aliasName_1603_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = l_Lean_Parser_parserAliasesRef;
v___x_1606_ = l_Lean_Parser_getConstAlias___redArg(v___x_1605_, v_aliasName_1603_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1614_; 
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v___x_1606_, 0);
lean_dec(v_unused_1615_);
v___x_1608_ = v___x_1606_;
v_isShared_1609_ = v_isSharedCheck_1614_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v___x_1606_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1614_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1610_ = lean_box(0);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1610_);
v___x_1612_ = v___x_1608_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v_a_1616_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1606_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1606_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias___boxed(lean_object* v_aliasName_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Parser_ensureConstantParserAlias(v_aliasName_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* v_constName_1635_, lean_object* v_compileParserDescr_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v_env_1648_; lean_object* v_opts_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; 
v_env_1648_ = lean_ctor_get(v_a_1637_, 0);
v_opts_1649_ = lean_ctor_get(v_a_1637_, 1);
v___x_1650_ = 0;
lean_inc(v_constName_1635_);
lean_inc_ref(v_env_1648_);
v___x_1651_ = l_Lean_Environment_find_x3f(v_env_1648_, v_constName_1635_, v___x_1650_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v___x_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec_ref(v_compileParserDescr_1636_);
v___x_1652_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_1653_ = 1;
v___x_1654_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1635_, v___x_1653_);
v___x_1655_ = lean_string_append(v___x_1652_, v___x_1654_);
lean_dec_ref(v___x_1654_);
v___x_1656_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_1657_ = lean_string_append(v___x_1655_, v___x_1656_);
v___x_1658_ = lean_mk_io_user_error(v___x_1657_);
v___x_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
else
{
lean_object* v_val_1660_; lean_object* v___x_1661_; 
v_val_1660_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_val_1660_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1661_ = l_Lean_ConstantInfo_type(v_val_1660_);
lean_dec(v_val_1660_);
if (lean_obj_tag(v___x_1661_) == 4)
{
lean_object* v_declName_1662_; 
v_declName_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_declName_1662_);
lean_dec_ref_known(v___x_1661_, 2);
if (lean_obj_tag(v_declName_1662_) == 1)
{
lean_object* v_pre_1663_; 
v_pre_1663_ = lean_ctor_get(v_declName_1662_, 0);
lean_inc(v_pre_1663_);
if (lean_obj_tag(v_pre_1663_) == 1)
{
lean_object* v_pre_1664_; 
v_pre_1664_ = lean_ctor_get(v_pre_1663_, 0);
switch(lean_obj_tag(v_pre_1664_))
{
case 1:
{
lean_object* v_pre_1665_; 
lean_inc_ref(v_pre_1664_);
lean_dec_ref(v_compileParserDescr_1636_);
v_pre_1665_ = lean_ctor_get(v_pre_1664_, 0);
if (lean_obj_tag(v_pre_1665_) == 0)
{
lean_object* v_str_1666_; lean_object* v_str_1667_; lean_object* v_str_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; 
v_str_1666_ = lean_ctor_get(v_declName_1662_, 1);
lean_inc_ref(v_str_1666_);
lean_dec_ref_known(v_declName_1662_, 2);
v_str_1667_ = lean_ctor_get(v_pre_1663_, 1);
lean_inc_ref(v_str_1667_);
lean_dec_ref_known(v_pre_1663_, 2);
v_str_1668_ = lean_ctor_get(v_pre_1664_, 1);
lean_inc_ref(v_str_1668_);
lean_dec_ref_known(v_pre_1664_, 2);
v___x_1669_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1670_ = lean_string_dec_eq(v_str_1668_, v___x_1669_);
lean_dec_ref(v_str_1668_);
if (v___x_1670_ == 0)
{
lean_dec_ref(v_str_1667_);
lean_dec_ref(v_str_1666_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1671_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_1672_ = lean_string_dec_eq(v_str_1667_, v___x_1671_);
lean_dec_ref(v_str_1667_);
if (v___x_1672_ == 0)
{
lean_dec_ref(v_str_1666_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_1674_ = lean_string_dec_eq(v_str_1666_, v___x_1673_);
if (v___x_1674_ == 0)
{
uint8_t v___x_1675_; 
v___x_1675_ = lean_string_dec_eq(v_str_1666_, v___x_1671_);
lean_dec_ref(v_str_1666_);
if (v___x_1675_ == 0)
{
goto v___jp_1639_;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = l_Lean_Environment_evalConst___redArg(v_env_1648_, v_opts_1649_, v_constName_1635_, v___x_1675_);
lean_dec(v_constName_1635_);
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
v___x_1682_ = lean_box(v___x_1675_);
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
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec_ref(v_str_1666_);
v___x_1696_ = l_Lean_Environment_evalConst___redArg(v_env_1648_, v_opts_1649_, v_constName_1635_, v___x_1674_);
lean_dec(v_constName_1635_);
v___x_1697_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1696_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1707_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1707_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1707_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1702_ = lean_box(v___x_1650_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v_a_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1703_);
v___x_1705_ = v___x_1700_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v_a_1708_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1697_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1697_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1664_, 2);
lean_dec_ref_known(v_pre_1663_, 2);
lean_dec_ref_known(v_declName_1662_, 2);
goto v___jp_1639_;
}
}
case 0:
{
lean_object* v_str_1716_; lean_object* v_str_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v_str_1716_ = lean_ctor_get(v_declName_1662_, 1);
lean_inc_ref(v_str_1716_);
lean_dec_ref_known(v_declName_1662_, 2);
v_str_1717_ = lean_ctor_get(v_pre_1663_, 1);
lean_inc_ref(v_str_1717_);
lean_dec_ref_known(v_pre_1663_, 2);
v___x_1718_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1719_ = lean_string_dec_eq(v_str_1717_, v___x_1718_);
lean_dec_ref(v_str_1717_);
if (v___x_1719_ == 0)
{
lean_dec_ref(v_str_1716_);
lean_dec_ref(v_compileParserDescr_1636_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1720_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_1721_ = lean_string_dec_eq(v_str_1716_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_1723_ = lean_string_dec_eq(v_str_1716_, v___x_1722_);
lean_dec_ref(v_str_1716_);
if (v___x_1723_ == 0)
{
lean_dec_ref(v_compileParserDescr_1636_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = l_Lean_Environment_evalConst___redArg(v_env_1648_, v_opts_1649_, v_constName_1635_, v___x_1723_);
lean_dec(v_constName_1635_);
v___x_1725_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1724_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
lean_inc_ref(v_a_1637_);
v___x_1727_ = lean_apply_3(v_compileParserDescr_1636_, v_a_1726_, v_a_1637_, lean_box(0));
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1737_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1732_ = lean_box(v___x_1650_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v_a_1728_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1733_);
v___x_1735_ = v___x_1730_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
v_a_1738_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1727_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1727_);
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
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec_ref(v_compileParserDescr_1636_);
v_a_1746_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1725_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1725_);
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
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec_ref(v_str_1716_);
v___x_1754_ = l_Lean_Environment_evalConst___redArg(v_env_1648_, v_opts_1649_, v_constName_1635_, v___x_1721_);
lean_dec(v_constName_1635_);
v___x_1755_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1754_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
lean_inc_ref(v_a_1637_);
v___x_1757_ = lean_apply_3(v_compileParserDescr_1636_, v_a_1756_, v_a_1637_, lean_box(0));
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1767_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1767_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1767_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1762_ = lean_box(v___x_1721_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v_a_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1763_);
v___x_1765_ = v___x_1760_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_a_1768_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1757_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1757_);
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
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec_ref(v_compileParserDescr_1636_);
v_a_1776_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1755_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1755_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_pre_1663_, 2);
lean_dec_ref_known(v_declName_1662_, 2);
lean_dec_ref(v_compileParserDescr_1636_);
goto v___jp_1639_;
}
}
}
else
{
lean_dec_ref_known(v_declName_1662_, 2);
lean_dec(v_pre_1663_);
lean_dec_ref(v_compileParserDescr_1636_);
goto v___jp_1639_;
}
}
else
{
lean_dec(v_declName_1662_);
lean_dec_ref(v_compileParserDescr_1636_);
goto v___jp_1639_;
}
}
else
{
lean_dec_ref(v___x_1661_);
lean_dec_ref(v_compileParserDescr_1636_);
goto v___jp_1639_;
}
}
v___jp_1639_:
{
lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1640_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__0));
v___x_1641_ = 1;
v___x_1642_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1635_, v___x_1641_);
v___x_1643_ = lean_string_append(v___x_1640_, v___x_1642_);
lean_dec_ref(v___x_1642_);
v___x_1644_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1));
v___x_1645_ = lean_string_append(v___x_1643_, v___x_1644_);
v___x_1646_ = lean_mk_io_user_error(v___x_1645_);
v___x_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object* v_constName_1784_, lean_object* v_compileParserDescr_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1784_, v_compileParserDescr_1785_, v_a_1786_);
lean_dec_ref(v_a_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed(lean_object* v_categories_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1789_, v_a_1790_, v_a_1791_);
lean_dec_ref(v_a_1791_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(lean_object* v_categories_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
switch(lean_obj_tag(v_a_1795_))
{
case 0:
{
lean_object* v_name_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
lean_dec_ref(v_categories_1794_);
v_name_1798_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_name_1798_);
lean_dec_ref_known(v_a_1795_, 1);
v___x_1799_ = l_Lean_Parser_parserAliasesRef;
v___x_1800_ = l_Lean_Parser_getConstAlias___redArg(v___x_1799_, v_name_1798_);
return v___x_1800_;
}
case 1:
{
lean_object* v_name_1801_; lean_object* v_p_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v_name_1801_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_name_1801_);
v_p_1802_ = lean_ctor_get(v_a_1795_, 1);
lean_inc_ref(v_p_1802_);
lean_dec_ref_known(v_a_1795_, 2);
v___x_1803_ = l_Lean_Parser_parserAliasesRef;
v___x_1804_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1803_, v_name_1801_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1806_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1806_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1794_, v_p_1802_, v_a_1796_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1815_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_apply_1(v_a_1805_, v_a_1807_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1811_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
lean_dec(v_a_1805_);
return v___x_1806_;
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec_ref(v_p_1802_);
lean_dec_ref(v_categories_1794_);
v_a_1816_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1804_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1804_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
case 2:
{
lean_object* v_name_1824_; lean_object* v_p_u2081_1825_; lean_object* v_p_u2082_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_name_1824_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_name_1824_);
v_p_u2081_1825_ = lean_ctor_get(v_a_1795_, 1);
lean_inc_ref(v_p_u2081_1825_);
v_p_u2082_1826_ = lean_ctor_get(v_a_1795_, 2);
lean_inc_ref(v_p_u2082_1826_);
lean_dec_ref_known(v_a_1795_, 3);
v___x_1827_ = l_Lean_Parser_parserAliasesRef;
v___x_1828_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1827_, v_name_1824_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1830_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
lean_inc_ref(v_categories_1794_);
v___x_1830_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1794_, v_p_u2081_1825_, v_a_1796_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1832_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1794_, v_p_u2082_1826_, v_a_1796_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1841_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1841_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1841_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1837_ = lean_apply_2(v_a_1829_, v_a_1831_, v_a_1833_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1837_);
v___x_1839_ = v___x_1835_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
else
{
lean_dec(v_a_1831_);
lean_dec(v_a_1829_);
return v___x_1832_;
}
}
else
{
lean_dec(v_a_1829_);
lean_dec_ref(v_p_u2082_1826_);
lean_dec_ref(v_categories_1794_);
return v___x_1830_;
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec_ref(v_p_u2082_1826_);
lean_dec_ref(v_p_u2081_1825_);
lean_dec_ref(v_categories_1794_);
v_a_1842_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1828_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1828_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
case 3:
{
lean_object* v_kind_1850_; lean_object* v_prec_1851_; lean_object* v_p_1852_; lean_object* v___x_1853_; 
v_kind_1850_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_kind_1850_);
v_prec_1851_ = lean_ctor_get(v_a_1795_, 1);
lean_inc(v_prec_1851_);
v_p_1852_ = lean_ctor_get(v_a_1795_, 2);
lean_inc_ref(v_p_1852_);
lean_dec_ref_known(v_a_1795_, 3);
v___x_1853_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1794_, v_p_1852_, v_a_1796_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1862_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1862_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1862_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1858_ = l_Lean_Parser_leadingNode(v_kind_1850_, v_prec_1851_, v_a_1854_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1858_);
v___x_1860_ = v___x_1856_;
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
else
{
lean_dec(v_prec_1851_);
lean_dec(v_kind_1850_);
return v___x_1853_;
}
}
case 4:
{
lean_object* v_kind_1863_; lean_object* v_prec_1864_; lean_object* v_lhsPrec_1865_; lean_object* v_p_1866_; lean_object* v___x_1867_; 
v_kind_1863_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_kind_1863_);
v_prec_1864_ = lean_ctor_get(v_a_1795_, 1);
lean_inc(v_prec_1864_);
v_lhsPrec_1865_ = lean_ctor_get(v_a_1795_, 2);
lean_inc(v_lhsPrec_1865_);
v_p_1866_ = lean_ctor_get(v_a_1795_, 3);
lean_inc_ref(v_p_1866_);
lean_dec_ref_known(v_a_1795_, 4);
v___x_1867_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1794_, v_p_1866_, v_a_1796_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1876_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1872_ = l_Lean_Parser_trailingNode(v_kind_1863_, v_prec_1864_, v_lhsPrec_1865_, v_a_1868_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1872_);
v___x_1874_ = v___x_1870_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
else
{
lean_dec(v_lhsPrec_1865_);
lean_dec(v_prec_1864_);
lean_dec(v_kind_1863_);
return v___x_1867_;
}
}
case 5:
{
lean_object* v_val_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1885_; 
lean_dec_ref(v_categories_1794_);
v_val_1877_ = lean_ctor_get(v_a_1795_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_a_1795_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1879_ = v_a_1795_;
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_val_1877_);
lean_dec(v_a_1795_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1885_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1881_ = l_Lean_Parser_symbol(v_val_1877_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 0);
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
case 6:
{
lean_object* v_val_1886_; uint8_t v_includeIdent_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec_ref(v_categories_1794_);
v_val_1886_ = lean_ctor_get(v_a_1795_, 0);
lean_inc_ref(v_val_1886_);
v_includeIdent_1887_ = lean_ctor_get_uint8(v_a_1795_, sizeof(void*)*1);
lean_dec_ref_known(v_a_1795_, 1);
v___x_1888_ = l_Lean_Parser_nonReservedSymbol(v_val_1886_, v_includeIdent_1887_);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
case 7:
{
lean_object* v_catName_1890_; lean_object* v_rbp_1891_; lean_object* v___x_1892_; 
v_catName_1890_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_catName_1890_);
v_rbp_1891_ = lean_ctor_get(v_a_1795_, 1);
lean_inc(v_rbp_1891_);
lean_dec_ref_known(v_a_1795_, 2);
v___x_1892_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_1794_, v_catName_1890_);
lean_dec_ref(v_categories_1794_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec(v_rbp_1891_);
v___x_1893_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_1890_);
v___x_1894_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1893_);
return v___x_1894_;
}
else
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1902_; 
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1892_, 0);
lean_dec(v_unused_1903_);
v___x_1896_ = v___x_1892_;
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v___x_1892_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = l_Lean_Parser_categoryParser(v_catName_1890_, v_rbp_1891_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
case 8:
{
lean_object* v_declName_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_declName_1904_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_declName_1904_);
lean_dec_ref_known(v_a_1795_, 1);
v___x_1905_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed), 4, 1);
lean_closure_set(v___x_1905_, 0, v_categories_1794_);
v___x_1906_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_declName_1904_, v___x_1905_, v_a_1796_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1915_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_snd_1911_; lean_object* v___x_1913_; 
v_snd_1911_ = lean_ctor_get(v_a_1907_, 1);
lean_inc(v_snd_1911_);
lean_dec(v_a_1907_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v_snd_1911_);
v___x_1913_ = v___x_1909_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_snd_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
v_a_1916_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1906_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1906_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
case 9:
{
lean_object* v_name_1924_; lean_object* v_kind_1925_; lean_object* v_p_1926_; lean_object* v___x_1927_; 
v_name_1924_ = lean_ctor_get(v_a_1795_, 0);
lean_inc_ref(v_name_1924_);
v_kind_1925_ = lean_ctor_get(v_a_1795_, 1);
lean_inc(v_kind_1925_);
v_p_1926_ = lean_ctor_get(v_a_1795_, 2);
lean_inc_ref(v_p_1926_);
lean_dec_ref_known(v_a_1795_, 3);
v___x_1927_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1794_, v_p_1926_, v_a_1796_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1938_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1938_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1938_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
uint8_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1932_ = 1;
lean_inc(v_kind_1925_);
v___x_1933_ = l_Lean_Parser_nodeWithAntiquot(v_name_1924_, v_kind_1925_, v_a_1928_, v___x_1932_);
v___x_1934_ = l_Lean_Parser_withCache(v_kind_1925_, v___x_1933_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1934_);
v___x_1936_ = v___x_1930_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
else
{
lean_dec(v_kind_1925_);
lean_dec_ref(v_name_1924_);
return v___x_1927_;
}
}
case 10:
{
lean_object* v_p_1939_; lean_object* v_sep_1940_; lean_object* v_psep_1941_; uint8_t v_allowTrailingSep_1942_; lean_object* v___x_1943_; 
v_p_1939_ = lean_ctor_get(v_a_1795_, 0);
lean_inc_ref(v_p_1939_);
v_sep_1940_ = lean_ctor_get(v_a_1795_, 1);
lean_inc_ref(v_sep_1940_);
v_psep_1941_ = lean_ctor_get(v_a_1795_, 2);
lean_inc_ref(v_psep_1941_);
v_allowTrailingSep_1942_ = lean_ctor_get_uint8(v_a_1795_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1795_, 3);
lean_inc_ref(v_categories_1794_);
v___x_1943_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1794_, v_p_1939_, v_a_1796_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1945_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v___x_1945_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1794_, v_psep_1941_, v_a_1796_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1954_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1954_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1954_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1950_ = l_Lean_Parser_sepBy(v_a_1944_, v_sep_1940_, v_a_1946_, v_allowTrailingSep_1942_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1950_);
v___x_1952_ = v___x_1948_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
else
{
lean_dec(v_a_1944_);
lean_dec_ref(v_sep_1940_);
return v___x_1945_;
}
}
else
{
lean_dec_ref(v_psep_1941_);
lean_dec_ref(v_sep_1940_);
lean_dec_ref(v_categories_1794_);
return v___x_1943_;
}
}
case 11:
{
lean_object* v_p_1955_; lean_object* v_sep_1956_; lean_object* v_psep_1957_; uint8_t v_allowTrailingSep_1958_; lean_object* v___x_1959_; 
v_p_1955_ = lean_ctor_get(v_a_1795_, 0);
lean_inc_ref(v_p_1955_);
v_sep_1956_ = lean_ctor_get(v_a_1795_, 1);
lean_inc_ref(v_sep_1956_);
v_psep_1957_ = lean_ctor_get(v_a_1795_, 2);
lean_inc_ref(v_psep_1957_);
v_allowTrailingSep_1958_ = lean_ctor_get_uint8(v_a_1795_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1795_, 3);
lean_inc_ref(v_categories_1794_);
v___x_1959_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1794_, v_p_1955_, v_a_1796_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1961_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1959_, 1);
v___x_1961_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1794_, v_psep_1957_, v_a_1796_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1970_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1966_ = l_Lean_Parser_sepBy1(v_a_1960_, v_sep_1956_, v_a_1962_, v_allowTrailingSep_1958_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1966_);
v___x_1968_ = v___x_1964_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
else
{
lean_dec(v_a_1960_);
lean_dec_ref(v_sep_1956_);
return v___x_1961_;
}
}
else
{
lean_dec_ref(v_psep_1957_);
lean_dec_ref(v_sep_1956_);
lean_dec_ref(v_categories_1794_);
return v___x_1959_;
}
}
default: 
{
lean_object* v_val_1971_; lean_object* v_asciiVal_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec_ref(v_categories_1794_);
v_val_1971_ = lean_ctor_get(v_a_1795_, 0);
lean_inc_ref(v_val_1971_);
v_asciiVal_1972_ = lean_ctor_get(v_a_1795_, 1);
lean_inc_ref(v_asciiVal_1972_);
lean_dec_ref_known(v_a_1795_, 2);
v___x_1973_ = l_Lean_Parser_unicodeSymbol___redArg(v_val_1971_, v_asciiVal_1972_);
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
return v___x_1974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object* v_categories_1975_, lean_object* v_d_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1975_, v_d_1976_, v_a_1977_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object* v_categories_1980_, lean_object* v_d_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Parser_compileParserDescr(v_categories_1980_, v_d_1981_, v_a_1982_);
lean_dec_ref(v_a_1982_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0(lean_object* v_categories_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1985_, v___y_1986_, v___y_1987_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0___boxed(lean_object* v_categories_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_Parser_mkParserOfConstant___lam__0(v_categories_1990_, v___y_1991_, v___y_1992_);
lean_dec_ref(v___y_1992_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* v_categories_1995_, lean_object* v_constName_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v___f_1999_; lean_object* v___x_2000_; 
v___f_1999_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserOfConstant___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1999_, 0, v_categories_1995_);
v___x_2000_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1996_, v___f_1999_, v_a_1997_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___boxed(lean_object* v_categories_2001_, lean_object* v_constName_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Parser_mkParserOfConstant(v_categories_2001_, v_constName_2002_, v_a_2003_);
lean_dec_ref(v_a_2003_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_st_mk_ref(v___x_2007_);
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object* v_hook_2012_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2014_ = l_Lean_Parser_parserAttributeHooks;
v___x_2015_ = lean_st_ref_take(v___x_2014_);
v___x_2016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2016_, 0, v_hook_2012_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = lean_st_ref_set(v___x_2014_, v___x_2016_);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook___boxed(lean_object* v_hook_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_Parser_registerParserAttributeHook(v_hook_2019_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(lean_object* v_catName_2022_, lean_object* v_declName_2023_, uint8_t v_builtin_2024_, lean_object* v_as_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
if (lean_obj_tag(v_as_2025_) == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_dec(v_declName_2023_);
lean_dec(v_catName_2022_);
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
else
{
lean_object* v_head_2031_; lean_object* v_tail_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_head_2031_ = lean_ctor_get(v_as_2025_, 0);
lean_inc(v_head_2031_);
v_tail_2032_ = lean_ctor_get(v_as_2025_, 1);
lean_inc(v_tail_2032_);
lean_dec_ref_known(v_as_2025_, 2);
v___x_2033_ = lean_box(v_builtin_2024_);
lean_inc(v___y_2027_);
lean_inc_ref(v___y_2026_);
lean_inc(v_declName_2023_);
lean_inc(v_catName_2022_);
v___x_2034_ = lean_apply_6(v_head_2031_, v_catName_2022_, v_declName_2023_, v___x_2033_, v___y_2026_, v___y_2027_, lean_box(0));
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_dec_ref_known(v___x_2034_, 1);
v_as_2025_ = v_tail_2032_;
goto _start;
}
else
{
lean_dec(v_tail_2032_);
lean_dec(v_declName_2023_);
lean_dec(v_catName_2022_);
return v___x_2034_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0___boxed(lean_object* v_catName_2036_, lean_object* v_declName_2037_, lean_object* v_builtin_2038_, lean_object* v_as_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
uint8_t v_builtin_boxed_2043_; lean_object* v_res_2044_; 
v_builtin_boxed_2043_ = lean_unbox(v_builtin_2038_);
v_res_2044_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2036_, v_declName_2037_, v_builtin_boxed_2043_, v_as_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object* v_catName_2045_, lean_object* v_declName_2046_, uint8_t v_builtin_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2051_ = l_Lean_Parser_parserAttributeHooks;
v___x_2052_ = lean_st_ref_get(v___x_2051_);
v___x_2053_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2045_, v_declName_2046_, v_builtin_2047_, v___x_2052_, v_a_2048_, v_a_2049_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object* v_catName_2054_, lean_object* v_declName_2055_, lean_object* v_builtin_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
uint8_t v_builtin_boxed_2060_; lean_object* v_res_2061_; 
v_builtin_boxed_2060_ = lean_unbox(v_builtin_2056_);
v_res_2061_ = l_Lean_Parser_runParserAttributeHooks(v_catName_2054_, v_declName_2055_, v_builtin_boxed_2060_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2062_, lean_object* v_decl_2063_, lean_object* v_stx_2064_, uint8_t v_x_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2064_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2069_) == 0)
{
uint8_t v___x_2070_; lean_object* v___x_2071_; 
lean_dec_ref_known(v___x_2069_, 1);
v___x_2070_ = 1;
v___x_2071_ = l_Lean_Parser_runParserAttributeHooks(v___x_2062_, v_decl_2063_, v___x_2070_, v___y_2066_, v___y_2067_);
return v___x_2071_;
}
else
{
lean_dec(v_decl_2063_);
lean_dec(v___x_2062_);
return v___x_2069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2072_, lean_object* v_decl_2073_, lean_object* v_stx_2074_, lean_object* v_x_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
uint8_t v_x_1064__boxed_2079_; lean_object* v_res_2080_; 
v_x_1064__boxed_2079_ = lean_unbox(v_x_2075_);
v_res_2080_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2072_, v_decl_2073_, v_stx_2074_, v_x_1064__boxed_2079_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
return v_res_2080_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2084_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2085_ = lean_unsigned_to_nat(0u);
v___x_2086_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
lean_ctor_set(v___x_2086_, 2, v___x_2085_);
lean_ctor_set(v___x_2086_, 3, v___x_2085_);
lean_ctor_set(v___x_2086_, 4, v___x_2084_);
lean_ctor_set(v___x_2086_, 5, v___x_2084_);
lean_ctor_set(v___x_2086_, 6, v___x_2084_);
lean_ctor_set(v___x_2086_, 7, v___x_2084_);
lean_ctor_set(v___x_2086_, 8, v___x_2084_);
lean_ctor_set(v___x_2086_, 9, v___x_2084_);
return v___x_2086_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = lean_unsigned_to_nat(32u);
v___x_2088_ = lean_mk_empty_array_with_capacity(v___x_2087_);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
return v___x_2089_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2090_ = ((size_t)5ULL);
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_unsigned_to_nat(32u);
v___x_2093_ = lean_mk_empty_array_with_capacity(v___x_2092_);
v___x_2094_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2095_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set(v___x_2095_, 1, v___x_2093_);
lean_ctor_set(v___x_2095_, 2, v___x_2091_);
lean_ctor_set(v___x_2095_, 3, v___x_2091_);
lean_ctor_set_usize(v___x_2095_, 4, v___x_2090_);
return v___x_2095_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2096_ = lean_box(1);
v___x_2097_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_2098_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2099_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v___x_2097_);
lean_ctor_set(v___x_2099_, 2, v___x_2096_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; lean_object* v_env_2105_; lean_object* v_options_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2104_ = lean_st_ref_get(v___y_2102_);
v_env_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc_ref(v_env_2105_);
lean_dec(v___x_2104_);
v_options_2106_ = lean_ctor_get(v___y_2101_, 2);
v___x_2107_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_2108_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2106_);
v___x_2109_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2109_, 0, v_env_2105_);
lean_ctor_set(v___x_2109_, 1, v___x_2107_);
lean_ctor_set(v___x_2109_, 2, v___x_2108_);
lean_ctor_set(v___x_2109_, 3, v_options_2106_);
v___x_2110_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v_msgData_2100_);
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_ref_2121_; lean_object* v___x_2122_; lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2131_; 
v_ref_2121_ = lean_ctor_get(v___y_2118_, 5);
v___x_2122_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msg_2117_, v___y_2118_, v___y_2119_);
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2125_ = v___x_2122_;
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2122_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
lean_inc(v_ref_2121_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v_ref_2121_);
lean_ctor_set(v___x_2127_, 1, v_a_2123_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set_tag(v___x_2125_, 1);
lean_ctor_set(v___x_2125_, 0, v___x_2127_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
return v_res_2136_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2142_ = l_Lean_stringToMessageData(v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2143_, lean_object* v_decl_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2148_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2149_ = l_Lean_MessageData_ofName(v___x_2143_);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2152_, v___y_2145_, v___y_2146_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2154_, lean_object* v_decl_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2154_, v_decl_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v_decl_2155_);
return v_res_2159_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_unsigned_to_nat(3646333153u);
v___x_2203_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2204_ = l_Lean_Name_num___override(v___x_2203_, v___x_2202_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2206_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2207_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2208_ = l_Lean_Name_str___override(v___x_2207_, v___x_2206_);
return v___x_2208_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2211_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2212_ = l_Lean_Name_str___override(v___x_2211_, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = lean_unsigned_to_nat(2u);
v___x_2214_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2215_ = l_Lean_Name_num___override(v___x_2214_, v___x_2213_);
return v___x_2215_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2222_ = 0;
v___x_2223_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2224_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2225_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2226_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v___x_2224_);
lean_ctor_set(v___x_2226_, 2, v___x_2223_);
lean_ctor_set_uint8(v___x_2226_, sizeof(void*)*3, v___x_2222_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2227_; lean_object* v___f_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___f_2227_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___f_2228_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2229_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v___f_2228_);
lean_ctor_set(v___x_2230_, 2, v___f_2227_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2233_ = l_Lean_registerBuiltinAttribute(v___x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v_a_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2236_, lean_object* v_msg_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2237_, v___y_2238_, v___y_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2242_, lean_object* v_msg_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(v_00_u03b1_2242_, v_msg_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2248_, lean_object* v_decl_2249_, lean_object* v_stx_2250_, uint8_t v_x_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2250_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2255_) == 0)
{
uint8_t v___x_2256_; lean_object* v___x_2257_; 
lean_dec_ref_known(v___x_2255_, 1);
v___x_2256_ = 0;
v___x_2257_ = l_Lean_Parser_runParserAttributeHooks(v___x_2248_, v_decl_2249_, v___x_2256_, v___y_2252_, v___y_2253_);
return v___x_2257_;
}
else
{
lean_dec(v_decl_2249_);
lean_dec(v___x_2248_);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2258_, lean_object* v_decl_2259_, lean_object* v_stx_2260_, lean_object* v_x_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
uint8_t v_x_211__boxed_2265_; lean_object* v_res_2266_; 
v_x_211__boxed_2265_ = lean_unbox(v_x_2261_);
v_res_2266_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2258_, v_decl_2259_, v_stx_2260_, v_x_211__boxed_2265_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2267_, lean_object* v_decl_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2272_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2273_ = l_Lean_MessageData_ofName(v___x_2267_);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2276_, v___y_2269_, v___y_2270_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2278_, lean_object* v_decl_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2278_, v_decl_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v_decl_2279_);
return v_res_2283_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_unsigned_to_nat(3789407938u);
v___x_2287_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2288_ = l_Lean_Name_num___override(v___x_2287_, v___x_2286_);
return v___x_2288_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2290_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2291_ = l_Lean_Name_str___override(v___x_2290_, v___x_2289_);
return v___x_2291_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2293_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2294_ = l_Lean_Name_str___override(v___x_2293_, v___x_2292_);
return v___x_2294_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2295_ = lean_unsigned_to_nat(2u);
v___x_2296_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2297_ = l_Lean_Name_num___override(v___x_2296_, v___x_2295_);
return v___x_2297_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2304_ = 0;
v___x_2305_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2306_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2307_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2308_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v___x_2306_);
lean_ctor_set(v___x_2308_, 2, v___x_2305_);
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*3, v___x_2304_);
return v___x_2308_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2309_; lean_object* v___f_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___f_2309_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___f_2310_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2311_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v___f_2310_);
lean_ctor_set(v___x_2312_, 2, v___f_2309_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2315_ = l_Lean_registerBuiltinAttribute(v___x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v_a_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object* v_s_2318_, lean_object* v_x_2319_, lean_object* v_a_2320_){
_start:
{
switch(lean_obj_tag(v_x_2319_))
{
case 0:
{
lean_object* v_val_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v_s_2318_);
v_val_2322_ = lean_ctor_get(v_x_2319_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_x_2319_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2324_ = v_x_2319_;
v_isShared_2325_ = v_isSharedCheck_2330_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_val_2322_);
lean_dec(v_x_2319_);
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
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_val_2322_);
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
case 1:
{
lean_object* v_val_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_s_2318_);
v_val_2331_ = lean_ctor_get(v_x_2319_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_x_2319_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2333_ = v_x_2319_;
v_isShared_2334_ = v_isSharedCheck_2339_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_val_2331_);
lean_dec(v_x_2319_);
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
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
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
case 2:
{
lean_object* v_catName_2340_; lean_object* v_declName_2341_; uint8_t v_behavior_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v_s_2318_);
v_catName_2340_ = lean_ctor_get(v_x_2319_, 0);
v_declName_2341_ = lean_ctor_get(v_x_2319_, 1);
v_behavior_2342_ = lean_ctor_get_uint8(v_x_2319_, sizeof(void*)*2);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_x_2319_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2344_ = v_x_2319_;
v_isShared_2345_ = v_isSharedCheck_2350_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_declName_2341_);
lean_inc(v_catName_2340_);
lean_dec(v_x_2319_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2350_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_catName_2340_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_declName_2341_);
lean_ctor_set_uint8(v_reuseFailAlloc_2349_, sizeof(void*)*2, v_behavior_2342_);
v___x_2347_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
return v___x_2348_;
}
}
}
default: 
{
lean_object* v_catName_2351_; lean_object* v_declName_2352_; lean_object* v_prio_2353_; lean_object* v_categories_2354_; lean_object* v___x_2355_; 
v_catName_2351_ = lean_ctor_get(v_x_2319_, 0);
lean_inc(v_catName_2351_);
v_declName_2352_ = lean_ctor_get(v_x_2319_, 1);
lean_inc_n(v_declName_2352_, 2);
v_prio_2353_ = lean_ctor_get(v_x_2319_, 2);
lean_inc(v_prio_2353_);
lean_dec_ref_known(v_x_2319_, 3);
v_categories_2354_ = lean_ctor_get(v_s_2318_, 2);
lean_inc_ref(v_categories_2354_);
lean_dec_ref(v_s_2318_);
v___x_2355_ = l_Lean_Parser_mkParserOfConstant(v_categories_2354_, v_declName_2352_, v_a_2320_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2367_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2367_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2367_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v_fst_2360_; lean_object* v_snd_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; lean_object* v___x_2365_; 
v_fst_2360_ = lean_ctor_get(v_a_2356_, 0);
lean_inc(v_fst_2360_);
v_snd_2361_ = lean_ctor_get(v_a_2356_, 1);
lean_inc(v_snd_2361_);
lean_dec(v_a_2356_);
v___x_2362_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_2362_, 0, v_catName_2351_);
lean_ctor_set(v___x_2362_, 1, v_declName_2352_);
lean_ctor_set(v___x_2362_, 2, v_snd_2361_);
lean_ctor_set(v___x_2362_, 3, v_prio_2353_);
v___x_2363_ = lean_unbox(v_fst_2360_);
lean_dec(v_fst_2360_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*4, v___x_2363_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2362_);
v___x_2365_ = v___x_2358_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2362_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_prio_2353_);
lean_dec(v_declName_2352_);
lean_dec(v_catName_2351_);
v_a_2368_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2355_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2355_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object* v_s_2376_, lean_object* v_x_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(v_s_2376_, v_x_2377_, v_a_2378_);
lean_dec_ref(v_a_2378_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v_x_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2383_, 0, v_a_2382_);
lean_inc_ref_n(v___x_2383_, 2);
v___x_2384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
lean_ctor_set(v___x_2384_, 2, v___x_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_x_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v_x_2385_, v_a_2386_);
lean_dec_ref(v_x_2385_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v___y_2388_){
_start:
{
lean_inc_ref(v___y_2388_);
return v___y_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v___y_2389_);
lean_dec_ref(v___y_2389_);
return v_res_2390_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2401_; lean_object* v___f_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___f_2401_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___f_2402_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2403_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2404_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2405_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2406_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed), 1, 0);
v___x_2407_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2408_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
lean_ctor_set(v___x_2408_, 1, v___x_2406_);
lean_ctor_set(v___x_2408_, 2, v___x_2405_);
lean_ctor_set(v___x_2408_, 3, v___x_2404_);
lean_ctor_set(v___x_2408_, 4, v___x_2403_);
lean_ctor_set(v___x_2408_, 5, v___f_2402_);
lean_ctor_set(v___x_2408_, 6, v___f_2401_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_);
v___x_2411_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object* v_env_2414_, lean_object* v_catName_2415_){
_start:
{
lean_object* v___x_2416_; lean_object* v_ext_2417_; lean_object* v_toEnvExtension_2418_; lean_object* v_asyncMode_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v_categories_2422_; lean_object* v___x_2423_; 
v___x_2416_ = l_Lean_Parser_parserExtension;
v_ext_2417_ = lean_ctor_get(v___x_2416_, 1);
v_toEnvExtension_2418_ = lean_ctor_get(v_ext_2417_, 0);
v_asyncMode_2419_ = lean_ctor_get(v_toEnvExtension_2418_, 2);
v___x_2420_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2421_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2420_, v___x_2416_, v_env_2414_, v_asyncMode_2419_);
v_categories_2422_ = lean_ctor_get(v___x_2421_, 2);
lean_inc_ref(v_categories_2422_);
lean_dec(v___x_2421_);
v___x_2423_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2422_, v_catName_2415_);
lean_dec_ref(v_categories_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object* v_env_2424_, lean_object* v_catName_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Parser_getParserCategory_x3f(v_env_2424_, v_catName_2425_);
lean_dec(v_catName_2425_);
return v_res_2426_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object* v_env_2427_, lean_object* v_catName_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_Parser_getParserCategory_x3f(v_env_2427_, v_catName_2428_);
if (lean_obj_tag(v___x_2429_) == 0)
{
uint8_t v___x_2430_; 
v___x_2430_ = 0;
return v___x_2430_;
}
else
{
uint8_t v___x_2431_; 
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = 1;
return v___x_2431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object* v_env_2432_, lean_object* v_catName_2433_){
_start:
{
uint8_t v_res_2434_; lean_object* v_r_2435_; 
v_res_2434_ = l_Lean_Parser_isParserCategory(v_env_2432_, v_catName_2433_);
lean_dec(v_catName_2433_);
v_r_2435_ = lean_box(v_res_2434_);
return v_r_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object* v_env_2436_, lean_object* v_catName_2437_, lean_object* v_declName_2438_, uint8_t v_behavior_2439_){
_start:
{
uint8_t v___x_2440_; 
lean_inc_ref(v_env_2436_);
v___x_2440_ = l_Lean_Parser_isParserCategory(v_env_2436_, v_catName_2437_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2441_ = l_Lean_Parser_parserExtension;
v___x_2442_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2442_, 0, v_catName_2437_);
lean_ctor_set(v___x_2442_, 1, v_declName_2438_);
lean_ctor_set_uint8(v___x_2442_, sizeof(void*)*2, v_behavior_2439_);
v___x_2443_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2441_, v_env_2436_, v___x_2442_);
v___x_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
return v___x_2444_;
}
else
{
lean_object* v___x_2445_; 
lean_dec(v_declName_2438_);
lean_dec_ref(v_env_2436_);
v___x_2445_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_2437_);
return v___x_2445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* v_env_2446_, lean_object* v_catName_2447_, lean_object* v_declName_2448_, lean_object* v_behavior_2449_){
_start:
{
uint8_t v_behavior_boxed_2450_; lean_object* v_res_2451_; 
v_behavior_boxed_2450_ = lean_unbox(v_behavior_2449_);
v_res_2451_ = l_Lean_Parser_addParserCategory(v_env_2446_, v_catName_2447_, v_declName_2448_, v_behavior_boxed_2450_);
return v_res_2451_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object* v_env_2452_, lean_object* v_catName_2453_){
_start:
{
lean_object* v___x_2454_; lean_object* v_ext_2455_; lean_object* v_toEnvExtension_2456_; lean_object* v_asyncMode_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_categories_2460_; lean_object* v___x_2461_; 
v___x_2454_ = l_Lean_Parser_parserExtension;
v_ext_2455_ = lean_ctor_get(v___x_2454_, 1);
v_toEnvExtension_2456_ = lean_ctor_get(v_ext_2455_, 0);
v_asyncMode_2457_ = lean_ctor_get(v_toEnvExtension_2456_, 2);
v___x_2458_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2459_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2458_, v___x_2454_, v_env_2452_, v_asyncMode_2457_);
v_categories_2460_ = lean_ctor_get(v___x_2459_, 2);
lean_inc_ref(v_categories_2460_);
lean_dec(v___x_2459_);
v___x_2461_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2460_, v_catName_2453_);
lean_dec_ref(v_categories_2460_);
if (lean_obj_tag(v___x_2461_) == 0)
{
uint8_t v___x_2462_; 
v___x_2462_ = 0;
return v___x_2462_;
}
else
{
lean_object* v_val_2463_; uint8_t v_behavior_2464_; 
v_val_2463_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_val_2463_);
lean_dec_ref_known(v___x_2461_, 1);
v_behavior_2464_ = lean_ctor_get_uint8(v_val_2463_, sizeof(void*)*3);
lean_dec(v_val_2463_);
return v_behavior_2464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object* v_env_2465_, lean_object* v_catName_2466_){
_start:
{
uint8_t v_res_2467_; lean_object* v_r_2468_; 
v_res_2467_ = l_Lean_Parser_leadingIdentBehavior(v_env_2465_, v_catName_2466_);
lean_dec(v_catName_2466_);
v_r_2468_ = lean_box(v_res_2467_);
return v_r_2468_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(lean_object* v_x_2469_, lean_object* v_x_2470_){
_start:
{
if (lean_obj_tag(v_x_2470_) == 0)
{
return v_x_2469_;
}
else
{
lean_object* v_head_2471_; lean_object* v_tail_2472_; lean_object* v___x_2473_; 
v_head_2471_ = lean_ctor_get(v_x_2470_, 0);
lean_inc_n(v_head_2471_, 2);
v_tail_2472_ = lean_ctor_get(v_x_2470_, 1);
lean_inc(v_tail_2472_);
lean_dec_ref_known(v_x_2470_, 2);
v___x_2473_ = l_Lean_Data_Trie_insert___redArg(v_x_2469_, v_head_2471_, v_head_2471_);
lean_dec(v_head_2471_);
v_x_2469_ = v___x_2473_;
v_x_2470_ = v_tail_2472_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__0(lean_object* v_info_2475_, lean_object* v_ctx_2476_){
_start:
{
lean_object* v_toInputContext_2477_; lean_object* v_toParserModuleContext_2478_; lean_object* v_toCacheableParserContext_2479_; lean_object* v_tokens_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2491_; 
v_toInputContext_2477_ = lean_ctor_get(v_ctx_2476_, 0);
v_toParserModuleContext_2478_ = lean_ctor_get(v_ctx_2476_, 1);
v_toCacheableParserContext_2479_ = lean_ctor_get(v_ctx_2476_, 2);
v_tokens_2480_ = lean_ctor_get(v_ctx_2476_, 3);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_ctx_2476_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2482_ = v_ctx_2476_;
v_isShared_2483_ = v_isSharedCheck_2491_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_tokens_2480_);
lean_inc(v_toCacheableParserContext_2479_);
lean_inc(v_toParserModuleContext_2478_);
lean_inc(v_toInputContext_2477_);
lean_dec(v_ctx_2476_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2491_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v_collectTokens_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2489_; 
v_collectTokens_2484_ = lean_ctor_get(v_info_2475_, 0);
lean_inc_ref(v_collectTokens_2484_);
lean_dec_ref(v_info_2475_);
v___x_2485_ = lean_box(0);
v___x_2486_ = lean_apply_1(v_collectTokens_2484_, v___x_2485_);
v___x_2487_ = l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(v_tokens_2480_, v___x_2486_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 3, v___x_2487_);
v___x_2489_ = v___x_2482_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_toInputContext_2477_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_toParserModuleContext_2478_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_toCacheableParserContext_2479_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1(lean_object* v_categories_2492_, lean_object* v_declName_2493_, lean_object* v___x_2494_, lean_object* v_ctx_2495_, lean_object* v_s_2496_, lean_object* v_evalFallback_x3f_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_Parser_mkParserOfConstant(v_categories_2492_, v_declName_2493_, v___x_2494_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v_snd_2501_; lean_object* v_info_2502_; lean_object* v_fn_2503_; lean_object* v___f_2504_; lean_object* v___x_2505_; 
lean_dec(v_evalFallback_x3f_2497_);
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v_snd_2501_ = lean_ctor_get(v_a_2500_, 1);
lean_inc(v_snd_2501_);
lean_dec(v_a_2500_);
v_info_2502_ = lean_ctor_get(v_snd_2501_, 0);
lean_inc_ref(v_info_2502_);
v_fn_2503_ = lean_ctor_get(v_snd_2501_, 1);
lean_inc_ref(v_fn_2503_);
lean_dec(v_snd_2501_);
v___f_2504_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__0), 2, 1);
lean_closure_set(v___f_2504_, 0, v_info_2502_);
v___x_2505_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2504_, v_fn_2503_, v_ctx_2495_, v_s_2496_);
return v___x_2505_;
}
else
{
if (lean_obj_tag(v_evalFallback_x3f_2497_) == 1)
{
lean_object* v_val_2506_; lean_object* v___x_2507_; 
lean_dec_ref_known(v___x_2499_, 1);
v_val_2506_ = lean_ctor_get(v_evalFallback_x3f_2497_, 0);
lean_inc(v_val_2506_);
lean_dec_ref_known(v_evalFallback_x3f_2497_, 1);
v___x_2507_ = lean_apply_2(v_val_2506_, v_ctx_2495_, v_s_2496_);
return v___x_2507_;
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; 
lean_dec(v_evalFallback_x3f_2497_);
lean_dec_ref(v_ctx_2495_);
v_a_2508_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2509_ = lean_io_error_to_string(v_a_2508_);
v___x_2510_ = lean_box(0);
v___x_2511_ = 1;
v___x_2512_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2496_, v___x_2509_, v___x_2510_, v___x_2511_);
return v___x_2512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed(lean_object* v_categories_2513_, lean_object* v_declName_2514_, lean_object* v___x_2515_, lean_object* v_ctx_2516_, lean_object* v_s_2517_, lean_object* v_evalFallback_x3f_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Lean_Parser_evalParserConstUnsafe___lam__1(v_categories_2513_, v_declName_2514_, v___x_2515_, v_ctx_2516_, v_s_2517_, v_evalFallback_x3f_2518_);
lean_dec_ref(v___x_2515_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* v_declName_2521_, lean_object* v_evalFallback_x3f_2522_, lean_object* v_ctx_2523_, lean_object* v_s_2524_){
_start:
{
lean_object* v_toParserModuleContext_2525_; lean_object* v_env_2526_; lean_object* v_options_2527_; lean_object* v___x_2528_; lean_object* v_ext_2529_; lean_object* v_toEnvExtension_2530_; lean_object* v_asyncMode_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v_categories_2534_; lean_object* v___x_2535_; lean_object* v___f_2536_; lean_object* v___x_2537_; 
v_toParserModuleContext_2525_ = lean_ctor_get(v_ctx_2523_, 1);
v_env_2526_ = lean_ctor_get(v_toParserModuleContext_2525_, 0);
v_options_2527_ = lean_ctor_get(v_toParserModuleContext_2525_, 1);
v___x_2528_ = l_Lean_Parser_parserExtension;
v_ext_2529_ = lean_ctor_get(v___x_2528_, 1);
v_toEnvExtension_2530_ = lean_ctor_get(v_ext_2529_, 0);
v_asyncMode_2531_ = lean_ctor_get(v_toEnvExtension_2530_, 2);
v___x_2532_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref_n(v_env_2526_, 2);
v___x_2533_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2532_, v___x_2528_, v_env_2526_, v_asyncMode_2531_);
v_categories_2534_ = lean_ctor_get(v___x_2533_, 2);
lean_inc_ref(v_categories_2534_);
lean_dec(v___x_2533_);
lean_inc_ref(v_options_2527_);
v___x_2535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2535_, 0, v_env_2526_);
lean_ctor_set(v___x_2535_, 1, v_options_2527_);
v___f_2536_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2536_, 0, v_categories_2534_);
lean_closure_set(v___f_2536_, 1, v_declName_2521_);
lean_closure_set(v___f_2536_, 2, v___x_2535_);
lean_closure_set(v___f_2536_, 3, v_ctx_2523_);
lean_closure_set(v___f_2536_, 4, v_s_2524_);
lean_closure_set(v___f_2536_, 5, v_evalFallback_x3f_2522_);
v___x_2537_ = l_unsafeBaseIO___redArg(v___f_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object* v_name_2538_, lean_object* v_decl_2539_, lean_object* v_ref_2540_){
_start:
{
lean_object* v_defValue_2542_; lean_object* v_descr_2543_; lean_object* v_deprecation_x3f_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v_defValue_2542_ = lean_ctor_get(v_decl_2539_, 0);
v_descr_2543_ = lean_ctor_get(v_decl_2539_, 1);
v_deprecation_x3f_2544_ = lean_ctor_get(v_decl_2539_, 2);
v___x_2545_ = lean_alloc_ctor(1, 0, 1);
v___x_2546_ = lean_unbox(v_defValue_2542_);
lean_ctor_set_uint8(v___x_2545_, 0, v___x_2546_);
lean_inc(v_deprecation_x3f_2544_);
lean_inc_ref(v_descr_2543_);
lean_inc_n(v_name_2538_, 2);
v___x_2547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2547_, 0, v_name_2538_);
lean_ctor_set(v___x_2547_, 1, v_ref_2540_);
lean_ctor_set(v___x_2547_, 2, v___x_2545_);
lean_ctor_set(v___x_2547_, 3, v_descr_2543_);
lean_ctor_set(v___x_2547_, 4, v_deprecation_x3f_2544_);
v___x_2548_ = lean_register_option(v_name_2538_, v___x_2547_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2556_; 
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2556_ == 0)
{
lean_object* v_unused_2557_; 
v_unused_2557_ = lean_ctor_get(v___x_2548_, 0);
lean_dec(v_unused_2557_);
v___x_2550_ = v___x_2548_;
v_isShared_2551_ = v_isSharedCheck_2556_;
goto v_resetjp_2549_;
}
else
{
lean_dec(v___x_2548_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2556_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2554_; 
lean_inc(v_defValue_2542_);
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v_name_2538_);
lean_ctor_set(v___x_2552_, 1, v_defValue_2542_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2552_);
v___x_2554_ = v___x_2550_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v_name_2538_);
v_a_2558_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2548_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2548_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2566_, lean_object* v_decl_2567_, lean_object* v_ref_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v_name_2566_, v_decl_2567_, v_ref_2568_);
lean_dec_ref(v_decl_2567_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2588_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2589_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2590_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2591_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v___x_2588_, v___x_2589_, v___x_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object* v_a_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(lean_object* v_o_2597_, lean_object* v_k_2598_, uint8_t v_v_2599_){
_start:
{
lean_object* v_map_2600_; uint8_t v_hasTrace_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2615_; 
v_map_2600_ = lean_ctor_get(v_o_2597_, 0);
v_hasTrace_2601_ = lean_ctor_get_uint8(v_o_2597_, sizeof(void*)*1);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_o_2597_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2603_ = v_o_2597_;
v_isShared_2604_ = v_isSharedCheck_2615_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_map_2600_);
lean_dec(v_o_2597_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2615_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2605_, 0, v_v_2599_);
lean_inc(v_k_2598_);
v___x_2606_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2598_, v___x_2605_, v_map_2600_);
if (v_hasTrace_2601_ == 0)
{
lean_object* v___x_2607_; uint8_t v___x_2608_; lean_object* v___x_2610_; 
v___x_2607_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_2608_ = l_Lean_Name_isPrefixOf(v___x_2607_, v_k_2598_);
lean_dec(v_k_2598_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2606_);
v___x_2610_ = v___x_2603_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2606_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*1, v___x_2608_);
return v___x_2610_;
}
}
else
{
lean_object* v___x_2613_; 
lean_dec(v_k_2598_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2606_);
v___x_2613_ = v___x_2603_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2606_);
lean_ctor_set_uint8(v_reuseFailAlloc_2614_, sizeof(void*)*1, v_hasTrace_2601_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___boxed(lean_object* v_o_2616_, lean_object* v_k_2617_, lean_object* v_v_2618_){
_start:
{
uint8_t v_v_boxed_2619_; lean_object* v_res_2620_; 
v_v_boxed_2619_ = lean_unbox(v_v_2618_);
v_res_2620_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_o_2616_, v_k_2617_, v_v_boxed_2619_);
return v_res_2620_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(lean_object* v_opts_2621_, lean_object* v_opt_2622_){
_start:
{
lean_object* v_name_2623_; lean_object* v_defValue_2624_; lean_object* v_map_2625_; lean_object* v___x_2626_; 
v_name_2623_ = lean_ctor_get(v_opt_2622_, 0);
v_defValue_2624_ = lean_ctor_get(v_opt_2622_, 1);
v_map_2625_ = lean_ctor_get(v_opts_2621_, 0);
v___x_2626_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2625_, v_name_2623_);
if (lean_obj_tag(v___x_2626_) == 0)
{
uint8_t v___x_2627_; 
v___x_2627_ = lean_unbox(v_defValue_2624_);
return v___x_2627_;
}
else
{
lean_object* v_val_2628_; 
v_val_2628_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_val_2628_);
lean_dec_ref_known(v___x_2626_, 1);
if (lean_obj_tag(v_val_2628_) == 1)
{
uint8_t v_v_2629_; 
v_v_2629_ = lean_ctor_get_uint8(v_val_2628_, 0);
lean_dec_ref_known(v_val_2628_, 0);
return v_v_2629_;
}
else
{
uint8_t v___x_2630_; 
lean_dec(v_val_2628_);
v___x_2630_ = lean_unbox(v_defValue_2624_);
return v___x_2630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1___boxed(lean_object* v_opts_2631_, lean_object* v_opt_2632_){
_start:
{
uint8_t v_res_2633_; lean_object* v_r_2634_; 
v_res_2633_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_opts_2631_, v_opt_2632_);
lean_dec_ref(v_opt_2632_);
lean_dec_ref(v_opts_2631_);
v_r_2634_ = lean_box(v_res_2633_);
return v_r_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0(lean_object* v_ctx_2640_){
_start:
{
lean_object* v_toParserModuleContext_2641_; lean_object* v_toInputContext_2642_; lean_object* v_toCacheableParserContext_2643_; lean_object* v_tokens_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2665_; 
v_toParserModuleContext_2641_ = lean_ctor_get(v_ctx_2640_, 1);
v_toInputContext_2642_ = lean_ctor_get(v_ctx_2640_, 0);
v_toCacheableParserContext_2643_ = lean_ctor_get(v_ctx_2640_, 2);
v_tokens_2644_ = lean_ctor_get(v_ctx_2640_, 3);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_ctx_2640_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2646_ = v_ctx_2640_;
v_isShared_2647_ = v_isSharedCheck_2665_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_tokens_2644_);
lean_inc(v_toCacheableParserContext_2643_);
lean_inc(v_toParserModuleContext_2641_);
lean_inc(v_toInputContext_2642_);
lean_dec(v_ctx_2640_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2665_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v_env_2648_; lean_object* v_options_2649_; lean_object* v_currNamespace_2650_; lean_object* v_openDecls_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2664_; 
v_env_2648_ = lean_ctor_get(v_toParserModuleContext_2641_, 0);
v_options_2649_ = lean_ctor_get(v_toParserModuleContext_2641_, 1);
v_currNamespace_2650_ = lean_ctor_get(v_toParserModuleContext_2641_, 2);
v_openDecls_2651_ = lean_ctor_get(v_toParserModuleContext_2641_, 3);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_toParserModuleContext_2641_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2653_ = v_toParserModuleContext_2641_;
v_isShared_2654_ = v_isSharedCheck_2664_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_openDecls_2651_);
lean_inc(v_currNamespace_2650_);
lean_inc(v_options_2649_);
lean_inc(v_env_2648_);
lean_dec(v_toParserModuleContext_2641_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2664_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; uint8_t v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2655_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_2656_ = 0;
v___x_2657_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_2649_, v___x_2655_, v___x_2656_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 1, v___x_2657_);
v___x_2659_ = v___x_2653_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_env_2648_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_currNamespace_2650_);
lean_ctor_set(v_reuseFailAlloc_2663_, 3, v_openDecls_2651_);
v___x_2659_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2661_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 1, v___x_2659_);
v___x_2661_ = v___x_2646_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_toInputContext_2642_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2662_, 2, v_toCacheableParserContext_2643_);
lean_ctor_set(v_reuseFailAlloc_2662_, 3, v_tokens_2644_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object* v_fn_2666_, lean_object* v_declName_2667_, lean_object* v___f_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v_toParserModuleContext_2671_; lean_object* v_toCacheableParserContext_2672_; uint8_t v___y_2674_; lean_object* v_quotDepth_2686_; uint8_t v_suppressInsideQuot_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v_toParserModuleContext_2671_ = lean_ctor_get(v___y_2669_, 1);
v_toCacheableParserContext_2672_ = lean_ctor_get(v___y_2669_, 2);
v_quotDepth_2686_ = lean_ctor_get(v_toCacheableParserContext_2672_, 1);
v_suppressInsideQuot_2687_ = lean_ctor_get_uint8(v_toCacheableParserContext_2672_, sizeof(void*)*4);
v___x_2688_ = lean_unsigned_to_nat(0u);
v___x_2689_ = lean_nat_dec_lt(v___x_2688_, v_quotDepth_2686_);
if (v___x_2689_ == 0)
{
v___y_2674_ = v___x_2689_;
goto v___jp_2673_;
}
else
{
uint8_t v___x_2690_; 
v___x_2690_ = lean_bool_not(v_suppressInsideQuot_2687_);
v___y_2674_ = v___x_2690_;
goto v___jp_2673_;
}
v___jp_2673_:
{
if (v___y_2674_ == 0)
{
lean_object* v___x_2675_; 
lean_dec_ref(v___f_2668_);
lean_dec(v_declName_2667_);
v___x_2675_ = lean_apply_2(v_fn_2666_, v___y_2669_, v___y_2670_);
return v___x_2675_;
}
else
{
lean_object* v_env_2676_; lean_object* v_options_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v_env_2676_ = lean_ctor_get(v_toParserModuleContext_2671_, 0);
v_options_2677_ = lean_ctor_get(v_toParserModuleContext_2671_, 1);
v___x_2678_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_2679_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_2677_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; 
lean_dec_ref(v___f_2668_);
lean_dec(v_declName_2667_);
v___x_2680_ = lean_apply_2(v_fn_2666_, v___y_2669_, v___y_2670_);
return v___x_2680_;
}
else
{
uint8_t v___x_2681_; 
lean_inc(v_declName_2667_);
lean_inc_ref(v_env_2676_);
v___x_2681_ = l_Lean_Environment_contains(v_env_2676_, v_declName_2667_, v___x_2679_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; 
lean_dec_ref(v___f_2668_);
lean_dec(v_declName_2667_);
v___x_2682_ = lean_apply_2(v_fn_2666_, v___y_2669_, v___y_2670_);
return v___x_2682_;
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2683_, 0, v_fn_2666_);
v___x_2684_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_2684_, 0, v_declName_2667_);
lean_closure_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2668_, v___x_2684_, v___y_2669_, v___y_2670_);
return v___x_2685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object* v_declName_2692_, lean_object* v_p_2693_){
_start:
{
lean_object* v_info_2694_; lean_object* v_fn_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2704_; 
v_info_2694_ = lean_ctor_get(v_p_2693_, 0);
v_fn_2695_ = lean_ctor_get(v_p_2693_, 1);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_p_2693_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2697_ = v_p_2693_;
v_isShared_2698_ = v_isSharedCheck_2704_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_fn_2695_);
lean_inc(v_info_2694_);
lean_dec(v_p_2693_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2704_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___f_2699_; lean_object* v___f_2700_; lean_object* v___x_2702_; 
v___f_2699_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___closed__0));
v___f_2700_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__1), 5, 3);
lean_closure_set(v___f_2700_, 0, v_fn_2695_);
lean_closure_set(v___f_2700_, 1, v_declName_2692_);
lean_closure_set(v___f_2700_, 2, v___f_2699_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___f_2700_);
v___x_2702_ = v___x_2697_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_info_2694_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v___f_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object* v_catName_2705_, lean_object* v_declName_2706_, uint8_t v_leading_2707_, lean_object* v_p_2708_, lean_object* v_prio_2709_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v_p_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2711_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_2712_ = lean_st_ref_get(v___x_2711_);
lean_inc_n(v_declName_2706_, 2);
v_p_2713_ = l_Lean_Parser_evalInsideQuot(v_declName_2706_, v_p_2708_);
lean_inc_ref(v_p_2713_);
v___x_2714_ = l_Lean_Parser_addParser(v___x_2712_, v_catName_2705_, v_declName_2706_, v_leading_2707_, v_p_2713_, v_prio_2709_);
v___x_2715_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_2714_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v_info_2720_; lean_object* v_collectKinds_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
v___x_2717_ = lean_st_ref_set(v___x_2711_, v_a_2716_);
v___x_2718_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_2719_ = lean_st_ref_take(v___x_2718_);
v_info_2720_ = lean_ctor_get(v_p_2713_, 0);
lean_inc_ref(v_info_2720_);
lean_dec_ref(v_p_2713_);
v_collectKinds_2721_ = lean_ctor_get(v_info_2720_, 1);
lean_inc_ref(v_collectKinds_2721_);
v___x_2722_ = lean_apply_1(v_collectKinds_2721_, v___x_2719_);
v___x_2723_ = lean_st_ref_set(v___x_2718_, v___x_2722_);
v___x_2724_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_2720_, v_declName_2706_);
return v___x_2724_;
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec_ref(v_p_2713_);
lean_dec(v_declName_2706_);
v_a_2725_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2715_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2715_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* v_catName_2733_, lean_object* v_declName_2734_, lean_object* v_leading_2735_, lean_object* v_p_2736_, lean_object* v_prio_2737_, lean_object* v_a_2738_){
_start:
{
uint8_t v_leading_boxed_2739_; lean_object* v_res_2740_; 
v_leading_boxed_2739_ = lean_unbox(v_leading_2735_);
v_res_2740_ = l_Lean_Parser_addBuiltinParser(v_catName_2733_, v_declName_2734_, v_leading_boxed_2739_, v_p_2736_, v_prio_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* v_catName_2741_, lean_object* v_declName_2742_, lean_object* v_p_2743_, lean_object* v_prio_2744_){
_start:
{
uint8_t v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = 1;
v___x_2747_ = l_Lean_Parser_addBuiltinParser(v_catName_2741_, v_declName_2742_, v___x_2746_, v_p_2743_, v_prio_2744_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object* v_catName_2748_, lean_object* v_declName_2749_, lean_object* v_p_2750_, lean_object* v_prio_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_Parser_addBuiltinLeadingParser(v_catName_2748_, v_declName_2749_, v_p_2750_, v_prio_2751_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* v_catName_2754_, lean_object* v_declName_2755_, lean_object* v_p_2756_, lean_object* v_prio_2757_){
_start:
{
uint8_t v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = 0;
v___x_2760_ = l_Lean_Parser_addBuiltinParser(v_catName_2754_, v_declName_2755_, v___x_2759_, v_p_2756_, v_prio_2757_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object* v_catName_2761_, lean_object* v_declName_2762_, lean_object* v_p_2763_, lean_object* v_prio_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_Parser_addBuiltinTrailingParser(v_catName_2761_, v_declName_2762_, v_p_2763_, v_prio_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object* v_kind_2767_){
_start:
{
uint8_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = 1;
lean_inc(v_kind_2767_);
v___x_2769_ = l_Lean_Name_toString(v_kind_2767_, v___x_2768_);
v___x_2770_ = l_Lean_Parser_mkAntiquot(v___x_2769_, v_kind_2767_, v___x_2768_, v___x_2768_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object* v_kind_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v___x_2774_; lean_object* v_fn_2775_; lean_object* v___x_2776_; 
v___x_2774_ = l_Lean_Parser_mkCategoryAntiquotParser(v_kind_2771_);
v_fn_2775_ = lean_ctor_get(v___x_2774_, 1);
lean_inc_ref(v_fn_2775_);
lean_dec_ref(v___x_2774_);
v___x_2776_ = lean_apply_2(v_fn_2775_, v_a_2772_, v_a_2773_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl___lam__0(lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v___x_2780_; lean_object* v_fn_2781_; lean_object* v___x_2782_; 
v___x_2780_ = l_Lean_Parser_mkCategoryAntiquotParser(v___y_2777_);
v_fn_2781_ = lean_ctor_get(v___x_2780_, 1);
lean_inc_ref(v_fn_2781_);
lean_dec_ref(v___x_2780_);
v___x_2782_ = lean_apply_2(v_fn_2781_, v___y_2778_, v___y_2779_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* v_catName_2791_, lean_object* v_ctx_2792_, lean_object* v_s_2793_){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; uint8_t v___x_2797_; lean_object* v___y_2799_; 
v___x_2794_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2795_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__1));
v___x_2796_ = lean_name_eq(v_catName_2791_, v___x_2795_);
v___x_2797_ = 1;
if (v___x_2796_ == 0)
{
v___y_2799_ = v_catName_2791_;
goto v___jp_2798_;
}
else
{
lean_object* v___x_2821_; 
lean_dec(v_catName_2791_);
v___x_2821_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__5));
v___y_2799_ = v___x_2821_;
goto v___jp_2798_;
}
v___jp_2798_:
{
lean_object* v_toParserModuleContext_2800_; lean_object* v_env_2801_; lean_object* v___x_2802_; lean_object* v_ext_2803_; lean_object* v_toEnvExtension_2804_; lean_object* v_asyncMode_2805_; lean_object* v___x_2806_; lean_object* v_categories_2807_; lean_object* v___x_2808_; 
v_toParserModuleContext_2800_ = lean_ctor_get(v_ctx_2792_, 1);
v_env_2801_ = lean_ctor_get(v_toParserModuleContext_2800_, 0);
v___x_2802_ = l_Lean_Parser_parserExtension;
v_ext_2803_ = lean_ctor_get(v___x_2802_, 1);
v_toEnvExtension_2804_ = lean_ctor_get(v_ext_2803_, 0);
v_asyncMode_2805_ = lean_ctor_get(v_toEnvExtension_2804_, 2);
lean_inc_ref(v_env_2801_);
v___x_2806_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2794_, v___x_2802_, v_env_2801_, v_asyncMode_2805_);
v_categories_2807_ = lean_ctor_get(v___x_2806_, 2);
lean_inc_ref(v_categories_2807_);
lean_dec(v___x_2806_);
v___x_2808_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2807_, v___y_2799_);
lean_dec_ref(v_categories_2807_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_dec_ref(v_ctx_2792_);
v___x_2809_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__2));
v___x_2810_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2799_, v___x_2797_);
v___x_2811_ = lean_string_append(v___x_2809_, v___x_2810_);
lean_dec_ref(v___x_2810_);
v___x_2812_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__3));
v___x_2813_ = lean_string_append(v___x_2811_, v___x_2812_);
v___x_2814_ = lean_box(0);
v___x_2815_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2793_, v___x_2813_, v___x_2814_, v___x_2797_);
return v___x_2815_;
}
else
{
lean_object* v_val_2816_; lean_object* v_tables_2817_; uint8_t v_behavior_2818_; lean_object* v___f_2819_; lean_object* v___x_2820_; 
v_val_2816_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_val_2816_);
lean_dec_ref_known(v___x_2808_, 1);
v_tables_2817_ = lean_ctor_get(v_val_2816_, 2);
lean_inc_ref(v_tables_2817_);
v_behavior_2818_ = lean_ctor_get_uint8(v_val_2816_, sizeof(void*)*3);
lean_dec(v_val_2816_);
lean_inc(v___y_2799_);
v___f_2819_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl___lam__0), 3, 1);
lean_closure_set(v___f_2819_, 0, v___y_2799_);
v___x_2820_ = l_Lean_Parser_prattParser(v___y_2799_, v_tables_2817_, v_behavior_2818_, v___f_2819_, v_ctx_2792_, v_s_2793_);
return v___x_2820_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2824_ = l_Lean_Parser_categoryParserFnRef;
v___x_2825_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_));
v___x_2826_ = lean_st_ref_set(v___x_2824_, v___x_2825_);
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
return v_res_2829_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2830_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0);
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
return v___x_2832_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object* v_ext_2835_, lean_object* v_b_2836_, uint8_t v_kind_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v_currNamespace_2841_; lean_object* v___x_2842_; lean_object* v_env_2843_; lean_object* v_nextMacroScope_2844_; lean_object* v_ngen_2845_; lean_object* v_auxDeclNGen_2846_; lean_object* v_traceState_2847_; lean_object* v_messages_2848_; lean_object* v_infoState_2849_; lean_object* v_snapshotTasks_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2862_; 
v_currNamespace_2841_ = lean_ctor_get(v___y_2838_, 6);
v___x_2842_ = lean_st_ref_take(v___y_2839_);
v_env_2843_ = lean_ctor_get(v___x_2842_, 0);
v_nextMacroScope_2844_ = lean_ctor_get(v___x_2842_, 1);
v_ngen_2845_ = lean_ctor_get(v___x_2842_, 2);
v_auxDeclNGen_2846_ = lean_ctor_get(v___x_2842_, 3);
v_traceState_2847_ = lean_ctor_get(v___x_2842_, 4);
v_messages_2848_ = lean_ctor_get(v___x_2842_, 6);
v_infoState_2849_ = lean_ctor_get(v___x_2842_, 7);
v_snapshotTasks_2850_ = lean_ctor_get(v___x_2842_, 8);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2862_ == 0)
{
lean_object* v_unused_2863_; 
v_unused_2863_ = lean_ctor_get(v___x_2842_, 5);
lean_dec(v_unused_2863_);
v___x_2852_ = v___x_2842_;
v_isShared_2853_ = v_isSharedCheck_2862_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_snapshotTasks_2850_);
lean_inc(v_infoState_2849_);
lean_inc(v_messages_2848_);
lean_inc(v_traceState_2847_);
lean_inc(v_auxDeclNGen_2846_);
lean_inc(v_ngen_2845_);
lean_inc(v_nextMacroScope_2844_);
lean_inc(v_env_2843_);
lean_dec(v___x_2842_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2862_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
lean_inc(v_currNamespace_2841_);
v___x_2854_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2843_, v_ext_2835_, v_b_2836_, v_kind_2837_, v_currNamespace_2841_);
v___x_2855_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 5, v___x_2855_);
lean_ctor_set(v___x_2852_, 0, v___x_2854_);
v___x_2857_ = v___x_2852_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_nextMacroScope_2844_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_ngen_2845_);
lean_ctor_set(v_reuseFailAlloc_2861_, 3, v_auxDeclNGen_2846_);
lean_ctor_set(v_reuseFailAlloc_2861_, 4, v_traceState_2847_);
lean_ctor_set(v_reuseFailAlloc_2861_, 5, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2861_, 6, v_messages_2848_);
lean_ctor_set(v_reuseFailAlloc_2861_, 7, v_infoState_2849_);
lean_ctor_set(v_reuseFailAlloc_2861_, 8, v_snapshotTasks_2850_);
v___x_2857_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = lean_st_ref_set(v___y_2839_, v___x_2857_);
v___x_2859_ = lean_box(0);
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
return v___x_2860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object* v_ext_2864_, lean_object* v_b_2865_, lean_object* v_kind_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
uint8_t v_kind_boxed_2870_; lean_object* v_res_2871_; 
v_kind_boxed_2870_ = lean_unbox(v_kind_2866_);
v_res_2871_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2864_, v_b_2865_, v_kind_boxed_2870_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object* v_00_u03b1_2872_, lean_object* v_00_u03b2_2873_, lean_object* v_00_u03c3_2874_, lean_object* v_ext_2875_, lean_object* v_b_2876_, uint8_t v_kind_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2875_, v_b_2876_, v_kind_2877_, v___y_2878_, v___y_2879_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object* v_00_u03b1_2882_, lean_object* v_00_u03b2_2883_, lean_object* v_00_u03c3_2884_, lean_object* v_ext_2885_, lean_object* v_b_2886_, lean_object* v_kind_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
uint8_t v_kind_boxed_2891_; lean_object* v_res_2892_; 
v_kind_boxed_2891_ = lean_unbox(v_kind_2887_);
v_res_2892_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(v_00_u03b1_2882_, v_00_u03b2_2883_, v_00_u03c3_2884_, v_ext_2885_, v_b_2886_, v_kind_boxed_2891_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object* v_x_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
if (lean_obj_tag(v_x_2893_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_a_2897_ = lean_ctor_get(v_x_2893_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v_x_2893_, 1);
v___x_2898_ = l_Lean_stringToMessageData(v_a_2897_);
v___x_2899_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2898_, v___y_2894_, v___y_2895_);
return v___x_2899_;
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
v_a_2900_ = lean_ctor_get(v_x_2893_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_x_2893_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v_x_2893_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v_x_2893_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
lean_ctor_set_tag(v___x_2902_, 0);
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object* v_x_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object* v_tk_2913_, uint8_t v_kind_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v___x_2918_; lean_object* v_env_2919_; lean_object* v___x_2920_; lean_object* v_ext_2921_; lean_object* v_toEnvExtension_2922_; lean_object* v_asyncMode_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v_tokens_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2918_ = lean_st_ref_get(v_a_2916_);
v_env_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc_ref(v_env_2919_);
lean_dec(v___x_2918_);
v___x_2920_ = l_Lean_Parser_parserExtension;
v_ext_2921_ = lean_ctor_get(v___x_2920_, 1);
v_toEnvExtension_2922_ = lean_ctor_get(v_ext_2921_, 0);
v_asyncMode_2923_ = lean_ctor_get(v_toEnvExtension_2922_, 2);
v___x_2924_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2925_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2924_, v___x_2920_, v_env_2919_, v_asyncMode_2923_);
v_tokens_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc_ref(v_tokens_2926_);
lean_dec(v___x_2925_);
lean_inc_ref(v_tk_2913_);
v___x_2927_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_2926_, v_tk_2913_);
v___x_2928_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v___x_2927_, v_a_2915_, v_a_2916_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec_ref_known(v___x_2928_, 1);
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v_tk_2913_);
v___x_2930_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_2920_, v___x_2929_, v_kind_2914_, v_a_2915_, v_a_2916_);
return v___x_2930_;
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec_ref(v_tk_2913_);
v_a_2931_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2928_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2928_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object* v_tk_2939_, lean_object* v_kind_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
uint8_t v_kind_boxed_2944_; lean_object* v_res_2945_; 
v_kind_boxed_2944_ = lean_unbox(v_kind_2940_);
v_res_2945_ = l_Lean_Parser_addToken(v_tk_2939_, v_kind_boxed_2944_, v_a_2941_, v_a_2942_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_object* v_00_u03b1_2946_, lean_object* v_x_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2947_, v___y_2948_, v___y_2949_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___boxed(lean_object* v_00_u03b1_2952_, lean_object* v_x_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(v_00_u03b1_2952_, v_x_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object* v_env_2958_, lean_object* v_k_2959_){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = l_Lean_Parser_parserExtension;
v___x_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2961_, 0, v_k_2959_);
v___x_2962_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2960_, v_env_2958_, v___x_2961_);
return v___x_2962_;
}
}
static uint8_t _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0(void){
_start:
{
lean_object* v___x_2963_; uint8_t v___x_2964_; 
v___x_2963_ = lean_box(0);
v___x_2964_ = lean_internal_is_stage0(v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object* v_env_2965_, lean_object* v_k_2966_){
_start:
{
lean_object* v___x_2967_; lean_object* v_ext_2968_; lean_object* v_toEnvExtension_2969_; lean_object* v_asyncMode_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v_kinds_2973_; uint8_t v___x_2974_; 
v___x_2967_ = l_Lean_Parser_parserExtension;
v_ext_2968_ = lean_ctor_get(v___x_2967_, 1);
v_toEnvExtension_2969_ = lean_ctor_get(v_ext_2968_, 0);
v_asyncMode_2970_ = lean_ctor_get(v_toEnvExtension_2969_, 2);
v___x_2971_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_2965_);
v___x_2972_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2971_, v___x_2967_, v_env_2965_, v_asyncMode_2970_);
v_kinds_2973_ = lean_ctor_get(v___x_2972_, 1);
lean_inc_ref(v_kinds_2973_);
lean_dec(v___x_2972_);
v___x_2974_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_2973_, v_k_2966_);
lean_dec_ref(v_kinds_2973_);
if (v___x_2974_ == 0)
{
uint8_t v___x_2975_; 
v___x_2975_ = lean_uint8_once(&l_Lean_Parser_isValidSyntaxNodeKind___closed__0, &l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once, _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0);
if (v___x_2975_ == 0)
{
lean_dec(v_k_2966_);
lean_dec_ref(v_env_2965_);
return v___x_2975_;
}
else
{
uint8_t v___x_2976_; 
v___x_2976_ = l_Lean_Environment_contains(v_env_2965_, v_k_2966_, v___x_2975_);
return v___x_2976_;
}
}
else
{
lean_dec(v_k_2966_);
lean_dec_ref(v_env_2965_);
return v___x_2974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* v_env_2977_, lean_object* v_k_2978_){
_start:
{
uint8_t v_res_2979_; lean_object* v_r_2980_; 
v_res_2979_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_2977_, v_k_2978_);
v_r_2980_ = lean_box(v_res_2979_);
return v_r_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds___lam__0(lean_object* v_ks_2981_, lean_object* v_k_2982_, lean_object* v_x_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2984_, 0, v_k_2982_);
lean_ctor_set(v___x_2984_, 1, v_ks_2981_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2985_, lean_object* v_keys_2986_, lean_object* v_vals_2987_, lean_object* v_i_2988_, lean_object* v_acc_2989_){
_start:
{
lean_object* v___x_2990_; uint8_t v___x_2991_; 
v___x_2990_ = lean_array_get_size(v_keys_2986_);
v___x_2991_ = lean_nat_dec_lt(v_i_2988_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_dec(v_i_2988_);
lean_dec(v_f_2985_);
return v_acc_2989_;
}
else
{
lean_object* v_k_2992_; lean_object* v_v_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v_k_2992_ = lean_array_fget_borrowed(v_keys_2986_, v_i_2988_);
v_v_2993_ = lean_array_fget_borrowed(v_vals_2987_, v_i_2988_);
lean_inc(v_f_2985_);
lean_inc(v_v_2993_);
lean_inc(v_k_2992_);
v___x_2994_ = lean_apply_3(v_f_2985_, v_acc_2989_, v_k_2992_, v_v_2993_);
v___x_2995_ = lean_unsigned_to_nat(1u);
v___x_2996_ = lean_nat_add(v_i_2988_, v___x_2995_);
lean_dec(v_i_2988_);
v_i_2988_ = v___x_2996_;
v_acc_2989_ = v___x_2994_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2998_, lean_object* v_keys_2999_, lean_object* v_vals_3000_, lean_object* v_i_3001_, lean_object* v_acc_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2998_, v_keys_2999_, v_vals_3000_, v_i_3001_, v_acc_3002_);
lean_dec_ref(v_vals_3000_);
lean_dec_ref(v_keys_2999_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3004_, lean_object* v_x_3005_, lean_object* v_x_3006_){
_start:
{
if (lean_obj_tag(v_x_3005_) == 0)
{
lean_object* v_es_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
v_es_3007_ = lean_ctor_get(v_x_3005_, 0);
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = lean_array_get_size(v_es_3007_);
v___x_3010_ = lean_nat_dec_lt(v___x_3008_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_dec(v_f_3004_);
return v_x_3006_;
}
else
{
uint8_t v___x_3011_; 
v___x_3011_ = lean_nat_dec_le(v___x_3009_, v___x_3009_);
if (v___x_3011_ == 0)
{
if (v___x_3010_ == 0)
{
lean_dec(v_f_3004_);
return v_x_3006_;
}
else
{
size_t v___x_3012_; size_t v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((size_t)0ULL);
v___x_3013_ = lean_usize_of_nat(v___x_3009_);
v___x_3014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3004_, v_es_3007_, v___x_3012_, v___x_3013_, v_x_3006_);
return v___x_3014_;
}
}
else
{
size_t v___x_3015_; size_t v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = ((size_t)0ULL);
v___x_3016_ = lean_usize_of_nat(v___x_3009_);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3004_, v_es_3007_, v___x_3015_, v___x_3016_, v_x_3006_);
return v___x_3017_;
}
}
}
else
{
lean_object* v_ks_3018_; lean_object* v_vs_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_ks_3018_ = lean_ctor_get(v_x_3005_, 0);
v_vs_3019_ = lean_ctor_get(v_x_3005_, 1);
v___x_3020_ = lean_unsigned_to_nat(0u);
v___x_3021_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3004_, v_ks_3018_, v_vs_3019_, v___x_3020_, v_x_3006_);
return v___x_3021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3022_, lean_object* v_as_3023_, size_t v_i_3024_, size_t v_stop_3025_, lean_object* v_b_3026_){
_start:
{
lean_object* v___y_3028_; uint8_t v___x_3032_; 
v___x_3032_ = lean_usize_dec_eq(v_i_3024_, v_stop_3025_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_array_uget_borrowed(v_as_3023_, v_i_3024_);
switch(lean_obj_tag(v___x_3033_))
{
case 0:
{
lean_object* v_key_3034_; lean_object* v_val_3035_; lean_object* v___x_3036_; 
v_key_3034_ = lean_ctor_get(v___x_3033_, 0);
v_val_3035_ = lean_ctor_get(v___x_3033_, 1);
lean_inc(v_f_3022_);
lean_inc(v_val_3035_);
lean_inc(v_key_3034_);
v___x_3036_ = lean_apply_3(v_f_3022_, v_b_3026_, v_key_3034_, v_val_3035_);
v___y_3028_ = v___x_3036_;
goto v___jp_3027_;
}
case 1:
{
lean_object* v_node_3037_; lean_object* v___x_3038_; 
v_node_3037_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_f_3022_);
v___x_3038_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3022_, v_node_3037_, v_b_3026_);
v___y_3028_ = v___x_3038_;
goto v___jp_3027_;
}
default: 
{
v___y_3028_ = v_b_3026_;
goto v___jp_3027_;
}
}
}
else
{
lean_dec(v_f_3022_);
return v_b_3026_;
}
v___jp_3027_:
{
size_t v___x_3029_; size_t v___x_3030_; 
v___x_3029_ = ((size_t)1ULL);
v___x_3030_ = lean_usize_add(v_i_3024_, v___x_3029_);
v_i_3024_ = v___x_3030_;
v_b_3026_ = v___y_3028_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3039_, lean_object* v_as_3040_, lean_object* v_i_3041_, lean_object* v_stop_3042_, lean_object* v_b_3043_){
_start:
{
size_t v_i_boxed_3044_; size_t v_stop_boxed_3045_; lean_object* v_res_3046_; 
v_i_boxed_3044_ = lean_unbox_usize(v_i_3041_);
lean_dec(v_i_3041_);
v_stop_boxed_3045_ = lean_unbox_usize(v_stop_3042_);
lean_dec(v_stop_3042_);
v_res_3046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3039_, v_as_3040_, v_i_boxed_3044_, v_stop_boxed_3045_, v_b_3043_);
lean_dec_ref(v_as_3040_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3047_, lean_object* v_x_3048_, lean_object* v_x_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3047_, v_x_3048_, v_x_3049_);
lean_dec_ref(v_x_3048_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object* v_f_3051_, lean_object* v_x1_3052_, lean_object* v_x2_3053_, lean_object* v_x3_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_apply_3(v_f_3051_, v_x1_3052_, v_x2_3053_, v_x3_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object* v_map_3056_, lean_object* v_f_3057_, lean_object* v_init_3058_){
_start:
{
lean_object* v___f_3059_; lean_object* v___x_3060_; 
v___f_3059_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3059_, 0, v_f_3057_);
v___x_3060_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v___f_3059_, v_map_3056_, v_init_3058_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object* v_map_3061_, lean_object* v_f_3062_, lean_object* v_init_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3061_, v_f_3062_, v_init_3063_);
lean_dec_ref(v_map_3061_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* v_env_3066_){
_start:
{
lean_object* v___x_3067_; lean_object* v_ext_3068_; lean_object* v_toEnvExtension_3069_; lean_object* v_asyncMode_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v_kinds_3073_; lean_object* v___f_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3067_ = l_Lean_Parser_parserExtension;
v_ext_3068_ = lean_ctor_get(v___x_3067_, 1);
v_toEnvExtension_3069_ = lean_ctor_get(v_ext_3068_, 0);
v_asyncMode_3070_ = lean_ctor_get(v_toEnvExtension_3069_, 2);
v___x_3071_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3072_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3071_, v___x_3067_, v_env_3066_, v_asyncMode_3070_);
v_kinds_3073_ = lean_ctor_get(v___x_3072_, 1);
lean_inc_ref(v_kinds_3073_);
lean_dec(v___x_3072_);
v___f_3074_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKinds___closed__0));
v___x_3075_ = lean_box(0);
v___x_3076_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_kinds_3073_, v___f_3074_, v___x_3075_);
lean_dec_ref(v_kinds_3073_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object* v_00_u03c3_3077_, lean_object* v_00_u03b2_3078_, lean_object* v_map_3079_, lean_object* v_f_3080_, lean_object* v_init_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3079_, v_f_3080_, v_init_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object* v_00_u03c3_3083_, lean_object* v_00_u03b2_3084_, lean_object* v_map_3085_, lean_object* v_f_3086_, lean_object* v_init_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(v_00_u03c3_3083_, v_00_u03b2_3084_, v_map_3085_, v_f_3086_, v_init_3087_);
lean_dec_ref(v_map_3085_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object* v_map_3089_, lean_object* v_f_3090_, lean_object* v_init_3091_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3090_, v_map_3089_, v_init_3091_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object* v_map_3093_, lean_object* v_f_3094_, lean_object* v_init_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(v_map_3093_, v_f_3094_, v_init_3095_);
lean_dec_ref(v_map_3093_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object* v_00_u03c3_3097_, lean_object* v_00_u03b2_3098_, lean_object* v_map_3099_, lean_object* v_f_3100_, lean_object* v_init_3101_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3100_, v_map_3099_, v_init_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3103_, lean_object* v_00_u03b2_3104_, lean_object* v_map_3105_, lean_object* v_f_3106_, lean_object* v_init_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(v_00_u03c3_3103_, v_00_u03b2_3104_, v_map_3105_, v_f_3106_, v_init_3107_);
lean_dec_ref(v_map_3105_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3109_, lean_object* v_00_u03b1_3110_, lean_object* v_00_u03b2_3111_, lean_object* v_f_3112_, lean_object* v_x_3113_, lean_object* v_x_3114_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3112_, v_x_3113_, v_x_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3116_, lean_object* v_00_u03b1_3117_, lean_object* v_00_u03b2_3118_, lean_object* v_f_3119_, lean_object* v_x_3120_, lean_object* v_x_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(v_00_u03c3_3116_, v_00_u03b1_3117_, v_00_u03b2_3118_, v_f_3119_, v_x_3120_, v_x_3121_);
lean_dec_ref(v_x_3120_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3123_, lean_object* v_00_u03b2_3124_, lean_object* v_00_u03c3_3125_, lean_object* v_f_3126_, lean_object* v_as_3127_, size_t v_i_3128_, size_t v_stop_3129_, lean_object* v_b_3130_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3126_, v_as_3127_, v_i_3128_, v_stop_3129_, v_b_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3132_, lean_object* v_00_u03b2_3133_, lean_object* v_00_u03c3_3134_, lean_object* v_f_3135_, lean_object* v_as_3136_, lean_object* v_i_3137_, lean_object* v_stop_3138_, lean_object* v_b_3139_){
_start:
{
size_t v_i_boxed_3140_; size_t v_stop_boxed_3141_; lean_object* v_res_3142_; 
v_i_boxed_3140_ = lean_unbox_usize(v_i_3137_);
lean_dec(v_i_3137_);
v_stop_boxed_3141_ = lean_unbox_usize(v_stop_3138_);
lean_dec(v_stop_3138_);
v_res_3142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3132_, v_00_u03b2_3133_, v_00_u03c3_3134_, v_f_3135_, v_as_3136_, v_i_boxed_3140_, v_stop_boxed_3141_, v_b_3139_);
lean_dec_ref(v_as_3136_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3143_, lean_object* v_00_u03b1_3144_, lean_object* v_00_u03b2_3145_, lean_object* v_f_3146_, lean_object* v_keys_3147_, lean_object* v_vals_3148_, lean_object* v_heq_3149_, lean_object* v_i_3150_, lean_object* v_acc_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3146_, v_keys_3147_, v_vals_3148_, v_i_3150_, v_acc_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3153_, lean_object* v_00_u03b1_3154_, lean_object* v_00_u03b2_3155_, lean_object* v_f_3156_, lean_object* v_keys_3157_, lean_object* v_vals_3158_, lean_object* v_heq_3159_, lean_object* v_i_3160_, lean_object* v_acc_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3153_, v_00_u03b1_3154_, v_00_u03b2_3155_, v_f_3156_, v_keys_3157_, v_vals_3158_, v_heq_3159_, v_i_3160_, v_acc_3161_);
lean_dec_ref(v_vals_3158_);
lean_dec_ref(v_keys_3157_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* v_env_3163_){
_start:
{
lean_object* v___x_3164_; lean_object* v_ext_3165_; lean_object* v_toEnvExtension_3166_; lean_object* v_asyncMode_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v_tokens_3170_; 
v___x_3164_ = l_Lean_Parser_parserExtension;
v_ext_3165_ = lean_ctor_get(v___x_3164_, 1);
v_toEnvExtension_3166_ = lean_ctor_get(v_ext_3165_, 0);
v_asyncMode_3167_ = lean_ctor_get(v_toEnvExtension_3166_, 2);
v___x_3168_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3169_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3168_, v___x_3164_, v_env_3163_, v_asyncMode_3167_);
v_tokens_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc_ref(v_tokens_3170_);
lean_dec(v___x_3169_);
return v_tokens_3170_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__8));
v___x_3196_ = l_Lean_mkAtom(v___x_3195_);
return v___x_3196_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__10, &l_Lean_Parser_mkInputContext___auto__1___closed__10_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__10);
v___x_3198_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3199_ = lean_array_push(v___x_3198_, v___x_3197_);
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3211_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3212_ = lean_array_push(v___x_3211_, v___x_3210_);
return v___x_3212_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3213_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__15, &l_Lean_Parser_mkInputContext___auto__1___closed__15_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__15);
v___x_3214_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__13));
v___x_3215_ = lean_box(2);
v___x_3216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set(v___x_3216_, 1, v___x_3214_);
lean_ctor_set(v___x_3216_, 2, v___x_3213_);
return v___x_3216_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3217_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__16, &l_Lean_Parser_mkInputContext___auto__1___closed__16_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__16);
v___x_3218_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__11, &l_Lean_Parser_mkInputContext___auto__1___closed__11_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__11);
v___x_3219_ = lean_array_push(v___x_3218_, v___x_3217_);
return v___x_3219_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3220_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3221_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__17, &l_Lean_Parser_mkInputContext___auto__1___closed__17_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__17);
v___x_3222_ = lean_array_push(v___x_3221_, v___x_3220_);
return v___x_3222_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3224_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__18, &l_Lean_Parser_mkInputContext___auto__1___closed__18_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__18);
v___x_3225_ = lean_array_push(v___x_3224_, v___x_3223_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3227_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__19, &l_Lean_Parser_mkInputContext___auto__1___closed__19_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__19);
v___x_3228_ = lean_array_push(v___x_3227_, v___x_3226_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3230_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__20, &l_Lean_Parser_mkInputContext___auto__1___closed__20_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__20);
v___x_3231_ = lean_array_push(v___x_3230_, v___x_3229_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3232_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__21, &l_Lean_Parser_mkInputContext___auto__1___closed__21_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__21);
v___x_3233_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__9));
v___x_3234_ = lean_box(2);
v___x_3235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3234_);
lean_ctor_set(v___x_3235_, 1, v___x_3233_);
lean_ctor_set(v___x_3235_, 2, v___x_3232_);
return v___x_3235_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3236_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__22, &l_Lean_Parser_mkInputContext___auto__1___closed__22_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__22);
v___x_3237_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3238_ = lean_array_push(v___x_3237_, v___x_3236_);
return v___x_3238_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3239_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__23, &l_Lean_Parser_mkInputContext___auto__1___closed__23_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__23);
v___x_3240_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3241_ = lean_box(2);
v___x_3242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
lean_ctor_set(v___x_3242_, 1, v___x_3240_);
lean_ctor_set(v___x_3242_, 2, v___x_3239_);
return v___x_3242_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__24, &l_Lean_Parser_mkInputContext___auto__1___closed__24_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__24);
v___x_3244_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3245_ = lean_array_push(v___x_3244_, v___x_3243_);
return v___x_3245_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3246_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__25, &l_Lean_Parser_mkInputContext___auto__1___closed__25_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__25);
v___x_3247_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3248_ = lean_box(2);
v___x_3249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
lean_ctor_set(v___x_3249_, 1, v___x_3247_);
lean_ctor_set(v___x_3249_, 2, v___x_3246_);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3250_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__26, &l_Lean_Parser_mkInputContext___auto__1___closed__26_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__26);
v___x_3251_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3252_ = lean_array_push(v___x_3251_, v___x_3250_);
return v___x_3252_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3253_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__27, &l_Lean_Parser_mkInputContext___auto__1___closed__27_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__27);
v___x_3254_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3255_ = lean_box(2);
v___x_3256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
lean_ctor_set(v___x_3256_, 1, v___x_3254_);
lean_ctor_set(v___x_3256_, 2, v___x_3253_);
return v___x_3256_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1(void){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__28, &l_Lean_Parser_mkInputContext___auto__1___closed__28_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__28);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object* v_input_3258_, lean_object* v_fileName_3259_, uint8_t v_normalizeLineEndings_3260_, lean_object* v_endPos_3261_){
_start:
{
lean_object* v_fst_3263_; lean_object* v_snd_3264_; lean_object* v_text_3270_; 
v_text_3270_ = l_Lean_FileMap_ofString(v_input_3258_);
if (v_normalizeLineEndings_3260_ == 0)
{
v_fst_3263_ = v_text_3270_;
v_snd_3264_ = v_endPos_3261_;
goto v___jp_3262_;
}
else
{
lean_object* v_source_3271_; lean_object* v_endPos_x27_3272_; lean_object* v___x_3273_; lean_object* v_text_3274_; lean_object* v___x_3275_; 
v_source_3271_ = lean_ctor_get(v_text_3270_, 0);
lean_inc_ref(v_source_3271_);
v_endPos_x27_3272_ = l_Lean_FileMap_toPosition(v_text_3270_, v_endPos_3261_);
lean_dec(v_endPos_3261_);
v___x_3273_ = l_String_crlfToLf(v_source_3271_);
lean_dec_ref(v_source_3271_);
v_text_3274_ = l_Lean_FileMap_ofString(v___x_3273_);
v___x_3275_ = l_Lean_FileMap_ofPosition(v_text_3274_, v_endPos_x27_3272_);
v_fst_3263_ = v_text_3274_;
v_snd_3264_ = v___x_3275_;
goto v___jp_3262_;
}
v___jp_3262_:
{
lean_object* v_source_3265_; lean_object* v___x_3266_; uint8_t v___x_3267_; 
v_source_3265_ = lean_ctor_get(v_fst_3263_, 0);
lean_inc_ref(v_source_3265_);
v___x_3266_ = lean_string_utf8_byte_size(v_source_3265_);
v___x_3267_ = lean_nat_dec_le(v_snd_3264_, v___x_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; 
lean_dec(v_snd_3264_);
v___x_3268_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3268_, 0, v_source_3265_);
lean_ctor_set(v___x_3268_, 1, v_fileName_3259_);
lean_ctor_set(v___x_3268_, 2, v_fst_3263_);
lean_ctor_set(v___x_3268_, 3, v___x_3266_);
return v___x_3268_;
}
else
{
lean_object* v___x_3269_; 
v___x_3269_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3269_, 0, v_source_3265_);
lean_ctor_set(v___x_3269_, 1, v_fileName_3259_);
lean_ctor_set(v___x_3269_, 2, v_fst_3263_);
lean_ctor_set(v___x_3269_, 3, v_snd_3264_);
return v___x_3269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object* v_input_3276_, lean_object* v_fileName_3277_, lean_object* v_normalizeLineEndings_3278_, lean_object* v_endPos_3279_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3280_; lean_object* v_res_3281_; 
v_normalizeLineEndings_boxed_3280_ = lean_unbox(v_normalizeLineEndings_3278_);
v_res_3281_ = l_Lean_Parser_mkInputContext___redArg(v_input_3276_, v_fileName_3277_, v_normalizeLineEndings_boxed_3280_, v_endPos_3279_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object* v_input_3282_, lean_object* v_fileName_3283_, uint8_t v_normalizeLineEndings_3284_, lean_object* v_endPos_3285_, lean_object* v_endPos__valid_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_Parser_mkInputContext___redArg(v_input_3282_, v_fileName_3283_, v_normalizeLineEndings_3284_, v_endPos_3285_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object* v_input_3288_, lean_object* v_fileName_3289_, lean_object* v_normalizeLineEndings_3290_, lean_object* v_endPos_3291_, lean_object* v_endPos__valid_3292_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3293_; lean_object* v_res_3294_; 
v_normalizeLineEndings_boxed_3293_ = lean_unbox(v_normalizeLineEndings_3290_);
v_res_3294_ = l_Lean_Parser_mkInputContext(v_input_3288_, v_fileName_3289_, v_normalizeLineEndings_boxed_3293_, v_endPos_3291_, v_endPos__valid_3292_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* v_input_3297_){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3298_ = l_Lean_Parser_SyntaxStack_empty;
v___x_3299_ = lean_unsigned_to_nat(0u);
v___x_3300_ = l_Lean_Parser_initCacheForInput(v_input_3297_);
v___x_3301_ = lean_box(0);
v___x_3302_ = ((lean_object*)(l_Lean_Parser_mkParserState___closed__0));
v___x_3303_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3298_);
lean_ctor_set(v___x_3303_, 1, v___x_3299_);
lean_ctor_set(v___x_3303_, 2, v___x_3299_);
lean_ctor_set(v___x_3303_, 3, v___x_3300_);
lean_ctor_set(v___x_3303_, 4, v___x_3301_);
lean_ctor_set(v___x_3303_, 5, v___x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* v_input_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_Parser_mkParserState(v_input_3304_);
lean_dec_ref(v_input_3304_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* v_env_3308_, lean_object* v_catName_3309_, lean_object* v_input_3310_, lean_object* v_fileName_3311_){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v_p_3314_; uint8_t v___x_3315_; lean_object* v___x_3316_; lean_object* v_ictx_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v_s_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; uint8_t v___x_3329_; 
v___x_3312_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__0));
v___x_3313_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 1);
lean_closure_set(v___x_3313_, 0, v_catName_3309_);
v_p_3314_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_3314_, 0, v___x_3312_);
lean_closure_set(v_p_3314_, 1, v___x_3313_);
v___x_3315_ = 1;
v___x_3316_ = lean_string_utf8_byte_size(v_input_3310_);
lean_inc_ref(v_input_3310_);
v_ictx_3317_ = l_Lean_Parser_mkInputContext___redArg(v_input_3310_, v_fileName_3311_, v___x_3315_, v___x_3316_);
v___x_3318_ = l_Lean_Options_empty;
v___x_3319_ = lean_box(0);
v___x_3320_ = lean_box(0);
lean_inc_ref(v_env_3308_);
v___x_3321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3321_, 0, v_env_3308_);
lean_ctor_set(v___x_3321_, 1, v___x_3318_);
lean_ctor_set(v___x_3321_, 2, v___x_3319_);
lean_ctor_set(v___x_3321_, 3, v___x_3320_);
v___x_3322_ = l_Lean_Parser_getTokenTable(v_env_3308_);
v___x_3323_ = l_Lean_Parser_mkParserState(v_input_3310_);
lean_dec_ref(v_input_3310_);
lean_inc_ref(v_ictx_3317_);
v_s_3324_ = l_Lean_Parser_ParserFn_run(v_p_3314_, v_ictx_3317_, v___x_3321_, v___x_3322_, v___x_3323_);
lean_inc_ref(v_s_3324_);
v___x_3325_ = l_Lean_Parser_ParserState_allErrors(v_s_3324_);
v___x_3326_ = lean_array_get_size(v___x_3325_);
lean_dec_ref(v___x_3325_);
v___x_3327_ = lean_unsigned_to_nat(0u);
v___x_3328_ = lean_nat_dec_eq(v___x_3326_, v___x_3327_);
v___x_3329_ = lean_bool_not(v___x_3328_);
if (v___x_3329_ == 0)
{
lean_object* v_stxStack_3330_; lean_object* v_pos_3331_; uint8_t v___x_3332_; 
v_stxStack_3330_ = lean_ctor_get(v_s_3324_, 0);
lean_inc_ref(v_stxStack_3330_);
v_pos_3331_ = lean_ctor_get(v_s_3324_, 2);
lean_inc(v_pos_3331_);
v___x_3332_ = l_Lean_Parser_InputContext_atEnd(v_ictx_3317_, v_pos_3331_);
lean_dec(v_pos_3331_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
lean_dec_ref(v_stxStack_3330_);
v___x_3333_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__1));
v___x_3334_ = l_Lean_Parser_ParserState_mkError(v_s_3324_, v___x_3333_);
v___x_3335_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3317_, v___x_3334_);
v___x_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
return v___x_3336_;
}
else
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_dec_ref(v_s_3324_);
lean_dec_ref(v_ictx_3317_);
v___x_3337_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3330_);
lean_dec_ref(v_stxStack_3330_);
v___x_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
return v___x_3338_;
}
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3317_, v_s_3324_);
v___x_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
return v___x_3340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* v_addFnName_3341_, lean_object* v_catName_3342_, lean_object* v_declName_3343_, lean_object* v_prio_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v_val_3360_; lean_object* v___x_3361_; 
v___x_3348_ = lean_box(0);
v___x_3349_ = l_Lean_mkConst(v_addFnName_3341_, v___x_3348_);
v___x_3350_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_catName_3342_);
lean_inc_n(v_declName_3343_, 2);
v___x_3351_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3343_);
v___x_3352_ = l_Lean_mkConst(v_declName_3343_, v___x_3348_);
v___x_3353_ = l_Lean_mkRawNatLit(v_prio_3344_);
v___x_3354_ = lean_unsigned_to_nat(4u);
v___x_3355_ = lean_mk_empty_array_with_capacity(v___x_3354_);
v___x_3356_ = lean_array_push(v___x_3355_, v___x_3350_);
v___x_3357_ = lean_array_push(v___x_3356_, v___x_3351_);
v___x_3358_ = lean_array_push(v___x_3357_, v___x_3352_);
v___x_3359_ = lean_array_push(v___x_3358_, v___x_3353_);
v_val_3360_ = l_Lean_mkAppN(v___x_3349_, v___x_3359_);
lean_dec_ref(v___x_3359_);
v___x_3361_ = l_Lean_declareBuiltin(v_declName_3343_, v_val_3360_, v_a_3345_, v_a_3346_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object* v_addFnName_3362_, lean_object* v_catName_3363_, lean_object* v_declName_3364_, lean_object* v_prio_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3362_, v_catName_3363_, v_declName_3364_, v_prio_3365_, v_a_3366_, v_a_3367_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* v_catName_3375_, lean_object* v_declName_3376_, lean_object* v_prio_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = ((lean_object*)(l_Lean_Parser_declareLeadingBuiltinParser___closed__1));
v___x_3382_ = l_Lean_Parser_declareBuiltinParser(v___x_3381_, v_catName_3375_, v_declName_3376_, v_prio_3377_, v_a_3378_, v_a_3379_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object* v_catName_3383_, lean_object* v_declName_3384_, lean_object* v_prio_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3383_, v_declName_3384_, v_prio_3385_, v_a_3386_, v_a_3387_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* v_catName_3395_, lean_object* v_declName_3396_, lean_object* v_prio_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = ((lean_object*)(l_Lean_Parser_declareTrailingBuiltinParser___closed__1));
v___x_3402_ = l_Lean_Parser_declareBuiltinParser(v___x_3401_, v_catName_3395_, v_declName_3396_, v_prio_3397_, v_a_3398_, v_a_3399_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object* v_catName_3403_, lean_object* v_declName_3404_, lean_object* v_prio_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3403_, v_declName_3404_, v_prio_3405_, v_a_3406_, v_a_3407_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* v_args_3416_){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3417_ = l_Lean_Syntax_getNumArgs(v_args_3416_);
v___x_3418_ = lean_unsigned_to_nat(0u);
v___x_3419_ = lean_nat_dec_eq(v___x_3417_, v___x_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3420_ = lean_unsigned_to_nat(1u);
v___x_3421_ = lean_nat_dec_eq(v___x_3417_, v___x_3420_);
lean_dec(v___x_3417_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; 
v___x_3422_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__1));
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = l_Lean_Syntax_getArg(v_args_3416_, v___x_3418_);
v___x_3424_ = l_Lean_Syntax_isNatLit_x3f(v___x_3423_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3425_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__2));
v___x_3426_ = l_Lean_Syntax_formatStx(v___x_3423_, v___x_3424_, v___x_3419_);
v___x_3427_ = l_Std_Format_defWidth;
v___x_3428_ = l_Std_Format_pretty(v___x_3426_, v___x_3427_, v___x_3418_, v___x_3418_);
v___x_3429_ = lean_string_append(v___x_3425_, v___x_3428_);
lean_dec_ref(v___x_3428_);
v___x_3430_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3431_ = lean_string_append(v___x_3429_, v___x_3430_);
v___x_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
return v___x_3432_;
}
else
{
lean_object* v_val_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_dec(v___x_3423_);
v_val_3433_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3424_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_val_3433_);
lean_dec(v___x_3424_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_val_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
}
else
{
lean_object* v___x_3441_; 
lean_dec(v___x_3417_);
v___x_3441_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__3));
return v___x_3441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* v_args_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Lean_Parser_getParserPriority(v_args_3442_);
lean_dec(v_args_3442_);
return v_res_3443_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0));
v___x_3446_ = l_Lean_stringToMessageData(v___x_3445_);
return v___x_3446_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2));
v___x_3449_ = l_Lean_stringToMessageData(v___x_3448_);
return v___x_3449_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3451_ = l_Lean_stringToMessageData(v___x_3450_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object* v_name_3455_, uint8_t v_kind_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___y_3466_; 
v___x_3460_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1);
v___x_3461_ = l_Lean_MessageData_ofName(v_name_3455_);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3462_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
switch(v_kind_3456_)
{
case 0:
{
lean_object* v___x_3473_; 
v___x_3473_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5));
v___y_3466_ = v___x_3473_;
goto v___jp_3465_;
}
case 1:
{
lean_object* v___x_3474_; 
v___x_3474_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6));
v___y_3466_ = v___x_3474_;
goto v___jp_3465_;
}
default: 
{
lean_object* v___x_3475_; 
v___x_3475_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7));
v___y_3466_ = v___x_3475_;
goto v___jp_3465_;
}
}
v___jp_3465_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
lean_inc_ref(v___y_3466_);
v___x_3467_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___y_3466_);
v___x_3468_ = l_Lean_MessageData_ofFormat(v___x_3467_);
v___x_3469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3464_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3469_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3471_, v___y_3457_, v___y_3458_);
return v___x_3472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object* v_name_3476_, lean_object* v_kind_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
uint8_t v_kind_boxed_3481_; lean_object* v_res_3482_; 
v_kind_boxed_3481_ = lean_unbox(v_kind_3477_);
v_res_3482_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3476_, v_kind_boxed_3481_, v___y_3478_, v___y_3479_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3483_, lean_object* v_msg_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_fileName_3488_; lean_object* v_fileMap_3489_; lean_object* v_options_3490_; lean_object* v_currRecDepth_3491_; lean_object* v_maxRecDepth_3492_; lean_object* v_ref_3493_; lean_object* v_currNamespace_3494_; lean_object* v_openDecls_3495_; lean_object* v_initHeartbeats_3496_; lean_object* v_maxHeartbeats_3497_; lean_object* v_quotContext_3498_; lean_object* v_currMacroScope_3499_; uint8_t v_diag_3500_; lean_object* v_cancelTk_x3f_3501_; uint8_t v_suppressElabErrors_3502_; lean_object* v_inheritedTraceOptions_3503_; lean_object* v_ref_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_fileName_3488_ = lean_ctor_get(v___y_3485_, 0);
v_fileMap_3489_ = lean_ctor_get(v___y_3485_, 1);
v_options_3490_ = lean_ctor_get(v___y_3485_, 2);
v_currRecDepth_3491_ = lean_ctor_get(v___y_3485_, 3);
v_maxRecDepth_3492_ = lean_ctor_get(v___y_3485_, 4);
v_ref_3493_ = lean_ctor_get(v___y_3485_, 5);
v_currNamespace_3494_ = lean_ctor_get(v___y_3485_, 6);
v_openDecls_3495_ = lean_ctor_get(v___y_3485_, 7);
v_initHeartbeats_3496_ = lean_ctor_get(v___y_3485_, 8);
v_maxHeartbeats_3497_ = lean_ctor_get(v___y_3485_, 9);
v_quotContext_3498_ = lean_ctor_get(v___y_3485_, 10);
v_currMacroScope_3499_ = lean_ctor_get(v___y_3485_, 11);
v_diag_3500_ = lean_ctor_get_uint8(v___y_3485_, sizeof(void*)*14);
v_cancelTk_x3f_3501_ = lean_ctor_get(v___y_3485_, 12);
v_suppressElabErrors_3502_ = lean_ctor_get_uint8(v___y_3485_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3503_ = lean_ctor_get(v___y_3485_, 13);
v_ref_3504_ = l_Lean_replaceRef(v_ref_3483_, v_ref_3493_);
lean_inc_ref(v_inheritedTraceOptions_3503_);
lean_inc(v_cancelTk_x3f_3501_);
lean_inc(v_currMacroScope_3499_);
lean_inc(v_quotContext_3498_);
lean_inc(v_maxHeartbeats_3497_);
lean_inc(v_initHeartbeats_3496_);
lean_inc(v_openDecls_3495_);
lean_inc(v_currNamespace_3494_);
lean_inc(v_maxRecDepth_3492_);
lean_inc(v_currRecDepth_3491_);
lean_inc_ref(v_options_3490_);
lean_inc_ref(v_fileMap_3489_);
lean_inc_ref(v_fileName_3488_);
v___x_3505_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3505_, 0, v_fileName_3488_);
lean_ctor_set(v___x_3505_, 1, v_fileMap_3489_);
lean_ctor_set(v___x_3505_, 2, v_options_3490_);
lean_ctor_set(v___x_3505_, 3, v_currRecDepth_3491_);
lean_ctor_set(v___x_3505_, 4, v_maxRecDepth_3492_);
lean_ctor_set(v___x_3505_, 5, v_ref_3504_);
lean_ctor_set(v___x_3505_, 6, v_currNamespace_3494_);
lean_ctor_set(v___x_3505_, 7, v_openDecls_3495_);
lean_ctor_set(v___x_3505_, 8, v_initHeartbeats_3496_);
lean_ctor_set(v___x_3505_, 9, v_maxHeartbeats_3497_);
lean_ctor_set(v___x_3505_, 10, v_quotContext_3498_);
lean_ctor_set(v___x_3505_, 11, v_currMacroScope_3499_);
lean_ctor_set(v___x_3505_, 12, v_cancelTk_x3f_3501_);
lean_ctor_set(v___x_3505_, 13, v_inheritedTraceOptions_3503_);
lean_ctor_set_uint8(v___x_3505_, sizeof(void*)*14, v_diag_3500_);
lean_ctor_set_uint8(v___x_3505_, sizeof(void*)*14 + 1, v_suppressElabErrors_3502_);
v___x_3506_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_3484_, v___x_3505_, v___y_3486_);
lean_dec_ref_known(v___x_3505_, 14);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3507_, lean_object* v_msg_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3507_, v_msg_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v_ref_3507_);
return v_res_3512_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_3515_ = l_Lean_stringToMessageData(v___x_3514_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_3518_ = l_Lean_stringToMessageData(v___x_3517_);
return v___x_3518_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_3521_ = l_Lean_stringToMessageData(v___x_3520_);
return v___x_3521_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_3524_ = l_Lean_stringToMessageData(v___x_3523_);
return v___x_3524_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_3527_ = l_Lean_stringToMessageData(v___x_3526_);
return v___x_3527_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_3530_ = l_Lean_stringToMessageData(v___x_3529_);
return v___x_3530_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_3533_ = l_Lean_stringToMessageData(v___x_3532_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_3534_, lean_object* v_declHint_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v___x_3538_; lean_object* v_env_3539_; uint8_t v___y_3541_; uint8_t v___x_3597_; uint8_t v___x_3598_; 
v___x_3538_ = lean_st_ref_get(v___y_3536_);
v_env_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc_ref(v_env_3539_);
lean_dec(v___x_3538_);
v___x_3597_ = l_Lean_Name_isAnonymous(v_declHint_3535_);
v___x_3598_ = lean_bool_not(v___x_3597_);
if (v___x_3598_ == 0)
{
v___y_3541_ = v___x_3598_;
goto v___jp_3540_;
}
else
{
uint8_t v_isExporting_3599_; 
v_isExporting_3599_ = lean_ctor_get_uint8(v_env_3539_, sizeof(void*)*8);
v___y_3541_ = v_isExporting_3599_;
goto v___jp_3540_;
}
v___jp_3540_:
{
if (v___y_3541_ == 0)
{
lean_object* v___x_3542_; 
lean_dec_ref(v_env_3539_);
lean_dec(v_declHint_3535_);
v___x_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3542_, 0, v_msg_3534_);
return v___x_3542_;
}
else
{
uint8_t v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3543_ = 0;
lean_inc_ref(v_env_3539_);
v___x_3544_ = l_Lean_Environment_setExporting(v_env_3539_, v___x_3543_);
lean_inc(v_declHint_3535_);
lean_inc_ref(v___x_3544_);
v___x_3545_ = l_Lean_Environment_contains(v___x_3544_, v_declHint_3535_, v___y_3541_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; 
lean_dec_ref(v___x_3544_);
lean_dec_ref(v_env_3539_);
lean_dec(v_declHint_3535_);
v___x_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3546_, 0, v_msg_3534_);
return v___x_3546_;
}
else
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v_c_3552_; lean_object* v___x_3553_; 
v___x_3547_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_3548_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__5);
v___x_3549_ = l_Lean_Options_empty;
v___x_3550_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3544_);
lean_ctor_set(v___x_3550_, 1, v___x_3547_);
lean_ctor_set(v___x_3550_, 2, v___x_3548_);
lean_ctor_set(v___x_3550_, 3, v___x_3549_);
lean_inc(v_declHint_3535_);
v___x_3551_ = l_Lean_MessageData_ofConstName(v_declHint_3535_, v___x_3543_);
v_c_3552_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3552_, 0, v___x_3550_);
lean_ctor_set(v_c_3552_, 1, v___x_3551_);
v___x_3553_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3539_, v_declHint_3535_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
lean_dec_ref(v_env_3539_);
lean_dec(v_declHint_3535_);
v___x_3554_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v_c_3552_);
v___x_3556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_3557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3555_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = l_Lean_MessageData_note(v___x_3557_);
v___x_3559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3559_, 0, v_msg_3534_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
return v___x_3560_;
}
else
{
lean_object* v_val_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3596_; 
v_val_3561_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3563_ = v___x_3553_;
v_isShared_3564_ = v_isSharedCheck_3596_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_val_3561_);
lean_dec(v___x_3553_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3596_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v_mod_3568_; uint8_t v___x_3569_; 
v___x_3565_ = lean_box(0);
v___x_3566_ = l_Lean_Environment_header(v_env_3539_);
lean_dec_ref(v_env_3539_);
v___x_3567_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3566_);
v_mod_3568_ = lean_array_get(v___x_3565_, v___x_3567_, v_val_3561_);
lean_dec(v_val_3561_);
lean_dec_ref(v___x_3567_);
v___x_3569_ = l_Lean_isPrivateName(v_declHint_3535_);
lean_dec(v_declHint_3535_);
if (v___x_3569_ == 0)
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
v___x_3570_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
lean_ctor_set(v___x_3571_, 1, v_c_3552_);
v___x_3572_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_3573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3571_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = l_Lean_MessageData_ofName(v_mod_3568_);
v___x_3575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3573_);
lean_ctor_set(v___x_3575_, 1, v___x_3574_);
v___x_3576_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_3577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3575_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
v___x_3578_ = l_Lean_MessageData_note(v___x_3577_);
v___x_3579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3579_, 0, v_msg_3534_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set_tag(v___x_3563_, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3579_);
v___x_3581_ = v___x_3563_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3583_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
lean_ctor_set(v___x_3584_, 1, v_c_3552_);
v___x_3585_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_3586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3584_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = l_Lean_MessageData_ofName(v_mod_3568_);
v___x_3588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3586_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
v___x_3589_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_3590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3588_);
lean_ctor_set(v___x_3590_, 1, v___x_3589_);
v___x_3591_ = l_Lean_MessageData_note(v___x_3590_);
v___x_3592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3592_, 0, v_msg_3534_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set_tag(v___x_3563_, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3592_);
v___x_3594_ = v___x_3563_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_3600_, lean_object* v_declHint_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3600_, v_declHint_3601_, v___y_3602_);
lean_dec(v___y_3602_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_3605_, lean_object* v_declHint_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v___x_3610_; lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3620_; 
v___x_3610_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3605_, v_declHint_3606_, v___y_3608_);
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3620_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3620_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3618_; 
v___x_3615_ = l_Lean_unknownIdentifierMessageTag;
v___x_3616_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
lean_ctor_set(v___x_3616_, 1, v_a_3611_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v___x_3616_);
v___x_3618_ = v___x_3613_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3616_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_3621_, lean_object* v_declHint_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3621_, v_declHint_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3627_, lean_object* v_msg_3628_, lean_object* v_declHint_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v___x_3633_; lean_object* v_a_3634_; lean_object* v___x_3635_; 
v___x_3633_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3628_, v_declHint_3629_, v___y_3630_, v___y_3631_);
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref(v___x_3633_);
v___x_3635_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3627_, v_a_3634_, v___y_3630_, v___y_3631_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3636_, lean_object* v_msg_3637_, lean_object* v_declHint_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3636_, v_msg_3637_, v_declHint_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v_ref_3636_);
return v_res_3642_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_3644_ = l_Lean_stringToMessageData(v___x_3643_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3645_, lean_object* v_constName_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v___x_3650_; uint8_t v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3650_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3651_ = 0;
lean_inc(v_constName_3646_);
v___x_3652_ = l_Lean_MessageData_ofConstName(v_constName_3646_, v___x_3651_);
v___x_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3650_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3653_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3645_, v___x_3655_, v_constName_3646_, v___y_3647_, v___y_3648_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3657_, lean_object* v_constName_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3657_, v_constName_3658_, v___y_3659_, v___y_3660_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v_ref_3657_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object* v_constName_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_ref_3667_; lean_object* v___x_3668_; 
v_ref_3667_ = lean_ctor_get(v___y_3664_, 5);
v___x_3668_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3667_, v_constName_3663_, v___y_3664_, v___y_3665_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object* v_constName_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v___x_3678_; lean_object* v_env_3679_; uint8_t v___x_3680_; lean_object* v___x_3681_; 
v___x_3678_ = lean_st_ref_get(v___y_3676_);
v_env_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc_ref(v_env_3679_);
lean_dec(v___x_3678_);
v___x_3680_ = 0;
lean_inc(v_constName_3674_);
v___x_3681_ = l_Lean_Environment_find_x3f(v_env_3679_, v_constName_3674_, v___x_3680_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3674_, v___y_3675_, v___y_3676_);
return v___x_3682_;
}
else
{
lean_object* v_val_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec(v_constName_3674_);
v_val_3683_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3681_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_val_3683_);
lean_dec(v___x_3681_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set_tag(v___x_3685_, 0);
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_val_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object* v_constName_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3691_, v___y_3692_, v___y_3693_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
return v_res_3695_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1(void){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0));
v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
return v___x_3698_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3(void){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2));
v___x_3701_ = l_Lean_stringToMessageData(v___x_3700_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* v_attrName_3702_, lean_object* v_catName_3703_, lean_object* v_declName_3704_, lean_object* v_stx_3705_, uint8_t v_kind_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_){
_start:
{
lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Attribute_Builtin_getPrio(v_stx_3705_, v_a_3707_, v_a_3708_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v___y_3733_; lean_object* v___y_3734_; uint8_t v___x_3762_; uint8_t v___x_3763_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref_known(v___x_3730_, 1);
v___x_3762_ = 0;
v___x_3763_ = l_Lean_instBEqAttributeKind_beq(v_kind_3706_, v___x_3762_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; 
lean_dec(v_a_3731_);
lean_dec(v_declName_3704_);
lean_dec(v_catName_3703_);
v___x_3764_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_attrName_3702_, v_kind_3706_, v_a_3707_, v_a_3708_);
return v___x_3764_;
}
else
{
lean_dec(v_attrName_3702_);
v___y_3733_ = v_a_3707_;
v___y_3734_ = v_a_3708_;
goto v___jp_3732_;
}
v___jp_3732_:
{
lean_object* v___x_3735_; 
lean_inc(v_declName_3704_);
v___x_3735_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_declName_3704_, v___y_3733_, v___y_3734_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3737_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
v___x_3737_ = l_Lean_ConstantInfo_type(v_a_3736_);
if (lean_obj_tag(v___x_3737_) == 4)
{
lean_object* v_declName_3738_; 
v_declName_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_declName_3738_);
lean_dec_ref_known(v___x_3737_, 2);
if (lean_obj_tag(v_declName_3738_) == 1)
{
lean_object* v_pre_3739_; 
v_pre_3739_ = lean_ctor_get(v_declName_3738_, 0);
lean_inc(v_pre_3739_);
if (lean_obj_tag(v_pre_3739_) == 1)
{
lean_object* v_pre_3740_; 
v_pre_3740_ = lean_ctor_get(v_pre_3739_, 0);
lean_inc(v_pre_3740_);
if (lean_obj_tag(v_pre_3740_) == 1)
{
lean_object* v_pre_3741_; 
v_pre_3741_ = lean_ctor_get(v_pre_3740_, 0);
if (lean_obj_tag(v_pre_3741_) == 0)
{
lean_object* v_str_3742_; lean_object* v_str_3743_; lean_object* v_str_3744_; lean_object* v___x_3745_; uint8_t v___x_3746_; 
v_str_3742_ = lean_ctor_get(v_declName_3738_, 1);
lean_inc_ref(v_str_3742_);
lean_dec_ref_known(v_declName_3738_, 2);
v_str_3743_ = lean_ctor_get(v_pre_3739_, 1);
lean_inc_ref(v_str_3743_);
lean_dec_ref_known(v_pre_3739_, 2);
v_str_3744_ = lean_ctor_get(v_pre_3740_, 1);
lean_inc_ref(v_str_3744_);
lean_dec_ref_known(v_pre_3740_, 2);
v___x_3745_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3746_ = lean_string_dec_eq(v_str_3744_, v___x_3745_);
lean_dec_ref(v_str_3744_);
if (v___x_3746_ == 0)
{
lean_dec_ref(v_str_3743_);
lean_dec_ref(v_str_3742_);
lean_dec(v_a_3731_);
lean_dec(v_catName_3703_);
v___y_3717_ = v_a_3736_;
v___y_3718_ = v___y_3733_;
v___y_3719_ = v___y_3734_;
goto v___jp_3716_;
}
else
{
lean_object* v___x_3747_; uint8_t v___x_3748_; 
v___x_3747_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3748_ = lean_string_dec_eq(v_str_3743_, v___x_3747_);
lean_dec_ref(v_str_3743_);
if (v___x_3748_ == 0)
{
lean_dec_ref(v_str_3742_);
lean_dec(v_a_3731_);
lean_dec(v_catName_3703_);
v___y_3717_ = v_a_3736_;
v___y_3718_ = v___y_3733_;
v___y_3719_ = v___y_3734_;
goto v___jp_3716_;
}
else
{
lean_object* v___x_3749_; uint8_t v___x_3750_; 
v___x_3749_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_3750_ = lean_string_dec_eq(v_str_3742_, v___x_3749_);
if (v___x_3750_ == 0)
{
uint8_t v___x_3751_; 
v___x_3751_ = lean_string_dec_eq(v_str_3742_, v___x_3747_);
lean_dec_ref(v_str_3742_);
if (v___x_3751_ == 0)
{
lean_dec(v_a_3731_);
lean_dec(v_catName_3703_);
v___y_3717_ = v_a_3736_;
v___y_3718_ = v___y_3733_;
v___y_3719_ = v___y_3734_;
goto v___jp_3716_;
}
else
{
lean_object* v___x_3752_; 
lean_dec(v_a_3736_);
lean_inc(v_declName_3704_);
lean_inc(v_catName_3703_);
v___x_3752_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3703_, v_declName_3704_, v_a_3731_, v___y_3733_, v___y_3734_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_dec_ref_known(v___x_3752_, 1);
v___y_3711_ = v___y_3733_;
v___y_3712_ = v___y_3734_;
goto v___jp_3710_;
}
else
{
lean_dec(v_declName_3704_);
lean_dec(v_catName_3703_);
return v___x_3752_;
}
}
}
else
{
lean_object* v___x_3753_; 
lean_dec_ref(v_str_3742_);
lean_dec(v_a_3736_);
lean_inc(v_declName_3704_);
lean_inc(v_catName_3703_);
v___x_3753_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3703_, v_declName_3704_, v_a_3731_, v___y_3733_, v___y_3734_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_dec_ref_known(v___x_3753_, 1);
v___y_3711_ = v___y_3733_;
v___y_3712_ = v___y_3734_;
goto v___jp_3710_;
}
else
{
lean_dec(v_declName_3704_);
lean_dec(v_catName_3703_);
return v___x_3753_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3740_, 2);
lean_dec_ref_known(v_pre_3739_, 2);
lean_dec_ref_known(v_declName_3738_, 2);
lean_dec(v_a_3731_);
lean_dec(v_catName_3703_);
v___y_3717_ = v_a_3736_;
v___y_3718_ = v___y_3733_;
v___y_3719_ = v___y_3734_;
goto v___jp_3716_;
}
}
else
{
lean_dec_ref_known(v_pre_3739_, 2);
lean_dec(v_pre_3740_);
lean_dec_ref_known(v_declName_3738_, 2);
lean_dec(v_a_3731_);
lean_dec(v_catName_3703_);
v___y_3717_ = v_a_3736_;
v___y_3718_ = v___y_3733_;
v___y_3719_ = v___y_3734_;
goto v___jp_3716_;
}
}
else
{
lean_dec(v_pre_3739_);
lean_dec_ref_known(v_declName_3738_, 2);
lean_dec(v_a_3731_);
lean_dec(v_catName_3703_);
v___y_3717_ = v_a_3736_;
v___y_3718_ = v___y_3733_;
v___y_3719_ = v___y_3734_;
goto v___jp_3716_;
}
}
else
{
lean_dec(v_declName_3738_);
lean_dec(v_a_3731_);
lean_dec(v_catName_3703_);
v___y_3717_ = v_a_3736_;
v___y_3718_ = v___y_3733_;
v___y_3719_ = v___y_3734_;
goto v___jp_3716_;
}
}
else
{
lean_dec_ref(v___x_3737_);
lean_dec(v_a_3731_);
lean_dec(v_catName_3703_);
v___y_3717_ = v_a_3736_;
v___y_3718_ = v___y_3733_;
v___y_3719_ = v___y_3734_;
goto v___jp_3716_;
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec(v_a_3731_);
lean_dec(v_declName_3704_);
lean_dec(v_catName_3703_);
v_a_3754_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3735_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3735_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec(v_declName_3704_);
lean_dec(v_catName_3703_);
lean_dec(v_attrName_3702_);
v_a_3765_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3730_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3730_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
v___jp_3710_:
{
lean_object* v___x_3713_; 
lean_inc(v_declName_3704_);
v___x_3713_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_3704_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3713_) == 0)
{
uint8_t v___x_3714_; lean_object* v___x_3715_; 
lean_dec_ref_known(v___x_3713_, 1);
v___x_3714_ = 1;
v___x_3715_ = l_Lean_Parser_runParserAttributeHooks(v_catName_3703_, v_declName_3704_, v___x_3714_, v___y_3711_, v___y_3712_);
return v___x_3715_;
}
else
{
lean_dec(v_declName_3704_);
lean_dec(v_catName_3703_);
return v___x_3713_;
}
}
v___jp_3716_:
{
lean_object* v___x_3720_; uint8_t v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3720_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
v___x_3721_ = 0;
v___x_3722_ = l_Lean_MessageData_ofConstName(v_declName_3704_, v___x_3721_);
v___x_3723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3720_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
v___x_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = l_Lean_ConstantInfo_type(v___y_3717_);
lean_dec_ref(v___y_3717_);
v___x_3727_ = l_Lean_indentExpr(v___x_3726_);
v___x_3728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3725_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3728_, v___y_3718_, v___y_3719_);
return v___x_3729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* v_attrName_3773_, lean_object* v_catName_3774_, lean_object* v_declName_3775_, lean_object* v_stx_3776_, lean_object* v_kind_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
uint8_t v_kind_boxed_3781_; lean_object* v_res_3782_; 
v_kind_boxed_3781_ = lean_unbox(v_kind_3777_);
v_res_3782_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3773_, v_catName_3774_, v_declName_3775_, v_stx_3776_, v_kind_boxed_3781_, v_a_3778_, v_a_3779_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object* v_00_u03b1_3783_, lean_object* v_name_3784_, uint8_t v_kind_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3784_, v_kind_3785_, v___y_3786_, v___y_3787_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b1_3790_, lean_object* v_name_3791_, lean_object* v_kind_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
uint8_t v_kind_boxed_3796_; lean_object* v_res_3797_; 
v_kind_boxed_3796_ = lean_unbox(v_kind_3792_);
v_res_3797_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(v_00_u03b1_3790_, v_name_3791_, v_kind_boxed_3796_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object* v_00_u03b1_3798_, lean_object* v_constName_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3799_, v___y_3800_, v___y_3801_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3804_, lean_object* v_constName_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(v_00_u03b1_3804_, v_constName_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3810_, lean_object* v_ref_3811_, lean_object* v_constName_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3811_, v_constName_3812_, v___y_3813_, v___y_3814_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3817_, lean_object* v_ref_3818_, lean_object* v_constName_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(v_00_u03b1_3817_, v_ref_3818_, v_constName_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v_ref_3818_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3824_, lean_object* v_ref_3825_, lean_object* v_msg_3826_, lean_object* v_declHint_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v___x_3831_; 
v___x_3831_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3825_, v_msg_3826_, v_declHint_3827_, v___y_3828_, v___y_3829_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3832_, lean_object* v_ref_3833_, lean_object* v_msg_3834_, lean_object* v_declHint_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3832_, v_ref_3833_, v_msg_3834_, v_declHint_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v_ref_3833_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_3840_, lean_object* v_declHint_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3840_, v_declHint_3841_, v___y_3843_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_3846_, lean_object* v_declHint_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_3846_, v_declHint_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3852_, lean_object* v_ref_3853_, lean_object* v_msg_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3853_, v_msg_3854_, v___y_3855_, v___y_3856_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3859_, lean_object* v_ref_3860_, lean_object* v_msg_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3859_, v_ref_3860_, v_msg_3861_, v___y_3862_, v___y_3863_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v_ref_3860_);
return v_res_3865_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2(void){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0));
v___x_3873_ = l_Lean_mkAtom(v___x_3872_);
return v___x_3873_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3874_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2);
v___x_3875_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3876_ = lean_array_push(v___x_3875_, v___x_3874_);
return v___x_3876_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7));
v___x_3886_ = l_Lean_mkAtom(v___x_3885_);
return v___x_3886_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3887_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8);
v___x_3888_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3889_ = lean_array_push(v___x_3888_, v___x_3887_);
return v___x_3889_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3890_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9);
v___x_3891_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6));
v___x_3892_ = lean_box(2);
v___x_3893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
lean_ctor_set(v___x_3893_, 1, v___x_3891_);
lean_ctor_set(v___x_3893_, 2, v___x_3890_);
return v___x_3893_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3894_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10);
v___x_3895_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3);
v___x_3896_ = lean_array_push(v___x_3895_, v___x_3894_);
return v___x_3896_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3897_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11);
v___x_3898_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1));
v___x_3899_ = lean_box(2);
v___x_3900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
lean_ctor_set(v___x_3900_, 1, v___x_3898_);
lean_ctor_set(v___x_3900_, 2, v___x_3897_);
return v___x_3900_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3901_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12);
v___x_3902_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3903_ = lean_array_push(v___x_3902_, v___x_3901_);
return v___x_3903_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14(void){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3904_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13);
v___x_3905_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3906_ = lean_box(2);
v___x_3907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
lean_ctor_set(v___x_3907_, 1, v___x_3905_);
lean_ctor_set(v___x_3907_, 2, v___x_3904_);
return v___x_3907_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3908_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14);
v___x_3909_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3910_ = lean_array_push(v___x_3909_, v___x_3908_);
return v___x_3910_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3911_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15);
v___x_3912_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3913_ = lean_box(2);
v___x_3914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
lean_ctor_set(v___x_3914_, 1, v___x_3912_);
lean_ctor_set(v___x_3914_, 2, v___x_3911_);
return v___x_3914_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3915_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16);
v___x_3916_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3917_ = lean_array_push(v___x_3916_, v___x_3915_);
return v___x_3917_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3918_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17);
v___x_3919_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3920_ = lean_box(2);
v___x_3921_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
lean_ctor_set(v___x_3921_, 1, v___x_3919_);
lean_ctor_set(v___x_3921_, 2, v___x_3918_);
return v___x_3921_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object* v_attrName_3923_, lean_object* v_decl_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3928_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3929_ = l_Lean_MessageData_ofName(v_attrName_3923_);
v___x_3930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3928_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3930_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
v___x_3933_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3932_, v___y_3925_, v___y_3926_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object* v_attrName_3934_, lean_object* v_decl_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_3934_, v_decl_3935_, v___y_3936_, v___y_3937_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v_decl_3935_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object* v_attrName_3940_, lean_object* v_catName_3941_, lean_object* v_declName_3942_, lean_object* v_stx_3943_, uint8_t v_kind_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v___x_3948_; 
v___x_3948_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3940_, v_catName_3941_, v_declName_3942_, v_stx_3943_, v_kind_3944_, v___y_3945_, v___y_3946_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object* v_attrName_3949_, lean_object* v_catName_3950_, lean_object* v_declName_3951_, lean_object* v_stx_3952_, lean_object* v_kind_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
uint8_t v_kind_boxed_3957_; lean_object* v_res_3958_; 
v_kind_boxed_3957_ = lean_unbox(v_kind_3953_);
v_res_3958_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_3949_, v_catName_3950_, v_declName_3951_, v_stx_3952_, v_kind_boxed_3957_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
return v_res_3958_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__0));
v___x_3961_ = lean_mk_io_user_error(v___x_3960_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* v_attrName_3964_, lean_object* v_declName_3965_, uint8_t v_behavior_3966_, lean_object* v_ref_3967_){
_start:
{
if (lean_obj_tag(v_declName_3965_) == 1)
{
lean_object* v_pre_3972_; 
v_pre_3972_ = lean_ctor_get(v_declName_3965_, 0);
if (lean_obj_tag(v_pre_3972_) == 1)
{
lean_object* v_pre_3973_; 
v_pre_3973_ = lean_ctor_get(v_pre_3972_, 0);
if (lean_obj_tag(v_pre_3973_) == 1)
{
lean_object* v_pre_3974_; 
v_pre_3974_ = lean_ctor_get(v_pre_3973_, 0);
if (lean_obj_tag(v_pre_3974_) == 1)
{
lean_object* v_pre_3975_; 
v_pre_3975_ = lean_ctor_get(v_pre_3974_, 0);
if (lean_obj_tag(v_pre_3975_) == 0)
{
lean_object* v_str_3976_; lean_object* v_str_3977_; lean_object* v_str_3978_; lean_object* v_str_3979_; lean_object* v___x_3980_; uint8_t v___x_3981_; 
v_str_3976_ = lean_ctor_get(v_declName_3965_, 1);
v_str_3977_ = lean_ctor_get(v_pre_3972_, 1);
v_str_3978_ = lean_ctor_get(v_pre_3973_, 1);
v_str_3979_ = lean_ctor_get(v_pre_3974_, 1);
v___x_3980_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3981_ = lean_string_dec_eq(v_str_3979_, v___x_3980_);
if (v___x_3981_ == 0)
{
lean_dec_ref_known(v_declName_3965_, 2);
lean_dec(v_ref_3967_);
lean_dec(v_attrName_3964_);
goto v___jp_3969_;
}
else
{
lean_object* v___x_3982_; uint8_t v___x_3983_; 
v___x_3982_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3983_ = lean_string_dec_eq(v_str_3978_, v___x_3982_);
if (v___x_3983_ == 0)
{
lean_dec_ref_known(v_declName_3965_, 2);
lean_dec(v_ref_3967_);
lean_dec(v_attrName_3964_);
goto v___jp_3969_;
}
else
{
lean_object* v___x_3984_; uint8_t v___x_3985_; 
v___x_3984_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__2));
v___x_3985_ = lean_string_dec_eq(v_str_3977_, v___x_3984_);
if (v___x_3985_ == 0)
{
lean_dec_ref_known(v_declName_3965_, 2);
lean_dec(v_ref_3967_);
lean_dec(v_attrName_3964_);
goto v___jp_3969_;
}
else
{
lean_object* v___x_3986_; lean_object* v_catName_3987_; lean_object* v___x_3988_; 
v___x_3986_ = lean_box(0);
lean_inc_ref(v_str_3976_);
v_catName_3987_ = l_Lean_Name_str___override(v___x_3986_, v_str_3976_);
lean_inc(v_catName_3987_);
v___x_3988_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_3987_, v_declName_3965_, v_behavior_3966_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v___f_3989_; lean_object* v___f_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
lean_dec_ref_known(v___x_3988_, 1);
lean_inc_n(v_attrName_3964_, 2);
v___f_3989_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3989_, 0, v_attrName_3964_);
v___f_3990_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3990_, 0, v_attrName_3964_);
lean_closure_set(v___f_3990_, 1, v_catName_3987_);
v___x_3991_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__3));
v___x_3992_ = 1;
v___x_3993_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3993_, 0, v_ref_3967_);
lean_ctor_set(v___x_3993_, 1, v_attrName_3964_);
lean_ctor_set(v___x_3993_, 2, v___x_3991_);
lean_ctor_set_uint8(v___x_3993_, sizeof(void*)*3, v___x_3992_);
v___x_3994_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
lean_ctor_set(v___x_3994_, 1, v___f_3990_);
lean_ctor_set(v___x_3994_, 2, v___f_3989_);
v___x_3995_ = l_Lean_registerBuiltinAttribute(v___x_3994_);
return v___x_3995_;
}
else
{
lean_dec(v_catName_3987_);
lean_dec(v_ref_3967_);
lean_dec(v_attrName_3964_);
return v___x_3988_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_declName_3965_, 2);
lean_dec(v_ref_3967_);
lean_dec(v_attrName_3964_);
goto v___jp_3969_;
}
}
else
{
lean_dec_ref_known(v_declName_3965_, 2);
lean_dec(v_ref_3967_);
lean_dec(v_attrName_3964_);
goto v___jp_3969_;
}
}
else
{
lean_dec_ref_known(v_declName_3965_, 2);
lean_dec(v_ref_3967_);
lean_dec(v_attrName_3964_);
goto v___jp_3969_;
}
}
else
{
lean_dec_ref_known(v_declName_3965_, 2);
lean_dec(v_ref_3967_);
lean_dec(v_attrName_3964_);
goto v___jp_3969_;
}
}
else
{
lean_dec(v_ref_3967_);
lean_dec(v_declName_3965_);
lean_dec(v_attrName_3964_);
goto v___jp_3969_;
}
v___jp_3969_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___closed__1, &l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
v___x_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
return v___x_3971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* v_attrName_3996_, lean_object* v_declName_3997_, lean_object* v_behavior_3998_, lean_object* v_ref_3999_, lean_object* v_a_4000_){
_start:
{
uint8_t v_behavior_boxed_4001_; lean_object* v_res_4002_; 
v_behavior_boxed_4001_ = lean_unbox(v_behavior_3998_);
v_res_4002_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_3996_, v_declName_3997_, v_behavior_boxed_4001_, v_ref_3999_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object* v_kind_4003_, lean_object* v_x_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v___x_4008_; lean_object* v_env_4009_; lean_object* v_nextMacroScope_4010_; lean_object* v_ngen_4011_; lean_object* v_auxDeclNGen_4012_; lean_object* v_traceState_4013_; lean_object* v_messages_4014_; lean_object* v_infoState_4015_; lean_object* v_snapshotTasks_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4028_; 
v___x_4008_ = lean_st_ref_take(v___y_4006_);
v_env_4009_ = lean_ctor_get(v___x_4008_, 0);
v_nextMacroScope_4010_ = lean_ctor_get(v___x_4008_, 1);
v_ngen_4011_ = lean_ctor_get(v___x_4008_, 2);
v_auxDeclNGen_4012_ = lean_ctor_get(v___x_4008_, 3);
v_traceState_4013_ = lean_ctor_get(v___x_4008_, 4);
v_messages_4014_ = lean_ctor_get(v___x_4008_, 6);
v_infoState_4015_ = lean_ctor_get(v___x_4008_, 7);
v_snapshotTasks_4016_ = lean_ctor_get(v___x_4008_, 8);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4028_ == 0)
{
lean_object* v_unused_4029_; 
v_unused_4029_ = lean_ctor_get(v___x_4008_, 5);
lean_dec(v_unused_4029_);
v___x_4018_ = v___x_4008_;
v_isShared_4019_ = v_isSharedCheck_4028_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_snapshotTasks_4016_);
lean_inc(v_infoState_4015_);
lean_inc(v_messages_4014_);
lean_inc(v_traceState_4013_);
lean_inc(v_auxDeclNGen_4012_);
lean_inc(v_ngen_4011_);
lean_inc(v_nextMacroScope_4010_);
lean_inc(v_env_4009_);
lean_dec(v___x_4008_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4028_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4023_; 
v___x_4020_ = l_Lean_Parser_addSyntaxNodeKind(v_env_4009_, v_kind_4003_);
v___x_4021_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__2);
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 5, v___x_4021_);
lean_ctor_set(v___x_4018_, 0, v___x_4020_);
v___x_4023_ = v___x_4018_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4020_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v_nextMacroScope_4010_);
lean_ctor_set(v_reuseFailAlloc_4027_, 2, v_ngen_4011_);
lean_ctor_set(v_reuseFailAlloc_4027_, 3, v_auxDeclNGen_4012_);
lean_ctor_set(v_reuseFailAlloc_4027_, 4, v_traceState_4013_);
lean_ctor_set(v_reuseFailAlloc_4027_, 5, v___x_4021_);
lean_ctor_set(v_reuseFailAlloc_4027_, 6, v_messages_4014_);
lean_ctor_set(v_reuseFailAlloc_4027_, 7, v_infoState_4015_);
lean_ctor_set(v_reuseFailAlloc_4027_, 8, v_snapshotTasks_4016_);
v___x_4023_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4024_ = lean_st_ref_set(v___y_4006_, v___x_4023_);
v___x_4025_ = lean_box(0);
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4025_);
return v___x_4026_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object* v_kind_4030_, lean_object* v_x_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_4030_, v_x_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_4036_, lean_object* v_keys_4037_, lean_object* v_vals_4038_, lean_object* v_i_4039_, lean_object* v_acc_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v___x_4044_; uint8_t v___x_4045_; 
v___x_4044_ = lean_array_get_size(v_keys_4037_);
v___x_4045_ = lean_nat_dec_lt(v_i_4039_, v___x_4044_);
if (v___x_4045_ == 0)
{
lean_object* v___x_4046_; 
lean_dec(v_i_4039_);
lean_dec_ref(v_f_4036_);
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v_acc_4040_);
return v___x_4046_;
}
else
{
lean_object* v_k_4047_; lean_object* v_v_4048_; lean_object* v___x_4049_; 
v_k_4047_ = lean_array_fget_borrowed(v_keys_4037_, v_i_4039_);
v_v_4048_ = lean_array_fget_borrowed(v_vals_4038_, v_i_4039_);
lean_inc_ref(v_f_4036_);
lean_inc(v___y_4042_);
lean_inc_ref(v___y_4041_);
lean_inc(v_v_4048_);
lean_inc(v_k_4047_);
v___x_4049_ = lean_apply_6(v_f_4036_, v_acc_4040_, v_k_4047_, v_v_4048_, v___y_4041_, v___y_4042_, lean_box(0));
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___x_4049_, 1);
v___x_4051_ = lean_unsigned_to_nat(1u);
v___x_4052_ = lean_nat_add(v_i_4039_, v___x_4051_);
lean_dec(v_i_4039_);
v_i_4039_ = v___x_4052_;
v_acc_4040_ = v_a_4050_;
goto _start;
}
else
{
lean_dec(v_i_4039_);
lean_dec_ref(v_f_4036_);
return v___x_4049_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_4054_, lean_object* v_keys_4055_, lean_object* v_vals_4056_, lean_object* v_i_4057_, lean_object* v_acc_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4054_, v_keys_4055_, v_vals_4056_, v_i_4057_, v_acc_4058_, v___y_4059_, v___y_4060_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec_ref(v_vals_4056_);
lean_dec_ref(v_keys_4055_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object* v_f_4063_, lean_object* v_x_4064_, lean_object* v_x_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
if (lean_obj_tag(v_x_4064_) == 0)
{
lean_object* v_es_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4089_; 
v_es_4069_ = lean_ctor_get(v_x_4064_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_x_4064_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4071_ = v_x_4064_;
v_isShared_4072_ = v_isSharedCheck_4089_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_es_4069_);
lean_dec(v_x_4064_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4089_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; uint8_t v___x_4075_; 
v___x_4073_ = lean_unsigned_to_nat(0u);
v___x_4074_ = lean_array_get_size(v_es_4069_);
v___x_4075_ = lean_nat_dec_lt(v___x_4073_, v___x_4074_);
if (v___x_4075_ == 0)
{
lean_object* v___x_4077_; 
lean_dec_ref(v_es_4069_);
lean_dec_ref(v_f_4063_);
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 0, v_x_4065_);
v___x_4077_ = v___x_4071_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_x_4065_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
else
{
uint8_t v___x_4079_; 
v___x_4079_ = lean_nat_dec_le(v___x_4074_, v___x_4074_);
if (v___x_4079_ == 0)
{
if (v___x_4075_ == 0)
{
lean_object* v___x_4081_; 
lean_dec_ref(v_es_4069_);
lean_dec_ref(v_f_4063_);
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 0, v_x_4065_);
v___x_4081_ = v___x_4071_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_x_4065_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
else
{
size_t v___x_4083_; size_t v___x_4084_; lean_object* v___x_4085_; 
lean_del_object(v___x_4071_);
v___x_4083_ = ((size_t)0ULL);
v___x_4084_ = lean_usize_of_nat(v___x_4074_);
v___x_4085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4063_, v_es_4069_, v___x_4083_, v___x_4084_, v_x_4065_, v___y_4066_, v___y_4067_);
lean_dec_ref(v_es_4069_);
return v___x_4085_;
}
}
else
{
size_t v___x_4086_; size_t v___x_4087_; lean_object* v___x_4088_; 
lean_del_object(v___x_4071_);
v___x_4086_ = ((size_t)0ULL);
v___x_4087_ = lean_usize_of_nat(v___x_4074_);
v___x_4088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4063_, v_es_4069_, v___x_4086_, v___x_4087_, v_x_4065_, v___y_4066_, v___y_4067_);
lean_dec_ref(v_es_4069_);
return v___x_4088_;
}
}
}
}
else
{
lean_object* v_ks_4090_; lean_object* v_vs_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v_ks_4090_ = lean_ctor_get(v_x_4064_, 0);
lean_inc_ref(v_ks_4090_);
v_vs_4091_ = lean_ctor_get(v_x_4064_, 1);
lean_inc_ref(v_vs_4091_);
lean_dec_ref_known(v_x_4064_, 2);
v___x_4092_ = lean_unsigned_to_nat(0u);
v___x_4093_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4063_, v_ks_4090_, v_vs_4091_, v___x_4092_, v_x_4065_, v___y_4066_, v___y_4067_);
lean_dec_ref(v_vs_4091_);
lean_dec_ref(v_ks_4090_);
return v___x_4093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_4094_, lean_object* v_as_4095_, size_t v_i_4096_, size_t v_stop_4097_, lean_object* v_b_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v_a_4103_; lean_object* v___y_4108_; uint8_t v___x_4110_; 
v___x_4110_ = lean_usize_dec_eq(v_i_4096_, v_stop_4097_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4111_; 
v___x_4111_ = lean_array_uget_borrowed(v_as_4095_, v_i_4096_);
switch(lean_obj_tag(v___x_4111_))
{
case 0:
{
lean_object* v_key_4112_; lean_object* v_val_4113_; lean_object* v___x_4114_; 
v_key_4112_ = lean_ctor_get(v___x_4111_, 0);
v_val_4113_ = lean_ctor_get(v___x_4111_, 1);
lean_inc_ref(v_f_4094_);
lean_inc(v___y_4100_);
lean_inc_ref(v___y_4099_);
lean_inc(v_val_4113_);
lean_inc(v_key_4112_);
v___x_4114_ = lean_apply_6(v_f_4094_, v_b_4098_, v_key_4112_, v_val_4113_, v___y_4099_, v___y_4100_, lean_box(0));
v___y_4108_ = v___x_4114_;
goto v___jp_4107_;
}
case 1:
{
lean_object* v_node_4115_; lean_object* v___x_4116_; 
v_node_4115_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_node_4115_);
lean_inc_ref(v_f_4094_);
v___x_4116_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4094_, v_node_4115_, v_b_4098_, v___y_4099_, v___y_4100_);
v___y_4108_ = v___x_4116_;
goto v___jp_4107_;
}
default: 
{
v_a_4103_ = v_b_4098_;
goto v___jp_4102_;
}
}
}
else
{
lean_object* v___x_4117_; 
lean_dec_ref(v_f_4094_);
v___x_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4117_, 0, v_b_4098_);
return v___x_4117_;
}
v___jp_4102_:
{
size_t v___x_4104_; size_t v___x_4105_; 
v___x_4104_ = ((size_t)1ULL);
v___x_4105_ = lean_usize_add(v_i_4096_, v___x_4104_);
v_i_4096_ = v___x_4105_;
v_b_4098_ = v_a_4103_;
goto _start;
}
v___jp_4107_:
{
if (lean_obj_tag(v___y_4108_) == 0)
{
lean_object* v_a_4109_; 
v_a_4109_ = lean_ctor_get(v___y_4108_, 0);
lean_inc(v_a_4109_);
lean_dec_ref_known(v___y_4108_, 1);
v_a_4103_ = v_a_4109_;
goto v___jp_4102_;
}
else
{
lean_dec_ref(v_f_4094_);
return v___y_4108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_4118_, lean_object* v_as_4119_, lean_object* v_i_4120_, lean_object* v_stop_4121_, lean_object* v_b_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
size_t v_i_boxed_4126_; size_t v_stop_boxed_4127_; lean_object* v_res_4128_; 
v_i_boxed_4126_ = lean_unbox_usize(v_i_4120_);
lean_dec(v_i_4120_);
v_stop_boxed_4127_ = lean_unbox_usize(v_stop_4121_);
lean_dec(v_stop_4121_);
v_res_4128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4118_, v_as_4119_, v_i_boxed_4126_, v_stop_boxed_4127_, v_b_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec_ref(v_as_4119_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_4129_, lean_object* v_x_4130_, lean_object* v_x_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4129_, v_x_4130_, v_x_4131_, v___y_4132_, v___y_4133_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object* v_f_4136_, lean_object* v_x_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v___x_4143_; 
lean_inc(v___y_4141_);
lean_inc_ref(v___y_4140_);
v___x_4143_ = lean_apply_5(v_f_4136_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, lean_box(0));
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object* v_f_4144_, lean_object* v_x_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4144_, v_x_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object* v_map_4152_, lean_object* v_f_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v___f_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___f_4157_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4157_, 0, v_f_4153_);
v___x_4158_ = lean_box(0);
v___x_4159_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v___f_4157_, v_map_4152_, v___x_4158_, v___y_4154_, v___y_4155_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object* v_map_4160_, lean_object* v_f_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4160_, v_f_4161_, v___y_4162_, v___y_4163_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
return v_res_4165_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4167_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0));
v___x_4168_ = l_Lean_stringToMessageData(v___x_4167_);
return v___x_4168_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4169_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_4170_ = l_Lean_stringToMessageData(v___x_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t v_attrKind_4171_, lean_object* v_declName_4172_, lean_object* v_as_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
if (lean_obj_tag(v_as_4173_) == 0)
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_dec(v_declName_4172_);
v___x_4177_ = lean_box(0);
v___x_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
return v___x_4178_;
}
else
{
lean_object* v_head_4179_; lean_object* v_tail_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4210_; 
v_head_4179_ = lean_ctor_get(v_as_4173_, 0);
v_tail_4180_ = lean_ctor_get(v_as_4173_, 1);
v_isSharedCheck_4210_ = !lean_is_exclusive(v_as_4173_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4182_ = v_as_4173_;
v_isShared_4183_ = v_isSharedCheck_4210_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_tail_4180_);
lean_inc(v_head_4179_);
lean_dec(v_as_4173_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4210_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___y_4185_; lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_Parser_addToken(v_head_4179_, v_attrKind_4171_, v___y_4174_, v___y_4175_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_del_object(v___x_4182_);
v___y_4185_ = v___x_4187_;
goto v___jp_4184_;
}
else
{
lean_object* v_a_4188_; uint8_t v___y_4190_; uint8_t v___x_4208_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_a_4188_);
v___x_4208_ = l_Lean_Exception_isInterrupt(v_a_4188_);
if (v___x_4208_ == 0)
{
uint8_t v___x_4209_; 
lean_inc(v_a_4188_);
v___x_4209_ = l_Lean_Exception_isRuntime(v_a_4188_);
v___y_4190_ = v___x_4209_;
goto v___jp_4189_;
}
else
{
v___y_4190_ = v___x_4208_;
goto v___jp_4189_;
}
v___jp_4189_:
{
if (v___y_4190_ == 0)
{
if (lean_obj_tag(v_a_4188_) == 0)
{
lean_object* v_msg_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4206_; 
lean_dec_ref_known(v___x_4187_, 1);
v_msg_4191_ = lean_ctor_get(v_a_4188_, 1);
v_isSharedCheck_4206_ = !lean_is_exclusive(v_a_4188_);
if (v_isSharedCheck_4206_ == 0)
{
lean_object* v_unused_4207_; 
v_unused_4207_ = lean_ctor_get(v_a_4188_, 0);
lean_dec(v_unused_4207_);
v___x_4193_ = v_a_4188_;
v_isShared_4194_ = v_isSharedCheck_4206_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_msg_4191_);
lean_dec(v_a_4188_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4206_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4198_; 
v___x_4195_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1);
lean_inc(v_declName_4172_);
v___x_4196_ = l_Lean_MessageData_ofConstName(v_declName_4172_, v___y_4190_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set_tag(v___x_4193_, 7);
lean_ctor_set(v___x_4193_, 1, v___x_4196_);
lean_ctor_set(v___x_4193_, 0, v___x_4195_);
v___x_4198_ = v___x_4193_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v___x_4195_);
lean_ctor_set(v_reuseFailAlloc_4205_, 1, v___x_4196_);
v___x_4198_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
lean_object* v___x_4199_; lean_object* v___x_4201_; 
v___x_4199_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2);
if (v_isShared_4183_ == 0)
{
lean_ctor_set_tag(v___x_4182_, 7);
lean_ctor_set(v___x_4182_, 1, v___x_4199_);
lean_ctor_set(v___x_4182_, 0, v___x_4198_);
v___x_4201_ = v___x_4182_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v___x_4198_);
lean_ctor_set(v_reuseFailAlloc_4204_, 1, v___x_4199_);
v___x_4201_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
lean_ctor_set(v___x_4202_, 1, v_msg_4191_);
v___x_4203_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4202_, v___y_4174_, v___y_4175_);
v___y_4185_ = v___x_4203_;
goto v___jp_4184_;
}
}
}
}
else
{
lean_dec(v_a_4188_);
lean_del_object(v___x_4182_);
v___y_4185_ = v___x_4187_;
goto v___jp_4184_;
}
}
else
{
lean_dec(v_a_4188_);
lean_del_object(v___x_4182_);
v___y_4185_ = v___x_4187_;
goto v___jp_4184_;
}
}
}
v___jp_4184_:
{
if (lean_obj_tag(v___y_4185_) == 0)
{
lean_dec_ref_known(v___y_4185_, 1);
v_as_4173_ = v_tail_4180_;
goto _start;
}
else
{
lean_dec(v_tail_4180_);
lean_dec(v_declName_4172_);
return v___y_4185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object* v_attrKind_4211_, lean_object* v_declName_4212_, lean_object* v_as_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
uint8_t v_attrKind_boxed_4217_; lean_object* v_res_4218_; 
v_attrKind_boxed_4217_ = lean_unbox(v_attrKind_4211_);
v_res_4218_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_boxed_4217_, v_declName_4212_, v_as_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object* v_catName_4220_, lean_object* v_declName_4221_, lean_object* v_stx_4222_, uint8_t v_attrKind_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_){
_start:
{
lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4222_, v_a_4224_, v_a_4225_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v_env_4236_; lean_object* v___x_4237_; lean_object* v_ext_4238_; lean_object* v_toEnvExtension_4239_; lean_object* v_asyncMode_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v_categories_4243_; lean_object* v_env_4244_; lean_object* v_options_4245_; lean_object* v_ref_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref_known(v___x_4232_, 1);
v___x_4234_ = lean_st_ref_get(v_a_4225_);
v___x_4235_ = lean_st_ref_get(v_a_4225_);
v_env_4236_ = lean_ctor_get(v___x_4234_, 0);
lean_inc_ref(v_env_4236_);
lean_dec(v___x_4234_);
v___x_4237_ = l_Lean_Parser_parserExtension;
v_ext_4238_ = lean_ctor_get(v___x_4237_, 1);
v_toEnvExtension_4239_ = lean_ctor_get(v_ext_4238_, 0);
v_asyncMode_4240_ = lean_ctor_get(v_toEnvExtension_4239_, 2);
v___x_4241_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4242_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4241_, v___x_4237_, v_env_4236_, v_asyncMode_4240_);
v_categories_4243_ = lean_ctor_get(v___x_4242_, 2);
lean_inc_ref_n(v_categories_4243_, 2);
lean_dec(v___x_4242_);
v_env_4244_ = lean_ctor_get(v___x_4235_, 0);
lean_inc_ref(v_env_4244_);
lean_dec(v___x_4235_);
v_options_4245_ = lean_ctor_get(v_a_4224_, 2);
v_ref_4246_ = lean_ctor_get(v_a_4224_, 5);
lean_inc_ref(v_options_4245_);
v___x_4247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4247_, 0, v_env_4244_);
lean_ctor_set(v___x_4247_, 1, v_options_4245_);
lean_inc(v_declName_4221_);
v___x_4248_ = l_Lean_Parser_mkParserOfConstant(v_categories_4243_, v_declName_4221_, v___x_4247_);
lean_dec_ref_known(v___x_4247_, 2);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v_snd_4250_; lean_object* v_info_4251_; lean_object* v_fst_4252_; lean_object* v_collectTokens_4253_; lean_object* v_collectKinds_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_a_4249_);
lean_dec_ref_known(v___x_4248_, 1);
v_snd_4250_ = lean_ctor_get(v_a_4249_, 1);
lean_inc(v_snd_4250_);
v_info_4251_ = lean_ctor_get(v_snd_4250_, 0);
v_fst_4252_ = lean_ctor_get(v_a_4249_, 0);
lean_inc(v_fst_4252_);
lean_dec(v_a_4249_);
v_collectTokens_4253_ = lean_ctor_get(v_info_4251_, 0);
v_collectKinds_4254_ = lean_ctor_get(v_info_4251_, 1);
v___x_4255_ = lean_box(0);
lean_inc_ref(v_collectTokens_4253_);
v___x_4256_ = lean_apply_1(v_collectTokens_4253_, v___x_4255_);
lean_inc(v_declName_4221_);
v___x_4257_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4223_, v_declName_4221_, v___x_4256_, v_a_4224_, v_a_4225_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v___f_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
lean_dec_ref_known(v___x_4257_, 1);
v___f_4258_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0));
v___x_4259_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
lean_inc_ref(v_collectKinds_4254_);
v___x_4260_ = lean_apply_1(v_collectKinds_4254_, v___x_4259_);
v___x_4261_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v___x_4260_, v___f_4258_, v_a_4224_, v_a_4225_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v___x_4262_; uint8_t v___x_4263_; uint8_t v___x_4264_; lean_object* v___x_4265_; 
lean_dec_ref_known(v___x_4261_, 1);
lean_inc(v_a_4233_);
lean_inc(v_snd_4250_);
lean_inc_n(v_declName_4221_, 2);
lean_inc_n(v_catName_4220_, 2);
v___x_4262_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_4262_, 0, v_catName_4220_);
lean_ctor_set(v___x_4262_, 1, v_declName_4221_);
lean_ctor_set(v___x_4262_, 2, v_snd_4250_);
lean_ctor_set(v___x_4262_, 3, v_a_4233_);
v___x_4263_ = lean_unbox(v_fst_4252_);
lean_ctor_set_uint8(v___x_4262_, sizeof(void*)*4, v___x_4263_);
v___x_4264_ = lean_unbox(v_fst_4252_);
lean_dec(v_fst_4252_);
v___x_4265_ = l_Lean_Parser_addParser(v_categories_4243_, v_catName_4220_, v_declName_4221_, v___x_4264_, v_snd_4250_, v_a_4233_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4275_; 
lean_dec_ref_known(v___x_4262_, 4);
lean_dec(v_declName_4221_);
lean_dec(v_catName_4220_);
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4268_ = v___x_4265_;
v_isShared_4269_ = v_isSharedCheck_4275_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___x_4265_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4275_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
lean_ctor_set_tag(v___x_4268_, 3);
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_a_4266_);
v___x_4271_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4272_ = l_Lean_MessageData_ofFormat(v___x_4271_);
v___x_4273_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4272_, v_a_4224_, v_a_4225_);
return v___x_4273_;
}
}
}
else
{
lean_object* v___x_4276_; 
lean_dec_ref_known(v___x_4265_, 1);
v___x_4276_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_4237_, v___x_4262_, v_attrKind_4223_, v_a_4224_, v_a_4225_);
lean_dec_ref(v___x_4276_);
v___y_4228_ = v_a_4224_;
v___y_4229_ = v_a_4225_;
goto v___jp_4227_;
}
}
else
{
lean_dec(v_fst_4252_);
lean_dec(v_snd_4250_);
lean_dec_ref(v_categories_4243_);
lean_dec(v_a_4233_);
lean_dec(v_declName_4221_);
lean_dec(v_catName_4220_);
return v___x_4261_;
}
}
else
{
lean_dec(v_fst_4252_);
lean_dec(v_snd_4250_);
lean_dec_ref(v_categories_4243_);
lean_dec(v_a_4233_);
lean_dec(v_declName_4221_);
lean_dec(v_catName_4220_);
return v___x_4257_;
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4288_; 
lean_dec_ref(v_categories_4243_);
lean_dec(v_a_4233_);
lean_dec(v_declName_4221_);
lean_dec(v_catName_4220_);
v_a_4277_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4279_ = v___x_4248_;
v_isShared_4280_ = v_isSharedCheck_4288_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4248_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4288_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4286_; 
v___x_4281_ = lean_io_error_to_string(v_a_4277_);
v___x_4282_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4281_);
v___x_4283_ = l_Lean_MessageData_ofFormat(v___x_4282_);
lean_inc(v_ref_4246_);
v___x_4284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4284_, 0, v_ref_4246_);
lean_ctor_set(v___x_4284_, 1, v___x_4283_);
if (v_isShared_4280_ == 0)
{
lean_ctor_set(v___x_4279_, 0, v___x_4284_);
v___x_4286_ = v___x_4279_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4284_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec(v_declName_4221_);
lean_dec(v_catName_4220_);
v_a_4289_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4232_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4232_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
v___jp_4227_:
{
uint8_t v___x_4230_; lean_object* v___x_4231_; 
v___x_4230_ = 0;
v___x_4231_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4220_, v_declName_4221_, v___x_4230_, v___y_4228_, v___y_4229_);
return v___x_4231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object* v_catName_4297_, lean_object* v_declName_4298_, lean_object* v_stx_4299_, lean_object* v_attrKind_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_){
_start:
{
uint8_t v_attrKind_boxed_4304_; lean_object* v_res_4305_; 
v_attrKind_boxed_4304_ = lean_unbox(v_attrKind_4300_);
v_res_4305_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4297_, v_declName_4298_, v_stx_4299_, v_attrKind_boxed_4304_, v_a_4301_, v_a_4302_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* v___attrName_4306_, lean_object* v_catName_4307_, lean_object* v_declName_4308_, lean_object* v_stx_4309_, uint8_t v_attrKind_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_){
_start:
{
lean_object* v___x_4314_; 
v___x_4314_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4307_, v_declName_4308_, v_stx_4309_, v_attrKind_4310_, v_a_4311_, v_a_4312_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* v___attrName_4315_, lean_object* v_catName_4316_, lean_object* v_declName_4317_, lean_object* v_stx_4318_, lean_object* v_attrKind_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_){
_start:
{
uint8_t v_attrKind_boxed_4323_; lean_object* v_res_4324_; 
v_attrKind_boxed_4323_ = lean_unbox(v_attrKind_4319_);
v_res_4324_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4315_, v_catName_4316_, v_declName_4317_, v_stx_4318_, v_attrKind_boxed_4323_, v_a_4320_, v_a_4321_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
lean_dec(v___attrName_4315_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object* v_00_u03b2_4325_, lean_object* v_map_4326_, lean_object* v_f_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4326_, v_f_4327_, v___y_4328_, v___y_4329_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b2_4332_, lean_object* v_map_4333_, lean_object* v_f_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(v_00_u03b2_4332_, v_map_4333_, v_f_4334_, v___y_4335_, v___y_4336_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object* v_map_4339_, lean_object* v_f_4340_, lean_object* v_init_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
lean_object* v___x_4345_; 
v___x_4345_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4340_, v_map_4339_, v_init_4341_, v___y_4342_, v___y_4343_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object* v_map_4346_, lean_object* v_f_4347_, lean_object* v_init_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4346_, v_f_4347_, v_init_4348_, v___y_4349_, v___y_4350_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object* v_00_u03c3_4353_, lean_object* v_00_u03b2_4354_, lean_object* v_map_4355_, lean_object* v_f_4356_, lean_object* v_init_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4356_, v_map_4355_, v_init_4357_, v___y_4358_, v___y_4359_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object* v_00_u03c3_4362_, lean_object* v_00_u03b2_4363_, lean_object* v_map_4364_, lean_object* v_f_4365_, lean_object* v_init_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(v_00_u03c3_4362_, v_00_u03b2_4363_, v_map_4364_, v_f_4365_, v_init_4366_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_4371_, lean_object* v_00_u03b1_4372_, lean_object* v_00_u03b2_4373_, lean_object* v_f_4374_, lean_object* v_x_4375_, lean_object* v_x_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4374_, v_x_4375_, v_x_4376_, v___y_4377_, v___y_4378_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03c3_4381_, lean_object* v_00_u03b1_4382_, lean_object* v_00_u03b2_4383_, lean_object* v_f_4384_, lean_object* v_x_4385_, lean_object* v_x_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(v_00_u03c3_4381_, v_00_u03b1_4382_, v_00_u03b2_4383_, v_f_4384_, v_x_4385_, v_x_4386_, v___y_4387_, v___y_4388_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4391_, lean_object* v_00_u03b2_4392_, lean_object* v_00_u03c3_4393_, lean_object* v_f_4394_, lean_object* v_as_4395_, size_t v_i_4396_, size_t v_stop_4397_, lean_object* v_b_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4394_, v_as_4395_, v_i_4396_, v_stop_4397_, v_b_4398_, v___y_4399_, v___y_4400_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4403_, lean_object* v_00_u03b2_4404_, lean_object* v_00_u03c3_4405_, lean_object* v_f_4406_, lean_object* v_as_4407_, lean_object* v_i_4408_, lean_object* v_stop_4409_, lean_object* v_b_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
size_t v_i_boxed_4414_; size_t v_stop_boxed_4415_; lean_object* v_res_4416_; 
v_i_boxed_4414_ = lean_unbox_usize(v_i_4408_);
lean_dec(v_i_4408_);
v_stop_boxed_4415_ = lean_unbox_usize(v_stop_4409_);
lean_dec(v_stop_4409_);
v_res_4416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4403_, v_00_u03b2_4404_, v_00_u03c3_4405_, v_f_4406_, v_as_4407_, v_i_boxed_4414_, v_stop_boxed_4415_, v_b_4410_, v___y_4411_, v___y_4412_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec_ref(v_as_4407_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_4417_, lean_object* v_00_u03b1_4418_, lean_object* v_00_u03b2_4419_, lean_object* v_f_4420_, lean_object* v_keys_4421_, lean_object* v_vals_4422_, lean_object* v_heq_4423_, lean_object* v_i_4424_, lean_object* v_acc_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v___x_4429_; 
v___x_4429_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4420_, v_keys_4421_, v_vals_4422_, v_i_4424_, v_acc_4425_, v___y_4426_, v___y_4427_);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_4430_, lean_object* v_00_u03b1_4431_, lean_object* v_00_u03b2_4432_, lean_object* v_f_4433_, lean_object* v_keys_4434_, lean_object* v_vals_4435_, lean_object* v_heq_4436_, lean_object* v_i_4437_, lean_object* v_acc_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4430_, v_00_u03b1_4431_, v_00_u03b2_4432_, v_f_4433_, v_keys_4434_, v_vals_4435_, v_heq_4436_, v_i_4437_, v_acc_4438_, v___y_4439_, v___y_4440_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec_ref(v_vals_4435_);
lean_dec_ref(v_keys_4434_);
return v_res_4442_;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___auto__1(void){
_start:
{
lean_object* v___x_4443_; 
v___x_4443_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object* v_catName_4444_, lean_object* v_declName_4445_, lean_object* v_stx_4446_, uint8_t v_attrKind_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v___x_4451_; 
v___x_4451_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4444_, v_declName_4445_, v_stx_4446_, v_attrKind_4447_, v___y_4448_, v___y_4449_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object* v_catName_4452_, lean_object* v_declName_4453_, lean_object* v_stx_4454_, lean_object* v_attrKind_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
uint8_t v_attrKind_boxed_4459_; lean_object* v_res_4460_; 
v_attrKind_boxed_4459_ = lean_unbox(v_attrKind_4455_);
v_res_4460_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4452_, v_declName_4453_, v_stx_4454_, v_attrKind_boxed_4459_, v___y_4456_, v___y_4457_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* v_attrName_4462_, lean_object* v_catName_4463_, lean_object* v_ref_4464_){
_start:
{
lean_object* v___f_4465_; lean_object* v___f_4466_; lean_object* v___x_4467_; uint8_t v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___f_4465_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4465_, 0, v_catName_4463_);
lean_inc(v_attrName_4462_);
v___f_4466_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4466_, 0, v_attrName_4462_);
v___x_4467_ = ((lean_object*)(l_Lean_Parser_mkParserAttributeImpl___closed__0));
v___x_4468_ = 1;
v___x_4469_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4469_, 0, v_ref_4464_);
lean_ctor_set(v___x_4469_, 1, v_attrName_4462_);
lean_ctor_set(v___x_4469_, 2, v___x_4467_);
lean_ctor_set_uint8(v___x_4469_, sizeof(void*)*3, v___x_4468_);
v___x_4470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
lean_ctor_set(v___x_4470_, 1, v___f_4465_);
lean_ctor_set(v___x_4470_, 2, v___f_4466_);
return v___x_4470_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4471_; 
v___x_4471_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* v_attrName_4472_, lean_object* v_catName_4473_, lean_object* v_ref_4474_){
_start:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = l_Lean_Parser_mkParserAttributeImpl(v_attrName_4472_, v_catName_4473_, v_ref_4474_);
v___x_4477_ = l_Lean_registerBuiltinAttribute(v___x_4476_);
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object* v_attrName_4478_, lean_object* v_catName_4479_, lean_object* v_ref_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4478_, v_catName_4479_, v_ref_4480_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object* v_ref_4486_, lean_object* v_args_4487_){
_start:
{
if (lean_obj_tag(v_args_4487_) == 1)
{
lean_object* v_head_4490_; 
v_head_4490_ = lean_ctor_get(v_args_4487_, 0);
lean_inc(v_head_4490_);
if (lean_obj_tag(v_head_4490_) == 2)
{
lean_object* v_tail_4491_; 
v_tail_4491_ = lean_ctor_get(v_args_4487_, 1);
lean_inc(v_tail_4491_);
lean_dec_ref_known(v_args_4487_, 2);
if (lean_obj_tag(v_tail_4491_) == 1)
{
lean_object* v_head_4492_; 
v_head_4492_ = lean_ctor_get(v_tail_4491_, 0);
lean_inc(v_head_4492_);
if (lean_obj_tag(v_head_4492_) == 2)
{
lean_object* v_tail_4493_; 
v_tail_4493_ = lean_ctor_get(v_tail_4491_, 1);
lean_inc(v_tail_4493_);
lean_dec_ref_known(v_tail_4491_, 2);
if (lean_obj_tag(v_tail_4493_) == 0)
{
lean_object* v_v_4494_; lean_object* v_v_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4503_; 
v_v_4494_ = lean_ctor_get(v_head_4490_, 0);
lean_inc(v_v_4494_);
lean_dec_ref_known(v_head_4490_, 1);
v_v_4495_ = lean_ctor_get(v_head_4492_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v_head_4492_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4497_ = v_head_4492_;
v_isShared_4498_ = v_isSharedCheck_4503_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_v_4495_);
lean_dec(v_head_4492_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4503_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; lean_object* v___x_4501_; 
v___x_4499_ = l_Lean_Parser_mkParserAttributeImpl(v_v_4494_, v_v_4495_, v_ref_4486_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set_tag(v___x_4497_, 1);
lean_ctor_set(v___x_4497_, 0, v___x_4499_);
v___x_4501_ = v___x_4497_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4499_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
else
{
lean_dec(v_tail_4493_);
lean_dec_ref_known(v_head_4492_, 1);
lean_dec_ref_known(v_head_4490_, 1);
lean_dec(v_ref_4486_);
goto v___jp_4488_;
}
}
else
{
lean_dec(v_head_4492_);
lean_dec_ref_known(v_tail_4491_, 2);
lean_dec_ref_known(v_head_4490_, 1);
lean_dec(v_ref_4486_);
goto v___jp_4488_;
}
}
else
{
lean_dec_ref_known(v_head_4490_, 1);
lean_dec(v_tail_4491_);
lean_dec(v_ref_4486_);
goto v___jp_4488_;
}
}
else
{
lean_dec_ref_known(v_args_4487_, 2);
lean_dec(v_head_4490_);
lean_dec(v_ref_4486_);
goto v___jp_4488_;
}
}
else
{
lean_dec(v_args_4487_);
lean_dec(v_ref_4486_);
goto v___jp_4488_;
}
v___jp_4488_:
{
lean_object* v___x_4489_; 
v___x_4489_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
return v___x_4489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___f_4509_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4510_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4511_ = l_Lean_registerAttributeImplBuilder(v___x_4510_, v___f_4509_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object* v_a_4512_){
_start:
{
lean_object* v_res_4513_; 
v_res_4513_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
return v_res_4513_;
}
}
static lean_object* _init_l_Lean_Parser_registerParserCategory___auto__1(void){
_start:
{
lean_object* v___x_4514_; 
v___x_4514_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object* v_env_4515_, lean_object* v_attrName_4516_, lean_object* v_catName_4517_, uint8_t v_behavior_4518_, lean_object* v_ref_4519_){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
lean_inc(v_ref_4519_);
lean_inc(v_catName_4517_);
v___x_4521_ = l_Lean_Parser_addParserCategory(v_env_4515_, v_catName_4517_, v_ref_4519_, v_behavior_4518_);
v___x_4522_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_4521_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4536_; 
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4525_ = v___x_4522_;
v_isShared_4526_ = v_isSharedCheck_4536_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4522_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4536_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4527_; lean_object* v___x_4529_; 
v___x_4527_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
if (v_isShared_4526_ == 0)
{
lean_ctor_set_tag(v___x_4525_, 2);
lean_ctor_set(v___x_4525_, 0, v_attrName_4516_);
v___x_4529_ = v___x_4525_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_attrName_4516_);
v___x_4529_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4530_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4530_, 0, v_catName_4517_);
v___x_4531_ = lean_box(0);
v___x_4532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4532_, 0, v___x_4530_);
lean_ctor_set(v___x_4532_, 1, v___x_4531_);
v___x_4533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4529_);
lean_ctor_set(v___x_4533_, 1, v___x_4532_);
v___x_4534_ = l_Lean_registerAttributeOfBuilder(v_a_4523_, v___x_4527_, v_ref_4519_, v___x_4533_);
return v___x_4534_;
}
}
}
else
{
lean_dec(v_ref_4519_);
lean_dec(v_catName_4517_);
lean_dec(v_attrName_4516_);
return v___x_4522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* v_env_4537_, lean_object* v_attrName_4538_, lean_object* v_catName_4539_, lean_object* v_behavior_4540_, lean_object* v_ref_4541_, lean_object* v_a_4542_){
_start:
{
uint8_t v_behavior_boxed_4543_; lean_object* v_res_4544_; 
v_behavior_boxed_4543_ = lean_unbox(v_behavior_4540_);
v_res_4544_ = l_Lean_Parser_registerParserCategory(v_env_4537_, v_attrName_4538_, v_catName_4539_, v_behavior_boxed_4543_, v_ref_4541_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; uint8_t v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4567_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4568_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4569_ = 0;
v___x_4570_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4571_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4567_, v___x_4568_, v___x_4569_, v___x_4570_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object* v_a_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
return v_res_4573_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4579_ = lean_unsigned_to_nat(3431364690u);
v___x_4580_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4581_ = l_Lean_Name_num___override(v___x_4580_, v___x_4579_);
return v___x_4581_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4582_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4583_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4584_ = l_Lean_Name_str___override(v___x_4583_, v___x_4582_);
return v___x_4584_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4585_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4586_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4587_ = l_Lean_Name_str___override(v___x_4586_, v___x_4585_);
return v___x_4587_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4588_ = lean_unsigned_to_nat(2u);
v___x_4589_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4590_ = l_Lean_Name_num___override(v___x_4589_, v___x_4588_);
return v___x_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4592_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4593_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4594_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4595_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4592_, v___x_4593_, v___x_4594_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object* v_a_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
return v_res_4597_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4607_ = lean_unsigned_to_nat(2342493449u);
v___x_4608_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4609_ = l_Lean_Name_num___override(v___x_4608_, v___x_4607_);
return v___x_4609_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4610_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4611_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4612_ = l_Lean_Name_str___override(v___x_4611_, v___x_4610_);
return v___x_4612_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4613_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4614_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4615_ = l_Lean_Name_str___override(v___x_4614_, v___x_4613_);
return v___x_4615_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4616_ = lean_unsigned_to_nat(2u);
v___x_4617_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4618_ = l_Lean_Name_num___override(v___x_4617_, v___x_4616_);
return v___x_4618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; uint8_t v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4620_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4621_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4622_ = 0;
v___x_4623_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4624_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4620_, v___x_4621_, v___x_4622_, v___x_4623_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object* v_a_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
return v_res_4626_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4632_ = lean_unsigned_to_nat(3226070615u);
v___x_4633_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4634_ = l_Lean_Name_num___override(v___x_4633_, v___x_4632_);
return v___x_4634_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4635_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4636_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4637_ = l_Lean_Name_str___override(v___x_4636_, v___x_4635_);
return v___x_4637_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4638_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4639_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4640_ = l_Lean_Name_str___override(v___x_4639_, v___x_4638_);
return v___x_4640_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4641_ = lean_unsigned_to_nat(2u);
v___x_4642_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4643_ = l_Lean_Name_num___override(v___x_4642_, v___x_4641_);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4645_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4646_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4647_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4648_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4645_, v___x_4646_, v___x_4647_);
return v___x_4648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object* v_a_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* v_rbp_4651_){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4652_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4653_ = l_Lean_Parser_categoryParser(v___x_4652_, v_rbp_4651_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t v_addOpenSimple_4654_, lean_object* v_x_4655_, lean_object* v_x_4656_){
_start:
{
if (lean_obj_tag(v_x_4656_) == 0)
{
return v_x_4655_;
}
else
{
lean_object* v_head_4657_; lean_object* v_tail_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4681_; 
v_head_4657_ = lean_ctor_get(v_x_4656_, 0);
v_tail_4658_ = lean_ctor_get(v_x_4656_, 1);
v_isSharedCheck_4681_ = !lean_is_exclusive(v_x_4656_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4660_ = v_x_4656_;
v_isShared_4661_ = v_isSharedCheck_4681_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_tail_4658_);
lean_inc(v_head_4657_);
lean_dec(v_x_4656_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4681_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v_fst_4662_; lean_object* v_snd_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4680_; 
v_fst_4662_ = lean_ctor_get(v_x_4655_, 0);
v_snd_4663_ = lean_ctor_get(v_x_4655_, 1);
v_isSharedCheck_4680_ = !lean_is_exclusive(v_x_4655_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4665_ = v_x_4655_;
v_isShared_4666_ = v_isSharedCheck_4680_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_snd_4663_);
lean_inc(v_fst_4662_);
lean_dec(v_x_4655_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4680_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___y_4668_; 
if (v_addOpenSimple_4654_ == 0)
{
lean_del_object(v___x_4660_);
v___y_4668_ = v_snd_4663_;
goto v___jp_4667_;
}
else
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4678_; 
v___x_4675_ = lean_box(0);
lean_inc(v_head_4657_);
v___x_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4676_, 0, v_head_4657_);
lean_ctor_set(v___x_4676_, 1, v___x_4675_);
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 1, v_snd_4663_);
lean_ctor_set(v___x_4660_, 0, v___x_4676_);
v___x_4678_ = v___x_4660_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
lean_ctor_set(v_reuseFailAlloc_4679_, 1, v_snd_4663_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
v___y_4668_ = v___x_4678_;
goto v___jp_4667_;
}
}
v___jp_4667_:
{
lean_object* v___x_4669_; lean_object* v_env_4670_; lean_object* v___x_4672_; 
v___x_4669_ = l_Lean_Parser_parserExtension;
v_env_4670_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v___x_4669_, v_fst_4662_, v_head_4657_);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 1, v___y_4668_);
lean_ctor_set(v___x_4665_, 0, v_env_4670_);
v___x_4672_ = v___x_4665_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_env_4670_);
lean_ctor_set(v_reuseFailAlloc_4674_, 1, v___y_4668_);
v___x_4672_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
v_x_4655_ = v___x_4672_;
v_x_4656_ = v_tail_4658_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object* v_addOpenSimple_4682_, lean_object* v_x_4683_, lean_object* v_x_4684_){
_start:
{
uint8_t v_addOpenSimple_boxed_4685_; lean_object* v_res_4686_; 
v_addOpenSimple_boxed_4685_ = lean_unbox(v_addOpenSimple_4682_);
v_res_4686_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_boxed_4685_, v_x_4683_, v_x_4684_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t v_addOpenSimple_4687_, lean_object* v_as_4688_, size_t v_i_4689_, size_t v_stop_4690_, lean_object* v_b_4691_){
_start:
{
uint8_t v___x_4692_; 
v___x_4692_ = lean_usize_dec_eq(v_i_4689_, v_stop_4690_);
if (v___x_4692_ == 0)
{
lean_object* v_toParserModuleContext_4693_; lean_object* v_toInputContext_4694_; lean_object* v_toCacheableParserContext_4695_; lean_object* v_tokens_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4723_; 
v_toParserModuleContext_4693_ = lean_ctor_get(v_b_4691_, 1);
v_toInputContext_4694_ = lean_ctor_get(v_b_4691_, 0);
v_toCacheableParserContext_4695_ = lean_ctor_get(v_b_4691_, 2);
v_tokens_4696_ = lean_ctor_get(v_b_4691_, 3);
v_isSharedCheck_4723_ = !lean_is_exclusive(v_b_4691_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4698_ = v_b_4691_;
v_isShared_4699_ = v_isSharedCheck_4723_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_tokens_4696_);
lean_inc(v_toCacheableParserContext_4695_);
lean_inc(v_toParserModuleContext_4693_);
lean_inc(v_toInputContext_4694_);
lean_dec(v_b_4691_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4723_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v_env_4700_; lean_object* v_options_4701_; lean_object* v_currNamespace_4702_; lean_object* v_openDecls_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4722_; 
v_env_4700_ = lean_ctor_get(v_toParserModuleContext_4693_, 0);
v_options_4701_ = lean_ctor_get(v_toParserModuleContext_4693_, 1);
v_currNamespace_4702_ = lean_ctor_get(v_toParserModuleContext_4693_, 2);
v_openDecls_4703_ = lean_ctor_get(v_toParserModuleContext_4693_, 3);
v_isSharedCheck_4722_ = !lean_is_exclusive(v_toParserModuleContext_4693_);
if (v_isSharedCheck_4722_ == 0)
{
v___x_4705_ = v_toParserModuleContext_4693_;
v_isShared_4706_ = v_isSharedCheck_4722_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_openDecls_4703_);
lean_inc(v_currNamespace_4702_);
lean_inc(v_options_4701_);
lean_inc(v_env_4700_);
lean_dec(v_toParserModuleContext_4693_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4722_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4707_; lean_object* v_nss_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v_fst_4711_; lean_object* v_snd_4712_; lean_object* v___x_4714_; 
v___x_4707_ = lean_array_uget_borrowed(v_as_4688_, v_i_4689_);
lean_inc(v___x_4707_);
lean_inc(v_openDecls_4703_);
lean_inc(v_currNamespace_4702_);
lean_inc_ref(v_env_4700_);
v_nss_4708_ = l_Lean_ResolveName_resolveNamespace(v_env_4700_, v_currNamespace_4702_, v_openDecls_4703_, v___x_4707_);
v___x_4709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4709_, 0, v_env_4700_);
lean_ctor_set(v___x_4709_, 1, v_openDecls_4703_);
v___x_4710_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4687_, v___x_4709_, v_nss_4708_);
v_fst_4711_ = lean_ctor_get(v___x_4710_, 0);
lean_inc(v_fst_4711_);
v_snd_4712_ = lean_ctor_get(v___x_4710_, 1);
lean_inc(v_snd_4712_);
lean_dec_ref(v___x_4710_);
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 3, v_snd_4712_);
lean_ctor_set(v___x_4705_, 0, v_fst_4711_);
v___x_4714_ = v___x_4705_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_fst_4711_);
lean_ctor_set(v_reuseFailAlloc_4721_, 1, v_options_4701_);
lean_ctor_set(v_reuseFailAlloc_4721_, 2, v_currNamespace_4702_);
lean_ctor_set(v_reuseFailAlloc_4721_, 3, v_snd_4712_);
v___x_4714_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
lean_object* v___x_4716_; 
if (v_isShared_4699_ == 0)
{
lean_ctor_set(v___x_4698_, 1, v___x_4714_);
v___x_4716_ = v___x_4698_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_toInputContext_4694_);
lean_ctor_set(v_reuseFailAlloc_4720_, 1, v___x_4714_);
lean_ctor_set(v_reuseFailAlloc_4720_, 2, v_toCacheableParserContext_4695_);
lean_ctor_set(v_reuseFailAlloc_4720_, 3, v_tokens_4696_);
v___x_4716_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
size_t v___x_4717_; size_t v___x_4718_; 
v___x_4717_ = ((size_t)1ULL);
v___x_4718_ = lean_usize_add(v_i_4689_, v___x_4717_);
v_i_4689_ = v___x_4718_;
v_b_4691_ = v___x_4716_;
goto _start;
}
}
}
}
}
else
{
return v_b_4691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object* v_addOpenSimple_4724_, lean_object* v_as_4725_, lean_object* v_i_4726_, lean_object* v_stop_4727_, lean_object* v_b_4728_){
_start:
{
uint8_t v_addOpenSimple_boxed_4729_; size_t v_i_boxed_4730_; size_t v_stop_boxed_4731_; lean_object* v_res_4732_; 
v_addOpenSimple_boxed_4729_ = lean_unbox(v_addOpenSimple_4724_);
v_i_boxed_4730_ = lean_unbox_usize(v_i_4726_);
lean_dec(v_i_4726_);
v_stop_boxed_4731_ = lean_unbox_usize(v_stop_4727_);
lean_dec(v_stop_4727_);
v_res_4732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_boxed_4729_, v_as_4725_, v_i_boxed_4730_, v_stop_boxed_4731_, v_b_4728_);
lean_dec_ref(v_as_4725_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object* v___x_4733_, lean_object* v_ids_4734_, uint8_t v_addOpenSimple_4735_, lean_object* v_c_4736_){
_start:
{
lean_object* v___y_4738_; lean_object* v___x_4757_; lean_object* v___x_4758_; uint8_t v___x_4759_; 
v___x_4757_ = lean_unsigned_to_nat(0u);
v___x_4758_ = lean_array_get_size(v_ids_4734_);
v___x_4759_ = lean_nat_dec_lt(v___x_4757_, v___x_4758_);
if (v___x_4759_ == 0)
{
v___y_4738_ = v_c_4736_;
goto v___jp_4737_;
}
else
{
uint8_t v___x_4760_; 
v___x_4760_ = lean_nat_dec_le(v___x_4758_, v___x_4758_);
if (v___x_4760_ == 0)
{
if (v___x_4759_ == 0)
{
v___y_4738_ = v_c_4736_;
goto v___jp_4737_;
}
else
{
size_t v___x_4761_; size_t v___x_4762_; lean_object* v___x_4763_; 
v___x_4761_ = ((size_t)0ULL);
v___x_4762_ = lean_usize_of_nat(v___x_4758_);
v___x_4763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4735_, v_ids_4734_, v___x_4761_, v___x_4762_, v_c_4736_);
v___y_4738_ = v___x_4763_;
goto v___jp_4737_;
}
}
else
{
size_t v___x_4764_; size_t v___x_4765_; lean_object* v___x_4766_; 
v___x_4764_ = ((size_t)0ULL);
v___x_4765_ = lean_usize_of_nat(v___x_4758_);
v___x_4766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4735_, v_ids_4734_, v___x_4764_, v___x_4765_, v_c_4736_);
v___y_4738_ = v___x_4766_;
goto v___jp_4737_;
}
}
v___jp_4737_:
{
lean_object* v_toParserModuleContext_4739_; lean_object* v_toInputContext_4740_; lean_object* v_toCacheableParserContext_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4755_; 
v_toParserModuleContext_4739_ = lean_ctor_get(v___y_4738_, 1);
v_toInputContext_4740_ = lean_ctor_get(v___y_4738_, 0);
v_toCacheableParserContext_4741_ = lean_ctor_get(v___y_4738_, 2);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___y_4738_);
if (v_isSharedCheck_4755_ == 0)
{
lean_object* v_unused_4756_; 
v_unused_4756_ = lean_ctor_get(v___y_4738_, 3);
lean_dec(v_unused_4756_);
v___x_4743_ = v___y_4738_;
v_isShared_4744_ = v_isSharedCheck_4755_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_toCacheableParserContext_4741_);
lean_inc(v_toParserModuleContext_4739_);
lean_inc(v_toInputContext_4740_);
lean_dec(v___y_4738_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4755_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v_env_4745_; lean_object* v___x_4746_; lean_object* v_ext_4747_; lean_object* v_toEnvExtension_4748_; lean_object* v_asyncMode_4749_; lean_object* v___x_4750_; lean_object* v_tokens_4751_; lean_object* v___x_4753_; 
v_env_4745_ = lean_ctor_get(v_toParserModuleContext_4739_, 0);
v___x_4746_ = l_Lean_Parser_parserExtension;
v_ext_4747_ = lean_ctor_get(v___x_4746_, 1);
v_toEnvExtension_4748_ = lean_ctor_get(v_ext_4747_, 0);
v_asyncMode_4749_ = lean_ctor_get(v_toEnvExtension_4748_, 2);
lean_inc_ref(v_env_4745_);
v___x_4750_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4733_, v___x_4746_, v_env_4745_, v_asyncMode_4749_);
v_tokens_4751_ = lean_ctor_get(v___x_4750_, 0);
lean_inc_ref(v_tokens_4751_);
lean_dec(v___x_4750_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 3, v_tokens_4751_);
v___x_4753_ = v___x_4743_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_toInputContext_4740_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v_toParserModuleContext_4739_);
lean_ctor_set(v_reuseFailAlloc_4754_, 2, v_toCacheableParserContext_4741_);
lean_ctor_set(v_reuseFailAlloc_4754_, 3, v_tokens_4751_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object* v___x_4767_, lean_object* v_ids_4768_, lean_object* v_addOpenSimple_4769_, lean_object* v_c_4770_){
_start:
{
uint8_t v_addOpenSimple_boxed_4771_; lean_object* v_res_4772_; 
v_addOpenSimple_boxed_4771_ = lean_unbox(v_addOpenSimple_4769_);
v_res_4772_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_4767_, v_ids_4768_, v_addOpenSimple_boxed_4771_, v_c_4770_);
lean_dec_ref(v_ids_4768_);
lean_dec_ref(v___x_4767_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* v_ids_4773_, uint8_t v_addOpenSimple_4774_, lean_object* v_p_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___f_4780_; lean_object* v___x_4781_; 
v___x_4778_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4779_ = lean_box(v_addOpenSimple_4774_);
v___f_4780_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4780_, 0, v___x_4778_);
lean_closure_set(v___f_4780_, 1, v_ids_4773_);
lean_closure_set(v___f_4780_, 2, v___x_4779_);
v___x_4781_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_4780_, v_p_4775_, v_a_4776_, v_a_4777_);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* v_ids_4782_, lean_object* v_addOpenSimple_4783_, lean_object* v_p_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_){
_start:
{
uint8_t v_addOpenSimple_boxed_4787_; lean_object* v_res_4788_; 
v_addOpenSimple_boxed_4787_ = lean_unbox(v_addOpenSimple_4783_);
v_res_4788_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_4782_, v_addOpenSimple_boxed_4787_, v_p_4784_, v_a_4785_, v_a_4786_);
return v_res_4788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t v_sz_4789_, size_t v_i_4790_, lean_object* v_bs_4791_){
_start:
{
uint8_t v___x_4792_; 
v___x_4792_ = lean_usize_dec_lt(v_i_4790_, v_sz_4789_);
if (v___x_4792_ == 0)
{
return v_bs_4791_;
}
else
{
lean_object* v_v_4793_; lean_object* v___x_4794_; lean_object* v_bs_x27_4795_; lean_object* v___x_4796_; size_t v___x_4797_; size_t v___x_4798_; lean_object* v___x_4799_; 
v_v_4793_ = lean_array_uget(v_bs_4791_, v_i_4790_);
v___x_4794_ = lean_unsigned_to_nat(0u);
v_bs_x27_4795_ = lean_array_uset(v_bs_4791_, v_i_4790_, v___x_4794_);
v___x_4796_ = l_Lean_Syntax_getId(v_v_4793_);
lean_dec(v_v_4793_);
v___x_4797_ = ((size_t)1ULL);
v___x_4798_ = lean_usize_add(v_i_4790_, v___x_4797_);
v___x_4799_ = lean_array_uset(v_bs_x27_4795_, v_i_4790_, v___x_4796_);
v_i_4790_ = v___x_4798_;
v_bs_4791_ = v___x_4799_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object* v_sz_4801_, lean_object* v_i_4802_, lean_object* v_bs_4803_){
_start:
{
size_t v_sz_boxed_4804_; size_t v_i_boxed_4805_; lean_object* v_res_4806_; 
v_sz_boxed_4804_ = lean_unbox_usize(v_sz_4801_);
lean_dec(v_sz_4801_);
v_i_boxed_4805_ = lean_unbox_usize(v_i_4802_);
lean_dec(v_i_4802_);
v_res_4806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_boxed_4804_, v_i_boxed_4805_, v_bs_4803_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* v_openDeclStx_4820_, lean_object* v_p_4821_, lean_object* v_c_4822_, lean_object* v_s_4823_){
_start:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; uint8_t v___x_4826_; 
lean_inc(v_openDeclStx_4820_);
v___x_4824_ = l_Lean_Syntax_getKind(v_openDeclStx_4820_);
v___x_4825_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__2));
v___x_4826_ = lean_name_eq(v___x_4824_, v___x_4825_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4827_; uint8_t v___x_4828_; 
v___x_4827_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__4));
v___x_4828_ = lean_name_eq(v___x_4824_, v___x_4827_);
lean_dec(v___x_4824_);
if (v___x_4828_ == 0)
{
lean_object* v___x_4829_; 
lean_dec(v_openDeclStx_4820_);
v___x_4829_ = lean_apply_2(v_p_4821_, v_c_4822_, v_s_4823_);
return v___x_4829_;
}
else
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; size_t v_sz_4833_; size_t v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___x_4830_ = lean_unsigned_to_nat(1u);
v___x_4831_ = l_Lean_Syntax_getArg(v_openDeclStx_4820_, v___x_4830_);
lean_dec(v_openDeclStx_4820_);
v___x_4832_ = l_Lean_Syntax_getArgs(v___x_4831_);
lean_dec(v___x_4831_);
v_sz_4833_ = lean_array_size(v___x_4832_);
v___x_4834_ = ((size_t)0ULL);
v___x_4835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4833_, v___x_4834_, v___x_4832_);
v___x_4836_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4835_, v___x_4826_, v_p_4821_, v_c_4822_, v_s_4823_);
return v___x_4836_;
}
}
else
{
lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; size_t v_sz_4840_; size_t v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
lean_dec(v___x_4824_);
v___x_4837_ = lean_unsigned_to_nat(0u);
v___x_4838_ = l_Lean_Syntax_getArg(v_openDeclStx_4820_, v___x_4837_);
lean_dec(v_openDeclStx_4820_);
v___x_4839_ = l_Lean_Syntax_getArgs(v___x_4838_);
lean_dec(v___x_4838_);
v_sz_4840_ = lean_array_size(v___x_4839_);
v___x_4841_ = ((size_t)0ULL);
v___x_4842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4840_, v___x_4841_, v___x_4839_);
v___x_4843_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4842_, v___x_4826_, v_p_4821_, v_c_4822_, v_s_4823_);
return v___x_4843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* v_p_4850_, lean_object* v_c_4851_, lean_object* v_s_4852_){
_start:
{
lean_object* v_stxStack_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; uint8_t v___x_4856_; 
v_stxStack_4853_ = lean_ctor_get(v_s_4852_, 0);
v___x_4854_ = lean_unsigned_to_nat(0u);
v___x_4855_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4853_);
v___x_4856_ = lean_nat_dec_lt(v___x_4854_, v___x_4855_);
lean_dec(v___x_4855_);
if (v___x_4856_ == 0)
{
lean_object* v___x_4857_; 
v___x_4857_ = lean_apply_2(v_p_4850_, v_c_4851_, v_s_4852_);
return v___x_4857_;
}
else
{
lean_object* v_stx_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; uint8_t v___x_4861_; 
v_stx_4858_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4853_);
lean_inc(v_stx_4858_);
v___x_4859_ = l_Lean_Syntax_getKind(v_stx_4858_);
v___x_4860_ = ((lean_object*)(l_Lean_Parser_withOpenFn___closed__1));
v___x_4861_ = lean_name_eq(v___x_4859_, v___x_4860_);
lean_dec(v___x_4859_);
if (v___x_4861_ == 0)
{
lean_object* v___x_4862_; 
lean_dec(v_stx_4858_);
v___x_4862_ = lean_apply_2(v_p_4850_, v_c_4851_, v_s_4852_);
return v___x_4862_;
}
else
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4863_ = lean_unsigned_to_nat(1u);
v___x_4864_ = l_Lean_Syntax_getArg(v_stx_4858_, v___x_4863_);
lean_dec(v_stx_4858_);
v___x_4865_ = l_Lean_Parser_withOpenDeclFnCore(v___x_4864_, v_p_4850_, v_c_4851_, v_s_4852_);
return v___x_4865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* v_p_4866_){
_start:
{
lean_object* v_info_4867_; lean_object* v_fn_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4876_; 
v_info_4867_ = lean_ctor_get(v_p_4866_, 0);
v_fn_4868_ = lean_ctor_get(v_p_4866_, 1);
v_isSharedCheck_4876_ = !lean_is_exclusive(v_p_4866_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4870_ = v_p_4866_;
v_isShared_4871_ = v_isSharedCheck_4876_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_fn_4868_);
lean_inc(v_info_4867_);
lean_dec(v_p_4866_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4876_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4872_; lean_object* v___x_4874_; 
v___x_4872_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(v___x_4872_, 0, v_fn_4868_);
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 1, v___x_4872_);
v___x_4874_ = v___x_4870_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_info_4867_);
lean_ctor_set(v_reuseFailAlloc_4875_, 1, v___x_4872_);
v___x_4874_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
return v___x_4874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* v_p_4877_, lean_object* v_c_4878_, lean_object* v_s_4879_){
_start:
{
lean_object* v_stxStack_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; uint8_t v___x_4883_; 
v_stxStack_4880_ = lean_ctor_get(v_s_4879_, 0);
v___x_4881_ = lean_unsigned_to_nat(0u);
v___x_4882_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4880_);
v___x_4883_ = lean_nat_dec_lt(v___x_4881_, v___x_4882_);
lean_dec(v___x_4882_);
if (v___x_4883_ == 0)
{
lean_object* v___x_4884_; 
v___x_4884_ = lean_apply_2(v_p_4877_, v_c_4878_, v_s_4879_);
return v___x_4884_;
}
else
{
lean_object* v_stx_4885_; lean_object* v___x_4886_; 
v_stx_4885_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4880_);
v___x_4886_ = l_Lean_Parser_withOpenDeclFnCore(v_stx_4885_, v_p_4877_, v_c_4878_, v_s_4879_);
return v___x_4886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* v_p_4887_){
_start:
{
lean_object* v_info_4888_; lean_object* v_fn_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4897_; 
v_info_4888_ = lean_ctor_get(v_p_4887_, 0);
v_fn_4889_ = lean_ctor_get(v_p_4887_, 1);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_p_4887_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4891_ = v_p_4887_;
v_isShared_4892_ = v_isSharedCheck_4897_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_fn_4889_);
lean_inc(v_info_4888_);
lean_dec(v_p_4887_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4897_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4893_; lean_object* v___x_4895_; 
v___x_4893_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(v___x_4893_, 0, v_fn_4889_);
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 1, v___x_4893_);
v___x_4895_ = v___x_4891_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_info_4888_);
lean_ctor_set(v_reuseFailAlloc_4896_, 1, v___x_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object* v_val_4904_){
_start:
{
lean_object* v___x_4912_; 
v___x_4912_ = l_Lean_Syntax_isStrLit_x3f(v_val_4904_);
if (lean_obj_tag(v___x_4912_) == 1)
{
lean_object* v_val_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4921_; 
v_val_4913_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4915_ = v___x_4912_;
v_isShared_4916_ = v_isSharedCheck_4921_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_val_4913_);
lean_dec(v___x_4912_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4921_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4917_; lean_object* v___x_4919_; 
v___x_4917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4917_, 0, v_val_4913_);
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 0, v___x_4917_);
v___x_4919_ = v___x_4915_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4917_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
else
{
lean_object* v___x_4922_; 
lean_dec(v___x_4912_);
v___x_4922_ = l_Lean_Syntax_isNatLit_x3f(v_val_4904_);
if (lean_obj_tag(v___x_4922_) == 1)
{
lean_object* v_val_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4931_; 
v_val_4923_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4925_ = v___x_4922_;
v_isShared_4926_ = v_isSharedCheck_4931_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_val_4923_);
lean_dec(v___x_4922_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4931_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4927_; lean_object* v___x_4929_; 
v___x_4927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4927_, 0, v_val_4923_);
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 0, v___x_4927_);
v___x_4929_ = v___x_4925_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4927_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
else
{
lean_dec(v___x_4922_);
if (lean_obj_tag(v_val_4904_) == 2)
{
lean_object* v_val_4932_; lean_object* v___x_4933_; uint8_t v___x_4934_; 
v_val_4932_ = lean_ctor_get(v_val_4904_, 1);
v___x_4933_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3));
v___x_4934_ = lean_string_dec_eq(v_val_4932_, v___x_4933_);
if (v___x_4934_ == 0)
{
goto v___jp_4905_;
}
else
{
lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4935_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4935_, 0, v___x_4934_);
v___x_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4935_);
return v___x_4936_;
}
}
else
{
goto v___jp_4905_;
}
}
}
v___jp_4905_:
{
if (lean_obj_tag(v_val_4904_) == 2)
{
lean_object* v_val_4906_; lean_object* v___x_4907_; uint8_t v___x_4908_; 
v_val_4906_ = lean_ctor_get(v_val_4904_, 1);
v___x_4907_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0));
v___x_4908_ = lean_string_dec_eq(v_val_4906_, v___x_4907_);
if (v___x_4908_ == 0)
{
lean_object* v___x_4909_; 
v___x_4909_ = lean_box(0);
return v___x_4909_;
}
else
{
lean_object* v___x_4910_; 
v___x_4910_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2));
return v___x_4910_;
}
}
else
{
lean_object* v___x_4911_; 
v___x_4911_ = lean_box(0);
return v___x_4911_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object* v_val_4937_){
_start:
{
lean_object* v_res_4938_; 
v_res_4938_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_val_4937_);
lean_dec(v_val_4937_);
return v_res_4938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object* v_nameStx_4939_, lean_object* v_v_4940_, lean_object* v_c_4941_){
_start:
{
lean_object* v_toParserModuleContext_4942_; lean_object* v_toInputContext_4943_; lean_object* v_toCacheableParserContext_4944_; lean_object* v_tokens_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4982_; 
v_toParserModuleContext_4942_ = lean_ctor_get(v_c_4941_, 1);
v_toInputContext_4943_ = lean_ctor_get(v_c_4941_, 0);
v_toCacheableParserContext_4944_ = lean_ctor_get(v_c_4941_, 2);
v_tokens_4945_ = lean_ctor_get(v_c_4941_, 3);
v_isSharedCheck_4982_ = !lean_is_exclusive(v_c_4941_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4947_ = v_c_4941_;
v_isShared_4948_ = v_isSharedCheck_4982_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_tokens_4945_);
lean_inc(v_toCacheableParserContext_4944_);
lean_inc(v_toParserModuleContext_4942_);
lean_inc(v_toInputContext_4943_);
lean_dec(v_c_4941_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4982_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v_env_4949_; lean_object* v_options_4950_; lean_object* v_currNamespace_4951_; lean_object* v_openDecls_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4981_; 
v_env_4949_ = lean_ctor_get(v_toParserModuleContext_4942_, 0);
v_options_4950_ = lean_ctor_get(v_toParserModuleContext_4942_, 1);
v_currNamespace_4951_ = lean_ctor_get(v_toParserModuleContext_4942_, 2);
v_openDecls_4952_ = lean_ctor_get(v_toParserModuleContext_4942_, 3);
v_isSharedCheck_4981_ = !lean_is_exclusive(v_toParserModuleContext_4942_);
if (v_isSharedCheck_4981_ == 0)
{
v___x_4954_ = v_toParserModuleContext_4942_;
v_isShared_4955_ = v_isSharedCheck_4981_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_openDecls_4952_);
lean_inc(v_currNamespace_4951_);
lean_inc(v_options_4950_);
lean_inc(v_env_4949_);
lean_dec(v_toParserModuleContext_4942_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4981_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___y_4957_; lean_object* v_map_4964_; uint8_t v_hasTrace_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4980_; 
v_map_4964_ = lean_ctor_get(v_options_4950_, 0);
v_hasTrace_4965_ = lean_ctor_get_uint8(v_options_4950_, sizeof(void*)*1);
v_isSharedCheck_4980_ = !lean_is_exclusive(v_options_4950_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4967_ = v_options_4950_;
v_isShared_4968_ = v_isSharedCheck_4980_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_map_4964_);
lean_dec(v_options_4950_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4980_;
goto v_resetjp_4966_;
}
v___jp_4956_:
{
lean_object* v___x_4959_; 
if (v_isShared_4955_ == 0)
{
lean_ctor_set(v___x_4954_, 1, v___y_4957_);
v___x_4959_ = v___x_4954_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_env_4949_);
lean_ctor_set(v_reuseFailAlloc_4963_, 1, v___y_4957_);
lean_ctor_set(v_reuseFailAlloc_4963_, 2, v_currNamespace_4951_);
lean_ctor_set(v_reuseFailAlloc_4963_, 3, v_openDecls_4952_);
v___x_4959_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
lean_object* v___x_4961_; 
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 1, v___x_4959_);
v___x_4961_ = v___x_4947_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_toInputContext_4943_);
lean_ctor_set(v_reuseFailAlloc_4962_, 1, v___x_4959_);
lean_ctor_set(v_reuseFailAlloc_4962_, 2, v_toCacheableParserContext_4944_);
lean_ctor_set(v_reuseFailAlloc_4962_, 3, v_tokens_4945_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
v_resetjp_4966_:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4969_ = l_Lean_Syntax_getId(v_nameStx_4939_);
v___x_4970_ = l_Lean_Name_eraseMacroScopes(v___x_4969_);
lean_dec(v___x_4969_);
lean_inc(v___x_4970_);
v___x_4971_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_4970_, v_v_4940_, v_map_4964_);
if (v_hasTrace_4965_ == 0)
{
lean_object* v___x_4972_; uint8_t v___x_4973_; lean_object* v___x_4975_; 
v___x_4972_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_4973_ = l_Lean_Name_isPrefixOf(v___x_4972_, v___x_4970_);
lean_dec(v___x_4970_);
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 0, v___x_4971_);
v___x_4975_ = v___x_4967_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v___x_4971_);
v___x_4975_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
lean_ctor_set_uint8(v___x_4975_, sizeof(void*)*1, v___x_4973_);
v___y_4957_ = v___x_4975_;
goto v___jp_4956_;
}
}
else
{
lean_object* v___x_4978_; 
lean_dec(v___x_4970_);
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 0, v___x_4971_);
v___x_4978_ = v___x_4967_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v___x_4971_);
lean_ctor_set_uint8(v_reuseFailAlloc_4979_, sizeof(void*)*1, v_hasTrace_4965_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
v___y_4957_ = v___x_4978_;
goto v___jp_4956_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object* v_nameStx_4983_, lean_object* v_v_4984_, lean_object* v_c_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(v_nameStx_4983_, v_v_4984_, v_c_4985_);
lean_dec(v_nameStx_4983_);
return v_res_4986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object* v_nameStx_4987_, lean_object* v_valStx_4988_, lean_object* v_p_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_){
_start:
{
lean_object* v___x_4992_; 
v___x_4992_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_valStx_4988_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_object* v___x_4993_; 
lean_dec(v_nameStx_4987_);
v___x_4993_ = lean_apply_2(v_p_4989_, v_a_4990_, v_a_4991_);
return v___x_4993_;
}
else
{
lean_object* v_val_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
v_val_4994_ = lean_ctor_get(v___x_4992_, 0);
lean_inc(v_val_4994_);
lean_dec_ref_known(v___x_4992_, 1);
v___x_4995_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed), 3, 2);
lean_closure_set(v___x_4995_, 0, v_nameStx_4987_);
lean_closure_set(v___x_4995_, 1, v_val_4994_);
v___x_4996_ = l_Lean_Parser_adaptUncacheableContextFn(v___x_4995_, v_p_4989_, v_a_4990_, v_a_4991_);
return v___x_4996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object* v_nameStx_4997_, lean_object* v_valStx_4998_, lean_object* v_p_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v_nameStx_4997_, v_valStx_4998_, v_p_4999_, v_a_5000_, v_a_5001_);
lean_dec(v_valStx_4998_);
return v_res_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object* v_p_5009_, lean_object* v_c_5010_, lean_object* v_s_5011_){
_start:
{
lean_object* v_stxStack_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; uint8_t v___x_5015_; 
v_stxStack_5012_ = lean_ctor_get(v_s_5011_, 0);
v___x_5013_ = lean_unsigned_to_nat(0u);
v___x_5014_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5012_);
v___x_5015_ = lean_nat_dec_lt(v___x_5013_, v___x_5014_);
lean_dec(v___x_5014_);
if (v___x_5015_ == 0)
{
lean_object* v___x_5016_; 
v___x_5016_ = lean_apply_2(v_p_5009_, v_c_5010_, v_s_5011_);
return v___x_5016_;
}
else
{
lean_object* v_stx_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; uint8_t v___x_5020_; 
v_stx_5017_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5012_);
lean_inc(v_stx_5017_);
v___x_5018_ = l_Lean_Syntax_getKind(v_stx_5017_);
v___x_5019_ = ((lean_object*)(l_Lean_Parser_withSetOptionFn___closed__1));
v___x_5020_ = lean_name_eq(v___x_5018_, v___x_5019_);
lean_dec(v___x_5018_);
if (v___x_5020_ == 0)
{
lean_object* v___x_5021_; 
lean_dec(v_stx_5017_);
v___x_5021_ = lean_apply_2(v_p_5009_, v_c_5010_, v_s_5011_);
return v___x_5021_;
}
else
{
lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5022_ = lean_unsigned_to_nat(1u);
v___x_5023_ = l_Lean_Syntax_getArg(v_stx_5017_, v___x_5022_);
v___x_5024_ = lean_unsigned_to_nat(3u);
v___x_5025_ = l_Lean_Syntax_getArg(v_stx_5017_, v___x_5024_);
lean_dec(v_stx_5017_);
v___x_5026_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5023_, v___x_5025_, v_p_5009_, v_c_5010_, v_s_5011_);
lean_dec(v___x_5025_);
return v___x_5026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object* v_p_5027_){
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
v___x_5033_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionFn), 3, 1);
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
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object* v_p_5038_, lean_object* v_c_5039_, lean_object* v_s_5040_){
_start:
{
lean_object* v_stxStack_5041_; lean_object* v_sz_5042_; lean_object* v___x_5043_; uint8_t v___x_5044_; 
v_stxStack_5041_ = lean_ctor_get(v_s_5040_, 0);
v_sz_5042_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5041_);
v___x_5043_ = lean_unsigned_to_nat(3u);
v___x_5044_ = lean_nat_dec_le(v___x_5043_, v_sz_5042_);
if (v___x_5044_ == 0)
{
lean_object* v___x_5045_; 
lean_dec(v_sz_5042_);
v___x_5045_ = lean_apply_2(v_p_5038_, v_c_5039_, v_s_5040_);
return v___x_5045_;
}
else
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5046_ = lean_nat_sub(v_sz_5042_, v___x_5043_);
lean_dec(v_sz_5042_);
v___x_5047_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5041_, v___x_5046_);
lean_dec(v___x_5046_);
v___x_5048_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5041_);
v___x_5049_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5047_, v___x_5048_, v_p_5038_, v_c_5039_, v_s_5040_);
lean_dec(v___x_5048_);
return v___x_5049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object* v_p_5050_){
_start:
{
lean_object* v_info_5051_; lean_object* v_fn_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5060_; 
v_info_5051_ = lean_ctor_get(v_p_5050_, 0);
v_fn_5052_ = lean_ctor_get(v_p_5050_, 1);
v_isSharedCheck_5060_ = !lean_is_exclusive(v_p_5050_);
if (v_isSharedCheck_5060_ == 0)
{
v___x_5054_ = v_p_5050_;
v_isShared_5055_ = v_isSharedCheck_5060_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_fn_5052_);
lean_inc(v_info_5051_);
lean_dec(v_p_5050_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5060_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5056_; lean_object* v___x_5058_; 
v___x_5056_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionValueFn), 3, 1);
lean_closure_set(v___x_5056_, 0, v_fn_5052_);
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 1, v___x_5056_);
v___x_5058_ = v___x_5054_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_info_5051_);
lean_ctor_set(v_reuseFailAlloc_5059_, 1, v___x_5056_);
v___x_5058_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
return v___x_5058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object* v___x_5061_){
_start:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = lean_st_ref_get(v___x_5061_);
v___x_5064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5063_);
return v___x_5064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v___x_5065_, lean_object* v___y_5066_){
_start:
{
lean_object* v_res_5067_; 
v_res_5067_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_5065_);
lean_dec(v___x_5065_);
return v_res_5067_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5068_; lean_object* v___f_5069_; 
v___x_5068_ = l_Lean_Parser_parserAliasesRef;
v___f_5069_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5069_, 0, v___x_5068_);
return v___f_5069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___f_5071_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_);
v___x_5072_ = lean_box(0);
v___x_5073_ = lean_box(2);
v___x_5074_ = l_Lean_registerEnvExtension___redArg(v___f_5071_, v___x_5072_, v___x_5073_);
return v___x_5074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v_a_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx(lean_object* v_x_5077_){
_start:
{
switch(lean_obj_tag(v_x_5077_))
{
case 0:
{
lean_object* v___x_5078_; 
v___x_5078_ = lean_unsigned_to_nat(0u);
return v___x_5078_;
}
case 1:
{
lean_object* v___x_5079_; 
v___x_5079_ = lean_unsigned_to_nat(1u);
return v___x_5079_;
}
default: 
{
lean_object* v___x_5080_; 
v___x_5080_ = lean_unsigned_to_nat(2u);
return v___x_5080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___boxed(lean_object* v_x_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l_Lean_Parser_ParserResolution_ctorIdx(v_x_5081_);
lean_dec_ref(v_x_5081_);
return v_res_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object* v_t_5083_, lean_object* v_k_5084_){
_start:
{
switch(lean_obj_tag(v_t_5083_))
{
case 0:
{
lean_object* v_cat_5085_; lean_object* v___x_5086_; 
v_cat_5085_ = lean_ctor_get(v_t_5083_, 0);
lean_inc(v_cat_5085_);
lean_dec_ref_known(v_t_5083_, 1);
v___x_5086_ = lean_apply_1(v_k_5084_, v_cat_5085_);
return v___x_5086_;
}
case 1:
{
lean_object* v_decl_5087_; uint8_t v_isDescr_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; 
v_decl_5087_ = lean_ctor_get(v_t_5083_, 0);
lean_inc(v_decl_5087_);
v_isDescr_5088_ = lean_ctor_get_uint8(v_t_5083_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5083_, 1);
v___x_5089_ = lean_box(v_isDescr_5088_);
v___x_5090_ = lean_apply_2(v_k_5084_, v_decl_5087_, v___x_5089_);
return v___x_5090_;
}
default: 
{
lean_object* v_p_5091_; lean_object* v___x_5092_; 
v_p_5091_ = lean_ctor_get(v_t_5083_, 0);
lean_inc_ref(v_p_5091_);
lean_dec_ref_known(v_t_5083_, 1);
v___x_5092_ = lean_apply_1(v_k_5084_, v_p_5091_);
return v___x_5092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object* v_motive_5093_, lean_object* v_ctorIdx_5094_, lean_object* v_t_5095_, lean_object* v_h_5096_, lean_object* v_k_5097_){
_start:
{
lean_object* v___x_5098_; 
v___x_5098_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5095_, v_k_5097_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object* v_motive_5099_, lean_object* v_ctorIdx_5100_, lean_object* v_t_5101_, lean_object* v_h_5102_, lean_object* v_k_5103_){
_start:
{
lean_object* v_res_5104_; 
v_res_5104_ = l_Lean_Parser_ParserResolution_ctorElim(v_motive_5099_, v_ctorIdx_5100_, v_t_5101_, v_h_5102_, v_k_5103_);
lean_dec(v_ctorIdx_5100_);
return v_res_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object* v_t_5105_, lean_object* v_category_5106_){
_start:
{
lean_object* v___x_5107_; 
v___x_5107_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5105_, v_category_5106_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object* v_motive_5108_, lean_object* v_t_5109_, lean_object* v_h_5110_, lean_object* v_category_5111_){
_start:
{
lean_object* v___x_5112_; 
v___x_5112_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5109_, v_category_5111_);
return v___x_5112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object* v_t_5113_, lean_object* v_parser_5114_){
_start:
{
lean_object* v___x_5115_; 
v___x_5115_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5113_, v_parser_5114_);
return v___x_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object* v_motive_5116_, lean_object* v_t_5117_, lean_object* v_h_5118_, lean_object* v_parser_5119_){
_start:
{
lean_object* v___x_5120_; 
v___x_5120_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5117_, v_parser_5119_);
return v___x_5120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object* v_t_5121_, lean_object* v_alias_5122_){
_start:
{
lean_object* v___x_5123_; 
v___x_5123_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5121_, v_alias_5122_);
return v___x_5123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object* v_motive_5124_, lean_object* v_t_5125_, lean_object* v_h_5126_, lean_object* v_alias_5127_){
_start:
{
lean_object* v___x_5128_; 
v___x_5128_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5125_, v_alias_5127_);
return v___x_5128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object* v_env_5132_, lean_object* v_name_5133_){
_start:
{
uint8_t v___x_5134_; lean_object* v___x_5135_; 
v___x_5134_ = 0;
v___x_5135_ = l_Lean_Environment_find_x3f(v_env_5132_, v_name_5133_, v___x_5134_);
if (lean_obj_tag(v___x_5135_) == 0)
{
lean_object* v___x_5136_; 
v___x_5136_ = lean_box(0);
return v___x_5136_;
}
else
{
lean_object* v_val_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5184_; 
v_val_5137_ = lean_ctor_get(v___x_5135_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5135_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5139_ = v___x_5135_;
v_isShared_5140_ = v_isSharedCheck_5184_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_val_5137_);
lean_dec(v___x_5135_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5184_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5141_; 
v___x_5141_ = l_Lean_ConstantInfo_type(v_val_5137_);
lean_dec(v_val_5137_);
if (lean_obj_tag(v___x_5141_) == 4)
{
lean_object* v_declName_5142_; 
v_declName_5142_ = lean_ctor_get(v___x_5141_, 0);
lean_inc(v_declName_5142_);
lean_dec_ref_known(v___x_5141_, 2);
if (lean_obj_tag(v_declName_5142_) == 1)
{
lean_object* v_pre_5143_; 
v_pre_5143_ = lean_ctor_get(v_declName_5142_, 0);
lean_inc(v_pre_5143_);
if (lean_obj_tag(v_pre_5143_) == 1)
{
lean_object* v_pre_5144_; 
v_pre_5144_ = lean_ctor_get(v_pre_5143_, 0);
switch(lean_obj_tag(v_pre_5144_))
{
case 1:
{
lean_object* v_pre_5145_; 
lean_inc_ref(v_pre_5144_);
lean_del_object(v___x_5139_);
v_pre_5145_ = lean_ctor_get(v_pre_5144_, 0);
if (lean_obj_tag(v_pre_5145_) == 0)
{
lean_object* v_str_5146_; lean_object* v_str_5147_; lean_object* v_str_5148_; lean_object* v___x_5149_; uint8_t v___x_5150_; 
v_str_5146_ = lean_ctor_get(v_declName_5142_, 1);
lean_inc_ref(v_str_5146_);
lean_dec_ref_known(v_declName_5142_, 2);
v_str_5147_ = lean_ctor_get(v_pre_5143_, 1);
lean_inc_ref(v_str_5147_);
lean_dec_ref_known(v_pre_5143_, 2);
v_str_5148_ = lean_ctor_get(v_pre_5144_, 1);
lean_inc_ref(v_str_5148_);
lean_dec_ref_known(v_pre_5144_, 2);
v___x_5149_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5150_ = lean_string_dec_eq(v_str_5148_, v___x_5149_);
lean_dec_ref(v_str_5148_);
if (v___x_5150_ == 0)
{
lean_object* v___x_5151_; 
lean_dec_ref(v_str_5147_);
lean_dec_ref(v_str_5146_);
v___x_5151_ = lean_box(0);
return v___x_5151_;
}
else
{
lean_object* v___x_5152_; uint8_t v___x_5153_; 
v___x_5152_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_5153_ = lean_string_dec_eq(v_str_5147_, v___x_5152_);
lean_dec_ref(v_str_5147_);
if (v___x_5153_ == 0)
{
lean_object* v___x_5154_; 
lean_dec_ref(v_str_5146_);
v___x_5154_ = lean_box(0);
return v___x_5154_;
}
else
{
uint8_t v___x_5155_; 
v___x_5155_ = lean_string_dec_eq(v_str_5146_, v___x_5152_);
if (v___x_5155_ == 0)
{
lean_object* v___x_5156_; uint8_t v___x_5157_; 
v___x_5156_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_5157_ = lean_string_dec_eq(v_str_5146_, v___x_5156_);
lean_dec_ref(v_str_5146_);
if (v___x_5157_ == 0)
{
lean_object* v___x_5158_; 
v___x_5158_ = lean_box(0);
return v___x_5158_;
}
else
{
lean_object* v___x_5159_; 
v___x_5159_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5159_;
}
}
else
{
lean_object* v___x_5160_; 
lean_dec_ref(v_str_5146_);
v___x_5160_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5160_;
}
}
}
}
else
{
lean_object* v___x_5161_; 
lean_dec_ref_known(v_pre_5144_, 2);
lean_dec_ref_known(v_pre_5143_, 2);
lean_dec_ref_known(v_declName_5142_, 2);
v___x_5161_ = lean_box(0);
return v___x_5161_;
}
}
case 0:
{
lean_object* v_str_5162_; lean_object* v_str_5163_; lean_object* v___x_5164_; uint8_t v___x_5165_; 
v_str_5162_ = lean_ctor_get(v_declName_5142_, 1);
lean_inc_ref(v_str_5162_);
lean_dec_ref_known(v_declName_5142_, 2);
v_str_5163_ = lean_ctor_get(v_pre_5143_, 1);
lean_inc_ref(v_str_5163_);
lean_dec_ref_known(v_pre_5143_, 2);
v___x_5164_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5165_ = lean_string_dec_eq(v_str_5163_, v___x_5164_);
lean_dec_ref(v_str_5163_);
if (v___x_5165_ == 0)
{
lean_object* v___x_5166_; 
lean_dec_ref(v_str_5162_);
lean_del_object(v___x_5139_);
v___x_5166_ = lean_box(0);
return v___x_5166_;
}
else
{
lean_object* v___x_5167_; uint8_t v___x_5168_; 
v___x_5167_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_5168_ = lean_string_dec_eq(v_str_5162_, v___x_5167_);
if (v___x_5168_ == 0)
{
lean_object* v___x_5169_; uint8_t v___x_5170_; 
v___x_5169_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_5170_ = lean_string_dec_eq(v_str_5162_, v___x_5169_);
lean_dec_ref(v_str_5162_);
if (v___x_5170_ == 0)
{
lean_object* v___x_5171_; 
lean_del_object(v___x_5139_);
v___x_5171_ = lean_box(0);
return v___x_5171_;
}
else
{
lean_object* v___x_5172_; lean_object* v___x_5174_; 
v___x_5172_ = lean_box(v___x_5165_);
if (v_isShared_5140_ == 0)
{
lean_ctor_set(v___x_5139_, 0, v___x_5172_);
v___x_5174_ = v___x_5139_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v___x_5172_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
else
{
lean_object* v___x_5176_; lean_object* v___x_5178_; 
lean_dec_ref(v_str_5162_);
v___x_5176_ = lean_box(v___x_5165_);
if (v_isShared_5140_ == 0)
{
lean_ctor_set(v___x_5139_, 0, v___x_5176_);
v___x_5178_ = v___x_5139_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v___x_5176_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
default: 
{
lean_object* v___x_5180_; 
lean_dec_ref_known(v_pre_5143_, 2);
lean_dec_ref_known(v_declName_5142_, 2);
lean_del_object(v___x_5139_);
v___x_5180_ = lean_box(0);
return v___x_5180_;
}
}
}
else
{
lean_object* v___x_5181_; 
lean_dec(v_pre_5143_);
lean_dec_ref_known(v_declName_5142_, 2);
lean_del_object(v___x_5139_);
v___x_5181_ = lean_box(0);
return v___x_5181_;
}
}
else
{
lean_object* v___x_5182_; 
lean_dec(v_declName_5142_);
lean_del_object(v___x_5139_);
v___x_5182_ = lean_box(0);
return v___x_5182_;
}
}
else
{
lean_object* v___x_5183_; 
lean_dec_ref(v___x_5141_);
lean_del_object(v___x_5139_);
v___x_5183_ = lean_box(0);
return v___x_5183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object* v_env_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_){
_start:
{
if (lean_obj_tag(v_a_5186_) == 0)
{
lean_object* v___x_5188_; 
lean_dec_ref(v_env_5185_);
v___x_5188_ = lean_array_to_list(v_a_5187_);
return v___x_5188_;
}
else
{
lean_object* v_head_5189_; lean_object* v_snd_5190_; 
v_head_5189_ = lean_ctor_get(v_a_5186_, 0);
v_snd_5190_ = lean_ctor_get(v_head_5189_, 1);
if (lean_obj_tag(v_snd_5190_) == 0)
{
lean_object* v_tail_5191_; lean_object* v_fst_5192_; lean_object* v___x_5193_; 
lean_inc(v_head_5189_);
v_tail_5191_ = lean_ctor_get(v_a_5186_, 1);
lean_inc(v_tail_5191_);
lean_dec_ref_known(v_a_5186_, 2);
v_fst_5192_ = lean_ctor_get(v_head_5189_, 0);
lean_inc_n(v_fst_5192_, 2);
lean_dec(v_head_5189_);
lean_inc_ref(v_env_5185_);
v___x_5193_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5185_, v_fst_5192_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_dec(v_fst_5192_);
v_a_5186_ = v_tail_5191_;
goto _start;
}
else
{
lean_object* v_val_5195_; lean_object* v___x_5196_; uint8_t v___x_5197_; lean_object* v___x_5198_; 
v_val_5195_ = lean_ctor_get(v___x_5193_, 0);
lean_inc(v_val_5195_);
lean_dec_ref_known(v___x_5193_, 1);
v___x_5196_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5196_, 0, v_fst_5192_);
v___x_5197_ = lean_unbox(v_val_5195_);
lean_dec(v_val_5195_);
lean_ctor_set_uint8(v___x_5196_, sizeof(void*)*1, v___x_5197_);
v___x_5198_ = lean_array_push(v_a_5187_, v___x_5196_);
v_a_5186_ = v_tail_5191_;
v_a_5187_ = v___x_5198_;
goto _start;
}
}
else
{
lean_object* v_tail_5200_; 
v_tail_5200_ = lean_ctor_get(v_a_5186_, 1);
lean_inc(v_tail_5200_);
lean_dec_ref_known(v_a_5186_, 2);
v_a_5186_ = v_tail_5200_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object* v_env_5205_, lean_object* v_as_x27_5206_, lean_object* v_b_5207_){
_start:
{
if (lean_obj_tag(v_as_x27_5206_) == 0)
{
lean_dec_ref(v_env_5205_);
lean_inc_ref(v_b_5207_);
return v_b_5207_;
}
else
{
lean_object* v_head_5208_; lean_object* v_tail_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; 
v_head_5208_ = lean_ctor_get(v_as_x27_5206_, 0);
v_tail_5209_ = lean_ctor_get(v_as_x27_5206_, 1);
v___x_5210_ = lean_box(0);
v___x_5211_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_5208_) == 1)
{
lean_object* v_fields_5212_; 
v_fields_5212_ = lean_ctor_get(v_head_5208_, 1);
if (lean_obj_tag(v_fields_5212_) == 0)
{
lean_object* v_n_5213_; lean_object* v___x_5214_; 
v_n_5213_ = lean_ctor_get(v_head_5208_, 0);
lean_inc(v_n_5213_);
lean_inc_ref(v_env_5205_);
v___x_5214_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5205_, v_n_5213_);
if (lean_obj_tag(v___x_5214_) == 1)
{
lean_object* v_val_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5227_; 
lean_dec_ref(v_env_5205_);
v_val_5215_ = lean_ctor_get(v___x_5214_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5214_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5217_ = v___x_5214_;
v_isShared_5218_ = v_isSharedCheck_5227_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_val_5215_);
lean_dec(v___x_5214_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5227_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v___x_5219_; uint8_t v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5224_; 
lean_inc(v_n_5213_);
v___x_5219_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5219_, 0, v_n_5213_);
v___x_5220_ = lean_unbox(v_val_5215_);
lean_dec(v_val_5215_);
lean_ctor_set_uint8(v___x_5219_, sizeof(void*)*1, v___x_5220_);
v___x_5221_ = lean_box(0);
v___x_5222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5219_);
lean_ctor_set(v___x_5222_, 1, v___x_5221_);
if (v_isShared_5218_ == 0)
{
lean_ctor_set(v___x_5217_, 0, v___x_5222_);
v___x_5224_ = v___x_5217_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5222_);
v___x_5224_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
lean_object* v___x_5225_; 
v___x_5225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5224_);
lean_ctor_set(v___x_5225_, 1, v___x_5210_);
return v___x_5225_;
}
}
}
else
{
lean_dec(v___x_5214_);
v_as_x27_5206_ = v_tail_5209_;
v_b_5207_ = v___x_5211_;
goto _start;
}
}
else
{
v_as_x27_5206_ = v_tail_5209_;
v_b_5207_ = v___x_5211_;
goto _start;
}
}
else
{
v_as_x27_5206_ = v_tail_5209_;
v_b_5207_ = v___x_5211_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object* v_env_5231_, lean_object* v_as_x27_5232_, lean_object* v_b_5233_){
_start:
{
lean_object* v_res_5234_; 
v_res_5234_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5231_, v_as_x27_5232_, v_b_5233_);
lean_dec_ref(v_b_5233_);
lean_dec(v_as_x27_5232_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object* v_env_5237_, lean_object* v_opts_5238_, lean_object* v_currNamespace_5239_, lean_object* v_openDecls_5240_, lean_object* v_ident_5241_){
_start:
{
if (lean_obj_tag(v_ident_5241_) == 3)
{
lean_object* v_val_5242_; lean_object* v_preresolved_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v_fst_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5281_; 
v_val_5242_ = lean_ctor_get(v_ident_5241_, 2);
lean_inc(v_val_5242_);
v_preresolved_5243_ = lean_ctor_get(v_ident_5241_, 3);
lean_inc(v_preresolved_5243_);
lean_dec_ref_known(v_ident_5241_, 4);
v___x_5244_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
lean_inc_ref(v_env_5237_);
v___x_5245_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5237_, v_preresolved_5243_, v___x_5244_);
lean_dec(v_preresolved_5243_);
v_fst_5246_ = lean_ctor_get(v___x_5245_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5281_ == 0)
{
lean_object* v_unused_5282_; 
v_unused_5282_ = lean_ctor_get(v___x_5245_, 1);
lean_dec(v_unused_5282_);
v___x_5248_ = v___x_5245_;
v_isShared_5249_ = v_isSharedCheck_5281_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_fst_5246_);
lean_dec(v___x_5245_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5281_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
if (lean_obj_tag(v_fst_5246_) == 0)
{
lean_object* v___x_5250_; uint8_t v___x_5251_; 
v___x_5250_ = l_Lean_Name_eraseMacroScopes(v_val_5242_);
lean_inc_ref(v_env_5237_);
v___x_5251_ = l_Lean_Parser_isParserCategory(v_env_5237_, v___x_5250_);
if (v___x_5251_ == 0)
{
lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; uint8_t v___x_5255_; 
lean_inc_ref_n(v_env_5237_, 2);
v___x_5252_ = l_Lean_ResolveName_resolveGlobalName(v_env_5237_, v_opts_5238_, v_currNamespace_5239_, v_openDecls_5240_, v_val_5242_);
v___x_5253_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0));
v___x_5254_ = l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(v_env_5237_, v___x_5252_, v___x_5253_);
v___x_5255_ = l_List_isEmpty___redArg(v___x_5254_);
if (v___x_5255_ == 0)
{
lean_dec(v___x_5250_);
lean_del_object(v___x_5248_);
lean_dec_ref(v_env_5237_);
return v___x_5254_;
}
else
{
lean_object* v___x_5256_; lean_object* v_asyncMode_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; 
lean_dec(v___x_5254_);
v___x_5256_ = l_Lean_Parser_aliasExtension;
v_asyncMode_5257_ = lean_ctor_get(v___x_5256_, 2);
v___x_5258_ = lean_box(1);
v___x_5259_ = lean_box(0);
v___x_5260_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5258_, v___x_5256_, v_env_5237_, v_asyncMode_5257_, v___x_5259_);
v___x_5261_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5260_, v___x_5250_);
lean_dec(v___x_5250_);
lean_dec(v___x_5260_);
if (lean_obj_tag(v___x_5261_) == 1)
{
lean_object* v_val_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5273_; 
v_val_5262_ = lean_ctor_get(v___x_5261_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v___x_5261_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5264_ = v___x_5261_;
v_isShared_5265_ = v_isSharedCheck_5273_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_val_5262_);
lean_dec(v___x_5261_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5273_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5267_; 
if (v_isShared_5265_ == 0)
{
lean_ctor_set_tag(v___x_5264_, 2);
v___x_5267_ = v___x_5264_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_val_5262_);
v___x_5267_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
lean_object* v___x_5268_; lean_object* v___x_5270_; 
v___x_5268_ = lean_box(0);
if (v_isShared_5249_ == 0)
{
lean_ctor_set_tag(v___x_5248_, 1);
lean_ctor_set(v___x_5248_, 1, v___x_5268_);
lean_ctor_set(v___x_5248_, 0, v___x_5267_);
v___x_5270_ = v___x_5248_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v___x_5267_);
lean_ctor_set(v_reuseFailAlloc_5271_, 1, v___x_5268_);
v___x_5270_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
return v___x_5270_;
}
}
}
}
else
{
lean_object* v___x_5274_; 
lean_dec(v___x_5261_);
lean_del_object(v___x_5248_);
v___x_5274_ = lean_box(0);
return v___x_5274_;
}
}
}
else
{
lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5278_; 
lean_dec(v_val_5242_);
lean_dec(v_openDecls_5240_);
lean_dec(v_currNamespace_5239_);
lean_dec_ref(v_env_5237_);
v___x_5275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5250_);
v___x_5276_ = lean_box(0);
if (v_isShared_5249_ == 0)
{
lean_ctor_set_tag(v___x_5248_, 1);
lean_ctor_set(v___x_5248_, 1, v___x_5276_);
lean_ctor_set(v___x_5248_, 0, v___x_5275_);
v___x_5278_ = v___x_5248_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___x_5275_);
lean_ctor_set(v_reuseFailAlloc_5279_, 1, v___x_5276_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
return v___x_5278_;
}
}
}
else
{
lean_object* v_val_5280_; 
lean_del_object(v___x_5248_);
lean_dec(v_val_5242_);
lean_dec(v_openDecls_5240_);
lean_dec(v_currNamespace_5239_);
lean_dec_ref(v_env_5237_);
v_val_5280_ = lean_ctor_get(v_fst_5246_, 0);
lean_inc(v_val_5280_);
lean_dec_ref_known(v_fst_5246_, 1);
return v_val_5280_;
}
}
}
else
{
lean_object* v___x_5283_; 
lean_dec(v_ident_5241_);
lean_dec(v_openDecls_5240_);
lean_dec(v_currNamespace_5239_);
lean_dec_ref(v_env_5237_);
v___x_5283_ = lean_box(0);
return v___x_5283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object* v_env_5284_, lean_object* v_opts_5285_, lean_object* v_currNamespace_5286_, lean_object* v_openDecls_5287_, lean_object* v_ident_5288_){
_start:
{
lean_object* v_res_5289_; 
v_res_5289_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5284_, v_opts_5285_, v_currNamespace_5286_, v_openDecls_5287_, v_ident_5288_);
lean_dec_ref(v_opts_5285_);
return v_res_5289_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object* v_env_5290_, lean_object* v_as_5291_, lean_object* v_as_x27_5292_, lean_object* v_b_5293_, lean_object* v_a_5294_){
_start:
{
lean_object* v___x_5295_; 
v___x_5295_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5290_, v_as_x27_5292_, v_b_5293_);
return v___x_5295_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object* v_env_5296_, lean_object* v_as_5297_, lean_object* v_as_x27_5298_, lean_object* v_b_5299_, lean_object* v_a_5300_){
_start:
{
lean_object* v_res_5301_; 
v_res_5301_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(v_env_5296_, v_as_5297_, v_as_x27_5298_, v_b_5299_, v_a_5300_);
lean_dec_ref(v_b_5299_);
lean_dec(v_as_x27_5298_);
lean_dec(v_as_5297_);
return v_res_5301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object* v_ctx_5302_, lean_object* v_id_5303_, uint8_t v_unsetExporting_5304_){
_start:
{
lean_object* v___y_5306_; 
if (v_unsetExporting_5304_ == 0)
{
lean_object* v_toParserModuleContext_5312_; lean_object* v_env_5313_; 
v_toParserModuleContext_5312_ = lean_ctor_get(v_ctx_5302_, 1);
v_env_5313_ = lean_ctor_get(v_toParserModuleContext_5312_, 0);
lean_inc_ref(v_env_5313_);
v___y_5306_ = v_env_5313_;
goto v___jp_5305_;
}
else
{
lean_object* v_toParserModuleContext_5314_; lean_object* v_env_5315_; uint8_t v___x_5316_; lean_object* v___x_5317_; 
v_toParserModuleContext_5314_ = lean_ctor_get(v_ctx_5302_, 1);
v_env_5315_ = lean_ctor_get(v_toParserModuleContext_5314_, 0);
v___x_5316_ = 0;
lean_inc_ref(v_env_5315_);
v___x_5317_ = l_Lean_Environment_setExporting(v_env_5315_, v___x_5316_);
v___y_5306_ = v___x_5317_;
goto v___jp_5305_;
}
v___jp_5305_:
{
lean_object* v_toParserModuleContext_5307_; lean_object* v_options_5308_; lean_object* v_currNamespace_5309_; lean_object* v_openDecls_5310_; lean_object* v___x_5311_; 
v_toParserModuleContext_5307_ = lean_ctor_get(v_ctx_5302_, 1);
lean_inc_ref(v_toParserModuleContext_5307_);
lean_dec_ref(v_ctx_5302_);
v_options_5308_ = lean_ctor_get(v_toParserModuleContext_5307_, 1);
lean_inc_ref(v_options_5308_);
v_currNamespace_5309_ = lean_ctor_get(v_toParserModuleContext_5307_, 2);
lean_inc(v_currNamespace_5309_);
v_openDecls_5310_ = lean_ctor_get(v_toParserModuleContext_5307_, 3);
lean_inc(v_openDecls_5310_);
lean_dec_ref(v_toParserModuleContext_5307_);
v___x_5311_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v___y_5306_, v_options_5308_, v_currNamespace_5309_, v_openDecls_5310_, v_id_5303_);
lean_dec_ref(v_options_5308_);
return v___x_5311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object* v_ctx_5318_, lean_object* v_id_5319_, lean_object* v_unsetExporting_5320_){
_start:
{
uint8_t v_unsetExporting_boxed_5321_; lean_object* v_res_5322_; 
v_unsetExporting_boxed_5321_ = lean_unbox(v_unsetExporting_5320_);
v_res_5322_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5318_, v_id_5319_, v_unsetExporting_boxed_5321_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object* v_id_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_){
_start:
{
lean_object* v___x_5327_; lean_object* v_env_5328_; lean_object* v_options_5329_; lean_object* v_currNamespace_5330_; lean_object* v_openDecls_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; 
v___x_5327_ = lean_st_ref_get(v_a_5325_);
v_env_5328_ = lean_ctor_get(v___x_5327_, 0);
lean_inc_ref(v_env_5328_);
lean_dec(v___x_5327_);
v_options_5329_ = lean_ctor_get(v_a_5324_, 2);
v_currNamespace_5330_ = lean_ctor_get(v_a_5324_, 6);
v_openDecls_5331_ = lean_ctor_get(v_a_5324_, 7);
lean_inc(v_openDecls_5331_);
lean_inc(v_currNamespace_5330_);
v___x_5332_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5328_, v_options_5329_, v_currNamespace_5330_, v_openDecls_5331_, v_id_5323_);
v___x_5333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5333_, 0, v___x_5332_);
return v___x_5333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object* v_id_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_){
_start:
{
lean_object* v_res_5338_; 
v_res_5338_ = l_Lean_Parser_resolveParserName(v_id_5334_, v_a_5335_, v_a_5336_);
lean_dec(v_a_5336_);
lean_dec_ref(v_a_5335_);
return v_res_5338_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object* v_x_5339_, lean_object* v_x_5340_){
_start:
{
if (lean_obj_tag(v_x_5339_) == 0)
{
if (lean_obj_tag(v_x_5340_) == 0)
{
uint8_t v___x_5341_; 
v___x_5341_ = 1;
return v___x_5341_;
}
else
{
uint8_t v___x_5342_; 
lean_dec_ref_known(v_x_5340_, 1);
v___x_5342_ = 0;
return v___x_5342_;
}
}
else
{
if (lean_obj_tag(v_x_5340_) == 0)
{
uint8_t v___x_5343_; 
lean_dec_ref_known(v_x_5339_, 1);
v___x_5343_ = 0;
return v___x_5343_;
}
else
{
lean_object* v_val_5344_; lean_object* v_val_5345_; uint8_t v___x_5346_; 
v_val_5344_ = lean_ctor_get(v_x_5339_, 0);
lean_inc(v_val_5344_);
lean_dec_ref_known(v_x_5339_, 1);
v_val_5345_ = lean_ctor_get(v_x_5340_, 0);
lean_inc(v_val_5345_);
lean_dec_ref_known(v_x_5340_, 1);
v___x_5346_ = l_Lean_Parser_instBEqError_beq(v_val_5344_, v_val_5345_);
return v___x_5346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object* v_x_5347_, lean_object* v_x_5348_){
_start:
{
uint8_t v_res_5349_; lean_object* v_r_5350_; 
v_res_5349_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5347_, v_x_5348_);
v_r_5350_ = lean_box(v_res_5349_);
return v_r_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(lean_object* v_ctx_5351_){
_start:
{
lean_object* v_toParserModuleContext_5352_; lean_object* v_toInputContext_5353_; lean_object* v_toCacheableParserContext_5354_; lean_object* v_tokens_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5378_; 
v_toParserModuleContext_5352_ = lean_ctor_get(v_ctx_5351_, 1);
v_toInputContext_5353_ = lean_ctor_get(v_ctx_5351_, 0);
v_toCacheableParserContext_5354_ = lean_ctor_get(v_ctx_5351_, 2);
v_tokens_5355_ = lean_ctor_get(v_ctx_5351_, 3);
v_isSharedCheck_5378_ = !lean_is_exclusive(v_ctx_5351_);
if (v_isSharedCheck_5378_ == 0)
{
v___x_5357_ = v_ctx_5351_;
v_isShared_5358_ = v_isSharedCheck_5378_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_tokens_5355_);
lean_inc(v_toCacheableParserContext_5354_);
lean_inc(v_toParserModuleContext_5352_);
lean_inc(v_toInputContext_5353_);
lean_dec(v_ctx_5351_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5378_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v_env_5359_; lean_object* v_options_5360_; lean_object* v_currNamespace_5361_; lean_object* v_openDecls_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5377_; 
v_env_5359_ = lean_ctor_get(v_toParserModuleContext_5352_, 0);
v_options_5360_ = lean_ctor_get(v_toParserModuleContext_5352_, 1);
v_currNamespace_5361_ = lean_ctor_get(v_toParserModuleContext_5352_, 2);
v_openDecls_5362_ = lean_ctor_get(v_toParserModuleContext_5352_, 3);
v_isSharedCheck_5377_ = !lean_is_exclusive(v_toParserModuleContext_5352_);
if (v_isSharedCheck_5377_ == 0)
{
v___x_5364_ = v_toParserModuleContext_5352_;
v_isShared_5365_ = v_isSharedCheck_5377_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_openDecls_5362_);
lean_inc(v_currNamespace_5361_);
lean_inc(v_options_5360_);
lean_inc(v_env_5359_);
lean_dec(v_toParserModuleContext_5352_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5377_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5366_; lean_object* v___x_5367_; uint8_t v___x_5368_; uint8_t v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5372_; 
v___x_5366_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_5367_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_5368_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_5360_, v___x_5367_);
v___x_5369_ = lean_bool_not(v___x_5368_);
v___x_5370_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_5360_, v___x_5366_, v___x_5369_);
if (v_isShared_5365_ == 0)
{
lean_ctor_set(v___x_5364_, 1, v___x_5370_);
v___x_5372_ = v___x_5364_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v_env_5359_);
lean_ctor_set(v_reuseFailAlloc_5376_, 1, v___x_5370_);
lean_ctor_set(v_reuseFailAlloc_5376_, 2, v_currNamespace_5361_);
lean_ctor_set(v_reuseFailAlloc_5376_, 3, v_openDecls_5362_);
v___x_5372_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
lean_object* v___x_5374_; 
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 1, v___x_5372_);
v___x_5374_ = v___x_5357_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_toInputContext_5353_);
lean_ctor_set(v_reuseFailAlloc_5375_, 1, v___x_5372_);
lean_ctor_set(v_reuseFailAlloc_5375_, 2, v_toCacheableParserContext_5354_);
lean_ctor_set(v_reuseFailAlloc_5375_, 3, v_tokens_5355_);
v___x_5374_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
return v___x_5374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* v_offset_5387_, lean_object* v_ctx_5388_, lean_object* v_s_5389_){
_start:
{
lean_object* v___y_5391_; uint8_t v___y_5392_; lean_object* v_stxStack_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; uint8_t v___x_5400_; 
v_stxStack_5396_ = lean_ctor_get(v_s_5389_, 0);
v___x_5397_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5396_);
v___x_5398_ = lean_unsigned_to_nat(1u);
v___x_5399_ = lean_nat_add(v_offset_5387_, v___x_5398_);
v___x_5400_ = lean_nat_dec_lt(v___x_5397_, v___x_5399_);
lean_dec(v___x_5399_);
if (v___x_5400_ == 0)
{
lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; 
v___x_5401_ = lean_nat_sub(v___x_5397_, v_offset_5387_);
lean_dec(v___x_5397_);
v___x_5402_ = lean_nat_sub(v___x_5401_, v___x_5398_);
lean_dec(v___x_5401_);
v___x_5403_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5396_, v___x_5402_);
lean_dec(v___x_5402_);
if (lean_obj_tag(v___x_5403_) == 3)
{
uint8_t v___x_5415_; lean_object* v___x_5416_; 
v___x_5415_ = 1;
lean_inc_ref(v___x_5403_);
lean_inc_ref(v_ctx_5388_);
v___x_5416_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5388_, v___x_5403_, v___x_5415_);
if (lean_obj_tag(v___x_5416_) == 0)
{
lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; 
lean_dec_ref(v_ctx_5388_);
v___x_5417_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__2));
v___x_5418_ = lean_box(0);
v___x_5419_ = l_Lean_Syntax_formatStx(v___x_5403_, v___x_5418_, v___x_5400_);
v___x_5420_ = l_Std_Format_defWidth;
v___x_5421_ = lean_unsigned_to_nat(0u);
v___x_5422_ = l_Std_Format_pretty(v___x_5419_, v___x_5420_, v___x_5421_, v___x_5421_);
v___x_5423_ = lean_string_append(v___x_5417_, v___x_5422_);
lean_dec_ref(v___x_5422_);
v___x_5424_ = lean_box(0);
v___x_5425_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5389_, v___x_5423_, v___x_5424_, v___x_5415_);
return v___x_5425_;
}
else
{
lean_object* v_head_5426_; lean_object* v_tail_5427_; lean_object* v_iniSz_5428_; lean_object* v_s_5430_; 
v_head_5426_ = lean_ctor_get(v___x_5416_, 0);
lean_inc(v_head_5426_);
v_tail_5427_ = lean_ctor_get(v___x_5416_, 1);
lean_inc(v_tail_5427_);
lean_dec_ref_known(v___x_5416_, 2);
v_iniSz_5428_ = l_Lean_Parser_ParserState_stackSize(v_s_5389_);
switch(lean_obj_tag(v_head_5426_))
{
case 0:
{
if (lean_obj_tag(v_tail_5427_) == 0)
{
lean_object* v_cat_5440_; lean_object* v___x_5441_; 
lean_dec_ref_known(v___x_5403_, 4);
v_cat_5440_ = lean_ctor_get(v_head_5426_, 0);
lean_inc(v_cat_5440_);
lean_dec_ref_known(v_head_5426_, 1);
v___x_5441_ = l_Lean_Parser_categoryParserFn(v_cat_5440_, v_ctx_5388_, v_s_5389_);
v_s_5430_ = v___x_5441_;
goto v___jp_5429_;
}
else
{
lean_dec_ref_known(v_tail_5427_, 2);
lean_dec_ref_known(v_head_5426_, 1);
lean_dec(v_iniSz_5428_);
lean_dec_ref(v_ctx_5388_);
goto v___jp_5404_;
}
}
case 1:
{
if (lean_obj_tag(v_tail_5427_) == 0)
{
lean_object* v_decl_5442_; lean_object* v___f_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
lean_dec_ref_known(v___x_5403_, 4);
v_decl_5442_ = lean_ctor_get(v_head_5426_, 0);
lean_inc(v_decl_5442_);
lean_dec_ref_known(v_head_5426_, 1);
v___f_5443_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__3));
v___x_5444_ = lean_box(0);
v___x_5445_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_5445_, 0, v_decl_5442_);
lean_closure_set(v___x_5445_, 1, v___x_5444_);
v___x_5446_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5443_, v___x_5445_, v_ctx_5388_, v_s_5389_);
v_s_5430_ = v___x_5446_;
goto v___jp_5429_;
}
else
{
lean_dec_ref_known(v_tail_5427_, 2);
lean_dec_ref_known(v_head_5426_, 1);
lean_dec(v_iniSz_5428_);
lean_dec_ref(v_ctx_5388_);
goto v___jp_5404_;
}
}
default: 
{
if (lean_obj_tag(v_tail_5427_) == 0)
{
lean_object* v_p_5447_; 
v_p_5447_ = lean_ctor_get(v_head_5426_, 0);
lean_inc_ref(v_p_5447_);
lean_dec_ref_known(v_head_5426_, 1);
if (lean_obj_tag(v_p_5447_) == 0)
{
lean_object* v_p_5448_; lean_object* v_fn_5449_; lean_object* v___x_5450_; 
lean_dec_ref_known(v___x_5403_, 4);
v_p_5448_ = lean_ctor_get(v_p_5447_, 0);
lean_inc(v_p_5448_);
lean_dec_ref_known(v_p_5447_, 1);
v_fn_5449_ = lean_ctor_get(v_p_5448_, 1);
lean_inc_ref(v_fn_5449_);
lean_dec(v_p_5448_);
v___x_5450_ = lean_apply_2(v_fn_5449_, v_ctx_5388_, v_s_5389_);
v_s_5430_ = v___x_5450_;
goto v___jp_5429_;
}
else
{
lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; 
lean_dec_ref(v_p_5447_);
lean_dec(v_iniSz_5428_);
lean_dec_ref(v_ctx_5388_);
v___x_5451_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__4));
v___x_5452_ = lean_box(0);
v___x_5453_ = l_Lean_Syntax_formatStx(v___x_5403_, v___x_5452_, v___x_5400_);
v___x_5454_ = l_Std_Format_defWidth;
v___x_5455_ = lean_unsigned_to_nat(0u);
v___x_5456_ = l_Std_Format_pretty(v___x_5453_, v___x_5454_, v___x_5455_, v___x_5455_);
v___x_5457_ = lean_string_append(v___x_5451_, v___x_5456_);
lean_dec_ref(v___x_5456_);
v___x_5458_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__5));
v___x_5459_ = lean_string_append(v___x_5457_, v___x_5458_);
v___x_5460_ = lean_box(0);
v___x_5461_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5389_, v___x_5459_, v___x_5460_, v___x_5415_);
return v___x_5461_;
}
}
else
{
lean_dec_ref_known(v_tail_5427_, 2);
lean_dec_ref_known(v_head_5426_, 1);
lean_dec(v_iniSz_5428_);
lean_dec_ref(v_ctx_5388_);
goto v___jp_5404_;
}
}
}
v___jp_5429_:
{
lean_object* v_errorMsg_5431_; lean_object* v___x_5432_; uint8_t v___x_5433_; uint8_t v___x_5434_; uint8_t v___x_5435_; 
v_errorMsg_5431_ = lean_ctor_get(v_s_5430_, 4);
v___x_5432_ = lean_box(0);
lean_inc(v_errorMsg_5431_);
v___x_5433_ = l_Option_instBEq_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_errorMsg_5431_, v___x_5432_);
v___x_5434_ = lean_bool_not(v___x_5433_);
v___x_5435_ = lean_bool_not(v___x_5434_);
if (v___x_5435_ == 0)
{
lean_dec(v_iniSz_5428_);
v___y_5391_ = v_s_5430_;
v___y_5392_ = v___x_5435_;
goto v___jp_5390_;
}
else
{
lean_object* v___x_5436_; lean_object* v___x_5437_; uint8_t v___x_5438_; uint8_t v___x_5439_; 
v___x_5436_ = l_Lean_Parser_ParserState_stackSize(v_s_5430_);
v___x_5437_ = lean_nat_add(v_iniSz_5428_, v___x_5398_);
lean_dec(v_iniSz_5428_);
v___x_5438_ = lean_nat_dec_eq(v___x_5436_, v___x_5437_);
lean_dec(v___x_5437_);
lean_dec(v___x_5436_);
v___x_5439_ = lean_bool_not(v___x_5438_);
v___y_5391_ = v_s_5430_;
v___y_5392_ = v___x_5439_;
goto v___jp_5390_;
}
}
}
}
else
{
lean_object* v___x_5462_; lean_object* v___x_5463_; uint8_t v___x_5464_; lean_object* v___x_5465_; 
lean_dec(v___x_5403_);
lean_dec_ref(v_ctx_5388_);
v___x_5462_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__6));
v___x_5463_ = lean_box(0);
v___x_5464_ = 1;
v___x_5465_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5389_, v___x_5462_, v___x_5463_, v___x_5464_);
return v___x_5465_;
}
v___jp_5404_:
{
lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; uint8_t v___x_5413_; lean_object* v___x_5414_; 
v___x_5405_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__1));
v___x_5406_ = lean_box(0);
v___x_5407_ = l_Lean_Syntax_formatStx(v___x_5403_, v___x_5406_, v___x_5400_);
v___x_5408_ = l_Std_Format_defWidth;
v___x_5409_ = lean_unsigned_to_nat(0u);
v___x_5410_ = l_Std_Format_pretty(v___x_5407_, v___x_5408_, v___x_5409_, v___x_5409_);
v___x_5411_ = lean_string_append(v___x_5405_, v___x_5410_);
lean_dec_ref(v___x_5410_);
v___x_5412_ = lean_box(0);
v___x_5413_ = 1;
v___x_5414_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5389_, v___x_5411_, v___x_5412_, v___x_5413_);
return v___x_5414_;
}
}
else
{
lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; 
lean_dec(v___x_5397_);
lean_dec_ref(v_ctx_5388_);
v___x_5466_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__7));
v___x_5467_ = lean_box(0);
v___x_5468_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5389_, v___x_5466_, v___x_5467_, v___x_5400_);
return v___x_5468_;
}
v___jp_5390_:
{
if (v___y_5392_ == 0)
{
return v___y_5391_;
}
else
{
lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; 
v___x_5393_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__0));
v___x_5394_ = lean_box(0);
v___x_5395_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___y_5391_, v___x_5393_, v___x_5394_, v___y_5392_);
return v___x_5395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* v_offset_5469_, lean_object* v_ctx_5470_, lean_object* v_s_5471_){
_start:
{
lean_object* v_res_5472_; 
v_res_5472_ = l_Lean_Parser_parserOfStackFn(v_offset_5469_, v_ctx_5470_, v_s_5471_);
lean_dec(v_offset_5469_);
return v_res_5472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object* v_prec_5473_, lean_object* v_x_5474_){
_start:
{
lean_object* v_quotDepth_5475_; uint8_t v_suppressInsideQuot_5476_; lean_object* v_savedPos_x3f_5477_; lean_object* v_forbiddenTk_x3f_5478_; lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5485_; 
v_quotDepth_5475_ = lean_ctor_get(v_x_5474_, 1);
v_suppressInsideQuot_5476_ = lean_ctor_get_uint8(v_x_5474_, sizeof(void*)*4);
v_savedPos_x3f_5477_ = lean_ctor_get(v_x_5474_, 2);
v_forbiddenTk_x3f_5478_ = lean_ctor_get(v_x_5474_, 3);
v_isSharedCheck_5485_ = !lean_is_exclusive(v_x_5474_);
if (v_isSharedCheck_5485_ == 0)
{
lean_object* v_unused_5486_; 
v_unused_5486_ = lean_ctor_get(v_x_5474_, 0);
lean_dec(v_unused_5486_);
v___x_5480_ = v_x_5474_;
v_isShared_5481_ = v_isSharedCheck_5485_;
goto v_resetjp_5479_;
}
else
{
lean_inc(v_forbiddenTk_x3f_5478_);
lean_inc(v_savedPos_x3f_5477_);
lean_inc(v_quotDepth_5475_);
lean_dec(v_x_5474_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5485_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v___x_5483_; 
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 0, v_prec_5473_);
v___x_5483_ = v___x_5480_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v_prec_5473_);
lean_ctor_set(v_reuseFailAlloc_5484_, 1, v_quotDepth_5475_);
lean_ctor_set(v_reuseFailAlloc_5484_, 2, v_savedPos_x3f_5477_);
lean_ctor_set(v_reuseFailAlloc_5484_, 3, v_forbiddenTk_x3f_5478_);
lean_ctor_set_uint8(v_reuseFailAlloc_5484_, sizeof(void*)*4, v_suppressInsideQuot_5476_);
v___x_5483_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
return v___x_5483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object* v___y_5487_){
_start:
{
lean_inc(v___y_5487_);
return v___y_5487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object* v___y_5488_){
_start:
{
lean_object* v_res_5489_; 
v_res_5489_ = l_Lean_Parser_parserOfStack___lam__1(v___y_5488_);
lean_dec(v___y_5488_);
return v_res_5489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object* v___y_5490_){
_start:
{
lean_inc_ref(v___y_5490_);
return v___y_5490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object* v___y_5491_){
_start:
{
lean_object* v_res_5492_; 
v_res_5492_ = l_Lean_Parser_parserOfStack___lam__2(v___y_5491_);
lean_dec_ref(v___y_5491_);
return v_res_5492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* v_offset_5499_, lean_object* v_prec_5500_){
_start:
{
lean_object* v___f_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; 
v___f_5501_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___lam__0), 2, 1);
lean_closure_set(v___f_5501_, 0, v_prec_5500_);
v___x_5502_ = ((lean_object*)(l_Lean_Parser_parserOfStack___closed__2));
v___x_5503_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___boxed), 3, 1);
lean_closure_set(v___x_5503_, 0, v_offset_5499_);
v___x_5504_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5504_, 0, v___f_5501_);
lean_closure_set(v___x_5504_, 1, v___x_5503_);
v___x_5505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5505_, 0, v___x_5502_);
lean_ctor_set(v___x_5505_, 1, v___x_5504_);
return v___x_5505_;
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
