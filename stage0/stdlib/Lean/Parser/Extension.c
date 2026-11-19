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
lean_object* lean_mk_thunk(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedGlobals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l_Lean_Parser_AliasTable_getConst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "parser `"};
static const lean_object* l_Lean_Parser_AliasTable_getConst___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_AliasTable_getConst___redArg___closed__0_value;
static const lean_string_object l_Lean_Parser_AliasTable_getConst___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` was not found"};
static const lean_object* l_Lean_Parser_AliasTable_getConst___redArg___closed__1 = (const lean_object*)&l_Lean_Parser_AliasTable_getConst___redArg___closed__1_value;
static const lean_string_object l_Lean_Parser_AliasTable_getConst___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` is not a constant, it takes one argument"};
static const lean_object* l_Lean_Parser_AliasTable_getConst___redArg___closed__2 = (const lean_object*)&l_Lean_Parser_AliasTable_getConst___redArg___closed__2_value;
static const lean_string_object l_Lean_Parser_AliasTable_getConst___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "` is not a constant, it takes two arguments"};
static const lean_object* l_Lean_Parser_AliasTable_getConst___redArg___closed__3 = (const lean_object*)&l_Lean_Parser_AliasTable_getConst___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getConst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getConst___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getConst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getConst___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_AliasTable_getUnary___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` does not take one argument"};
static const lean_object* l_Lean_Parser_AliasTable_getUnary___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_AliasTable_getUnary___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getUnary___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getUnary___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getUnary(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getUnary___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_AliasTable_getBinary___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` does not take two arguments"};
static const lean_object* l_Lean_Parser_AliasTable_getBinary___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_AliasTable_getBinary___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getBinary___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getBinary___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getBinary(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getBinary___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescrCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "failed to load parser `"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_parserExtension;
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKindCategories___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKindCategories___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Parser_getSyntaxNodeKindCategories___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_getSyntaxNodeKindCategories___closed__0 = (const lean_object*)&l_Lean_Parser_getSyntaxNodeKindCategories___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKindCategories(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConst_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConst___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConst(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "aliasExtension"};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Parser_mkParserOfConstantUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(10, 155, 76, 129, 210, 58, 191, 8)}};
static const lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_aliasExtension;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl___redArg(lean_object* v_x_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = lean_obj_tag_nat(v_x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl___redArg___boxed(lean_object* v_x_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Parser_AliasValue_ctorIdx___impl___redArg(v_x_470_);
lean_dec_ref(v_x_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl(lean_object* v_00_u03b1_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = lean_obj_tag_nat(v_x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl___boxed(lean_object* v_00_u03b1_475_, lean_object* v_x_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Parser_AliasValue_ctorIdx___impl(v_00_u03b1_475_, v_x_476_);
lean_dec_ref(v_x_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___redArg(lean_object* v_t_478_, lean_object* v_k_479_){
_start:
{
lean_object* v_p_480_; lean_object* v___x_481_; 
v_p_480_ = lean_ctor_get(v_t_478_, 0);
lean_inc(v_p_480_);
lean_dec_ref(v_t_478_);
v___x_481_ = lean_apply_1(v_k_479_, v_p_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim(lean_object* v_00_u03b1_482_, lean_object* v_motive_483_, lean_object* v_ctorIdx_484_, lean_object* v_t_485_, lean_object* v_h_486_, lean_object* v_k_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_485_, v_k_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___boxed(lean_object* v_00_u03b1_489_, lean_object* v_motive_490_, lean_object* v_ctorIdx_491_, lean_object* v_t_492_, lean_object* v_h_493_, lean_object* v_k_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_Parser_AliasValue_ctorElim(v_00_u03b1_489_, v_motive_490_, v_ctorIdx_491_, v_t_492_, v_h_493_, v_k_494_);
lean_dec(v_ctorIdx_491_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim___redArg(lean_object* v_t_496_, lean_object* v_const_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_496_, v_const_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim(lean_object* v_00_u03b1_499_, lean_object* v_motive_500_, lean_object* v_t_501_, lean_object* v_h_502_, lean_object* v_const_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_501_, v_const_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim___redArg(lean_object* v_t_505_, lean_object* v_unary_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_505_, v_unary_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim(lean_object* v_00_u03b1_508_, lean_object* v_motive_509_, lean_object* v_t_510_, lean_object* v_h_511_, lean_object* v_unary_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_510_, v_unary_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim___redArg(lean_object* v_t_514_, lean_object* v_binary_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_514_, v_binary_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim(lean_object* v_00_u03b1_517_, lean_object* v_motive_518_, lean_object* v_t_519_, lean_object* v_h_520_, lean_object* v_binary_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_519_, v_binary_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___impl(lean_object* v_x_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = lean_obj_tag_nat(v_x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___impl___boxed(lean_object* v_x_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___impl(v_x_525_);
lean_dec_ref(v_x_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(lean_object* v_t_527_, lean_object* v_k_528_){
_start:
{
switch(lean_obj_tag(v_t_527_))
{
case 0:
{
lean_object* v_val_529_; lean_object* v___x_530_; 
v_val_529_ = lean_ctor_get(v_t_527_, 0);
lean_inc_ref(v_val_529_);
lean_dec_ref_known(v_t_527_, 1);
v___x_530_ = lean_apply_1(v_k_528_, v_val_529_);
return v___x_530_;
}
case 1:
{
lean_object* v_val_531_; lean_object* v___x_532_; 
v_val_531_ = lean_ctor_get(v_t_527_, 0);
lean_inc(v_val_531_);
lean_dec_ref_known(v_t_527_, 1);
v___x_532_ = lean_apply_1(v_k_528_, v_val_531_);
return v___x_532_;
}
case 2:
{
lean_object* v_catName_533_; lean_object* v_declName_534_; uint8_t v_behavior_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_catName_533_ = lean_ctor_get(v_t_527_, 0);
lean_inc(v_catName_533_);
v_declName_534_ = lean_ctor_get(v_t_527_, 1);
lean_inc(v_declName_534_);
v_behavior_535_ = lean_ctor_get_uint8(v_t_527_, sizeof(void*)*2);
lean_dec_ref_known(v_t_527_, 2);
v___x_536_ = lean_box(v_behavior_535_);
v___x_537_ = lean_apply_3(v_k_528_, v_catName_533_, v_declName_534_, v___x_536_);
return v___x_537_;
}
default: 
{
lean_object* v_catName_538_; lean_object* v_declName_539_; uint8_t v_leading_540_; lean_object* v_firstTokens_541_; lean_object* v_prio_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_catName_538_ = lean_ctor_get(v_t_527_, 0);
lean_inc(v_catName_538_);
v_declName_539_ = lean_ctor_get(v_t_527_, 1);
lean_inc(v_declName_539_);
v_leading_540_ = lean_ctor_get_uint8(v_t_527_, sizeof(void*)*4);
v_firstTokens_541_ = lean_ctor_get(v_t_527_, 2);
lean_inc(v_firstTokens_541_);
v_prio_542_ = lean_ctor_get(v_t_527_, 3);
lean_inc(v_prio_542_);
lean_dec_ref_known(v_t_527_, 4);
v___x_543_ = lean_box(v_leading_540_);
v___x_544_ = lean_apply_5(v_k_528_, v_catName_538_, v_declName_539_, v___x_543_, v_firstTokens_541_, v_prio_542_);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(lean_object* v_motive_545_, lean_object* v_ctorIdx_546_, lean_object* v_t_547_, lean_object* v_h_548_, lean_object* v_k_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_547_, v_k_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___boxed(lean_object* v_motive_551_, lean_object* v_ctorIdx_552_, lean_object* v_t_553_, lean_object* v_h_554_, lean_object* v_k_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(v_motive_551_, v_ctorIdx_552_, v_t_553_, v_h_554_, v_k_555_);
lean_dec(v_ctorIdx_552_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim___redArg(lean_object* v_t_557_, lean_object* v_token_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_557_, v_token_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim(lean_object* v_motive_560_, lean_object* v_t_561_, lean_object* v_h_562_, lean_object* v_token_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_561_, v_token_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim___redArg(lean_object* v_t_565_, lean_object* v_kind_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_565_, v_kind_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim(lean_object* v_motive_568_, lean_object* v_t_569_, lean_object* v_h_570_, lean_object* v_kind_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_569_, v_kind_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim___redArg(lean_object* v_t_573_, lean_object* v_category_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_573_, v_category_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim(lean_object* v_motive_576_, lean_object* v_t_577_, lean_object* v_h_578_, lean_object* v_category_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_577_, v_category_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim___redArg(lean_object* v_t_581_, lean_object* v_parser_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_581_, v_parser_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim(lean_object* v_motive_584_, lean_object* v_t_585_, lean_object* v_h_586_, lean_object* v_parser_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_585_, v_parser_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___impl(lean_object* v_x_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_tag_nat(v_x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___impl___boxed(lean_object* v_x_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Parser_ParserExtension_Entry_ctorIdx___impl(v_x_596_);
lean_dec_ref(v_x_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(lean_object* v_t_598_, lean_object* v_k_599_){
_start:
{
switch(lean_obj_tag(v_t_598_))
{
case 0:
{
lean_object* v_val_600_; lean_object* v___x_601_; 
v_val_600_ = lean_ctor_get(v_t_598_, 0);
lean_inc_ref(v_val_600_);
lean_dec_ref_known(v_t_598_, 1);
v___x_601_ = lean_apply_1(v_k_599_, v_val_600_);
return v___x_601_;
}
case 1:
{
lean_object* v_val_602_; lean_object* v___x_603_; 
v_val_602_ = lean_ctor_get(v_t_598_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v_t_598_, 1);
v___x_603_ = lean_apply_1(v_k_599_, v_val_602_);
return v___x_603_;
}
case 2:
{
lean_object* v_catName_604_; lean_object* v_declName_605_; uint8_t v_behavior_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_catName_604_ = lean_ctor_get(v_t_598_, 0);
lean_inc(v_catName_604_);
v_declName_605_ = lean_ctor_get(v_t_598_, 1);
lean_inc(v_declName_605_);
v_behavior_606_ = lean_ctor_get_uint8(v_t_598_, sizeof(void*)*2);
lean_dec_ref_known(v_t_598_, 2);
v___x_607_ = lean_box(v_behavior_606_);
v___x_608_ = lean_apply_3(v_k_599_, v_catName_604_, v_declName_605_, v___x_607_);
return v___x_608_;
}
default: 
{
lean_object* v_catName_609_; lean_object* v_declName_610_; uint8_t v_leading_611_; lean_object* v_p_612_; lean_object* v_prio_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_catName_609_ = lean_ctor_get(v_t_598_, 0);
lean_inc(v_catName_609_);
v_declName_610_ = lean_ctor_get(v_t_598_, 1);
lean_inc(v_declName_610_);
v_leading_611_ = lean_ctor_get_uint8(v_t_598_, sizeof(void*)*4);
v_p_612_ = lean_ctor_get(v_t_598_, 2);
lean_inc_ref(v_p_612_);
v_prio_613_ = lean_ctor_get(v_t_598_, 3);
lean_inc(v_prio_613_);
lean_dec_ref_known(v_t_598_, 4);
v___x_614_ = lean_box(v_leading_611_);
v___x_615_ = lean_apply_5(v_k_599_, v_catName_609_, v_declName_610_, v___x_614_, v_p_612_, v_prio_613_);
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim(lean_object* v_motive_616_, lean_object* v_ctorIdx_617_, lean_object* v_t_618_, lean_object* v_h_619_, lean_object* v_k_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_618_, v_k_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___boxed(lean_object* v_motive_622_, lean_object* v_ctorIdx_623_, lean_object* v_t_624_, lean_object* v_h_625_, lean_object* v_k_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Parser_ParserExtension_Entry_ctorElim(v_motive_622_, v_ctorIdx_623_, v_t_624_, v_h_625_, v_k_626_);
lean_dec(v_ctorIdx_623_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim___redArg(lean_object* v_t_628_, lean_object* v_token_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_628_, v_token_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim(lean_object* v_motive_631_, lean_object* v_t_632_, lean_object* v_h_633_, lean_object* v_token_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_632_, v_token_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim___redArg(lean_object* v_t_636_, lean_object* v_kind_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_636_, v_kind_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim(lean_object* v_motive_639_, lean_object* v_t_640_, lean_object* v_h_641_, lean_object* v_kind_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_640_, v_kind_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim___redArg(lean_object* v_t_644_, lean_object* v_category_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_644_, v_category_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim(lean_object* v_motive_647_, lean_object* v_t_648_, lean_object* v_h_649_, lean_object* v_category_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_648_, v_category_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim___redArg(lean_object* v_t_652_, lean_object* v_parser_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_652_, v_parser_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim(lean_object* v_motive_655_, lean_object* v_t_656_, lean_object* v_h_657_, lean_object* v_parser_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_656_, v_parser_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object* v_x_664_){
_start:
{
switch(lean_obj_tag(v_x_664_))
{
case 0:
{
lean_object* v_val_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
v_val_665_ = lean_ctor_get(v_x_664_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v_x_664_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_val_665_);
lean_dec(v_x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_val_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
case 1:
{
lean_object* v_val_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
v_val_673_ = lean_ctor_get(v_x_664_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v_x_664_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_val_673_);
lean_dec(v_x_664_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_val_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
case 2:
{
lean_object* v_catName_681_; lean_object* v_declName_682_; uint8_t v_behavior_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
v_catName_681_ = lean_ctor_get(v_x_664_, 0);
v_declName_682_ = lean_ctor_get(v_x_664_, 1);
v_behavior_683_ = lean_ctor_get_uint8(v_x_664_, sizeof(void*)*2);
v_isSharedCheck_690_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v_x_664_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_declName_682_);
lean_inc(v_catName_681_);
lean_dec(v_x_664_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_catName_681_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_declName_682_);
lean_ctor_set_uint8(v_reuseFailAlloc_689_, sizeof(void*)*2, v_behavior_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
default: 
{
lean_object* v_p_691_; lean_object* v_info_692_; lean_object* v_catName_693_; lean_object* v_declName_694_; uint8_t v_leading_695_; lean_object* v_prio_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
v_p_691_ = lean_ctor_get(v_x_664_, 2);
v_info_692_ = lean_ctor_get(v_p_691_, 0);
lean_inc_ref(v_info_692_);
v_catName_693_ = lean_ctor_get(v_x_664_, 0);
v_declName_694_ = lean_ctor_get(v_x_664_, 1);
v_leading_695_ = lean_ctor_get_uint8(v_x_664_, sizeof(void*)*4);
v_prio_696_ = lean_ctor_get(v_x_664_, 3);
v_isSharedCheck_704_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v_x_664_, 2);
lean_dec(v_unused_705_);
v___x_698_ = v_x_664_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_prio_696_);
lean_inc(v_declName_694_);
lean_inc(v_catName_693_);
lean_dec(v_x_664_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_firstTokens_700_; lean_object* v___x_702_; 
v_firstTokens_700_ = lean_ctor_get(v_info_692_, 2);
lean_inc(v_firstTokens_700_);
lean_dec_ref(v_info_692_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 2, v_firstTokens_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_catName_693_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_declName_694_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_firstTokens_700_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_prio_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_703_, sizeof(void*)*4, v_leading_695_);
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
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_box(1);
v___x_707_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_708_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_709_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_707_);
lean_ctor_set(v___x_709_, 2, v___x_707_);
lean_ctor_set(v___x_709_, 3, v___x_706_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default(void){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_obj_once(&l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0, &l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0_once, _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0);
return v___x_710_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState(void){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object* v_tokens_715_, lean_object* v_tk_716_){
_start:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = ((lean_object*)(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0));
v___x_718_ = lean_string_dec_eq(v_tk_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Data_Trie_find_x3f___redArg(v_tokens_715_, v_tk_716_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_inc_ref(v_tk_716_);
v___x_720_ = l_Lean_Data_Trie_insert___redArg(v_tokens_715_, v_tk_716_, v_tk_716_);
lean_dec_ref(v_tk_716_);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
else
{
lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v_tk_716_);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v___x_719_, 0);
lean_dec(v_unused_729_);
v___x_723_ = v___x_719_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_dec(v___x_719_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v_tokens_715_);
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_tokens_715_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
lean_object* v___x_730_; 
lean_dec_ref(v_tk_716_);
lean_dec_ref(v_tokens_715_);
v___x_730_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1));
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg(lean_object* v_catName_733_){
_start:
{
lean_object* v___x_734_; uint8_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_734_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0));
v___x_735_ = 1;
v___x_736_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_733_, v___x_735_);
v___x_737_ = lean_string_append(v___x_734_, v___x_736_);
lean_dec_ref(v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_739_ = lean_string_append(v___x_737_, v___x_738_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object* v_00_u03b1_741_, lean_object* v_catName_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object* v_categories_746_, lean_object* v_catName_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__0));
v___x_749_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__1));
v___x_750_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_748_, v___x_749_, v_categories_746_, v_catName_747_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory___boxed(lean_object* v_categories_751_, lean_object* v_catName_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Parser_getCategory(v_categories_751_, v_catName_752_);
lean_dec_ref(v_categories_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(lean_object* v_as_755_){
_start:
{
lean_object* v___f_756_; lean_object* v___x_757_; 
v___f_756_ = ((lean_object*)(l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0));
v___x_757_ = l_List_eraseDupsBy___redArg(v___f_756_, v_as_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(lean_object* v_p_758_, lean_object* v_prio_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
lean_dec(v_prio_759_);
lean_dec_ref(v_p_758_);
return v_x_760_;
}
else
{
lean_object* v_head_762_; lean_object* v_tail_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_783_; 
v_head_762_ = lean_ctor_get(v_x_761_, 0);
v_tail_763_ = lean_ctor_get(v_x_761_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_783_ == 0)
{
v___x_765_ = v_x_761_;
v_isShared_766_ = v_isSharedCheck_783_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_tail_763_);
lean_inc(v_head_762_);
lean_dec(v_x_761_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_783_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v_leadingTable_767_; lean_object* v_leadingParsers_768_; lean_object* v_trailingTable_769_; lean_object* v_trailingParsers_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_782_; 
v_leadingTable_767_ = lean_ctor_get(v_x_760_, 0);
v_leadingParsers_768_ = lean_ctor_get(v_x_760_, 1);
v_trailingTable_769_ = lean_ctor_get(v_x_760_, 2);
v_trailingParsers_770_ = lean_ctor_get(v_x_760_, 3);
v_isSharedCheck_782_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_782_ == 0)
{
v___x_772_ = v_x_760_;
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_trailingParsers_770_);
lean_inc(v_trailingTable_769_);
lean_inc(v_leadingParsers_768_);
lean_inc(v_leadingTable_767_);
lean_dec(v_x_760_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
lean_inc(v_prio_759_);
lean_inc_ref(v_p_758_);
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 0);
lean_ctor_set(v___x_765_, 1, v_prio_759_);
lean_ctor_set(v___x_765_, 0, v_p_758_);
v___x_775_ = v___x_765_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_p_758_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_prio_759_);
v___x_775_ = v_reuseFailAlloc_781_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = l_Lean_Parser_TokenMap_insert___redArg(v_leadingTable_767_, v_head_762_, v___x_775_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_776_);
v___x_778_ = v___x_772_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_leadingParsers_768_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_trailingTable_769_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v_trailingParsers_770_);
v___x_778_ = v_reuseFailAlloc_780_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
v_x_760_ = v___x_778_;
v_x_761_ = v_tail_763_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_784_, lean_object* v_vals_785_, lean_object* v_i_786_, lean_object* v_k_787_){
_start:
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = lean_array_get_size(v_keys_784_);
v___x_789_ = lean_nat_dec_lt(v_i_786_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
lean_dec(v_i_786_);
v___x_790_ = lean_box(0);
return v___x_790_;
}
else
{
lean_object* v_k_x27_791_; uint8_t v___x_792_; 
v_k_x27_791_ = lean_array_fget_borrowed(v_keys_784_, v_i_786_);
v___x_792_ = lean_name_eq(v_k_787_, v_k_x27_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = lean_nat_add(v_i_786_, v___x_793_);
lean_dec(v_i_786_);
v_i_786_ = v___x_794_;
goto _start;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_array_fget_borrowed(v_vals_785_, v_i_786_);
lean_dec(v_i_786_);
lean_inc(v___x_796_);
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_798_, lean_object* v_vals_799_, lean_object* v_i_800_, lean_object* v_k_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_798_, v_vals_799_, v_i_800_, v_k_801_);
lean_dec(v_k_801_);
lean_dec_ref(v_vals_799_);
lean_dec_ref(v_keys_798_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(lean_object* v_x_803_, size_t v_x_804_, lean_object* v_x_805_){
_start:
{
if (lean_obj_tag(v_x_803_) == 0)
{
lean_object* v_es_806_; lean_object* v___x_807_; size_t v___x_808_; size_t v___x_809_; lean_object* v_j_810_; lean_object* v___x_811_; 
v_es_806_ = lean_ctor_get(v_x_803_, 0);
v___x_807_ = lean_box(2);
v___x_808_ = ((size_t)31ULL);
v___x_809_ = lean_usize_land(v_x_804_, v___x_808_);
v_j_810_ = lean_usize_to_nat(v___x_809_);
v___x_811_ = lean_array_get_borrowed(v___x_807_, v_es_806_, v_j_810_);
lean_dec(v_j_810_);
switch(lean_obj_tag(v___x_811_))
{
case 0:
{
lean_object* v_key_812_; lean_object* v_val_813_; uint8_t v___x_814_; 
v_key_812_ = lean_ctor_get(v___x_811_, 0);
v_val_813_ = lean_ctor_get(v___x_811_, 1);
v___x_814_ = lean_name_eq(v_x_805_, v_key_812_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
v___x_815_ = lean_box(0);
return v___x_815_;
}
else
{
lean_object* v___x_816_; 
lean_inc(v_val_813_);
v___x_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_816_, 0, v_val_813_);
return v___x_816_;
}
}
case 1:
{
lean_object* v_node_817_; size_t v___x_818_; size_t v___x_819_; 
v_node_817_ = lean_ctor_get(v___x_811_, 0);
v___x_818_ = ((size_t)5ULL);
v___x_819_ = lean_usize_shift_right(v_x_804_, v___x_818_);
v_x_803_ = v_node_817_;
v_x_804_ = v___x_819_;
goto _start;
}
default: 
{
lean_object* v___x_821_; 
v___x_821_ = lean_box(0);
return v___x_821_;
}
}
}
else
{
lean_object* v_ks_822_; lean_object* v_vs_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_ks_822_ = lean_ctor_get(v_x_803_, 0);
v_vs_823_ = lean_ctor_get(v_x_803_, 1);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_ks_822_, v_vs_823_, v___x_824_, v_x_805_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg___boxed(lean_object* v_x_826_, lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
size_t v_x_496__boxed_829_; lean_object* v_res_830_; 
v_x_496__boxed_829_ = lean_unbox_usize(v_x_827_);
lean_dec(v_x_827_);
v_res_830_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_826_, v_x_496__boxed_829_, v_x_828_);
lean_dec(v_x_828_);
lean_dec_ref(v_x_826_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
uint64_t v___y_834_; 
if (lean_obj_tag(v_x_832_) == 0)
{
uint64_t v___x_837_; 
v___x_837_ = 1723ULL;
v___y_834_ = v___x_837_;
goto v___jp_833_;
}
else
{
uint64_t v_hash_838_; 
v_hash_838_ = lean_ctor_get_uint64(v_x_832_, sizeof(void*)*2);
v___y_834_ = v_hash_838_;
goto v___jp_833_;
}
v___jp_833_:
{
size_t v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_uint64_to_usize(v___y_834_);
v___x_836_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_831_, v___x_835_, v_x_832_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg___boxed(lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_839_, v_x_840_);
lean_dec(v_x_840_);
lean_dec_ref(v_x_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
if (lean_obj_tag(v_a_842_) == 0)
{
lean_object* v___x_844_; 
v___x_844_ = l_List_reverse___redArg(v_a_843_);
return v___x_844_;
}
else
{
lean_object* v_head_845_; lean_object* v_tail_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_856_; 
v_head_845_ = lean_ctor_get(v_a_842_, 0);
v_tail_846_ = lean_ctor_get(v_a_842_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v_a_842_);
if (v_isSharedCheck_856_ == 0)
{
v___x_848_ = v_a_842_;
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_tail_846_);
lean_inc(v_head_845_);
lean_dec(v_a_842_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_850_ = lean_box(0);
v___x_851_ = l_Lean_Name_str___override(v___x_850_, v_head_845_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v_a_843_);
lean_ctor_set(v___x_848_, 0, v___x_851_);
v___x_853_ = v___x_848_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_a_843_);
v___x_853_ = v_reuseFailAlloc_855_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
v_a_842_ = v_tail_846_;
v_a_843_ = v___x_853_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object* v_categories_857_, lean_object* v_catName_858_, lean_object* v_declName_859_, lean_object* v_p_860_, lean_object* v_prio_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_857_, v_catName_858_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_863_; 
lean_dec(v_prio_861_);
lean_dec_ref(v_p_860_);
lean_dec(v_declName_859_);
lean_dec_ref(v_categories_857_);
v___x_863_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_858_);
return v___x_863_;
}
else
{
lean_object* v_val_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_910_; 
v_val_864_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_910_ == 0)
{
v___x_866_ = v___x_862_;
v_isShared_867_ = v_isSharedCheck_910_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_val_864_);
lean_dec(v___x_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_910_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_info_868_; lean_object* v_declName_869_; lean_object* v_kinds_870_; lean_object* v_tables_871_; uint8_t v_behavior_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_909_; 
v_info_868_ = lean_ctor_get(v_p_860_, 0);
v_declName_869_ = lean_ctor_get(v_val_864_, 0);
v_kinds_870_ = lean_ctor_get(v_val_864_, 1);
v_tables_871_ = lean_ctor_get(v_val_864_, 2);
v_behavior_872_ = lean_ctor_get_uint8(v_val_864_, sizeof(void*)*3);
v_isSharedCheck_909_ = !lean_is_exclusive(v_val_864_);
if (v_isSharedCheck_909_ == 0)
{
v___x_874_ = v_val_864_;
v_isShared_875_ = v_isSharedCheck_909_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_tables_871_);
lean_inc(v_kinds_870_);
lean_inc(v_declName_869_);
lean_dec(v_val_864_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_909_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v_firstTokens_876_; lean_object* v_kinds_877_; lean_object* v_tks_879_; 
v_firstTokens_876_ = lean_ctor_get(v_info_868_, 2);
v_kinds_877_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_870_, v_declName_859_);
switch(lean_obj_tag(v_firstTokens_876_))
{
case 2:
{
lean_object* v_a_891_; 
v_a_891_ = lean_ctor_get(v_firstTokens_876_, 0);
lean_inc(v_a_891_);
v_tks_879_ = v_a_891_;
goto v___jp_878_;
}
case 3:
{
lean_object* v_a_892_; 
v_a_892_ = lean_ctor_get(v_firstTokens_876_, 0);
lean_inc(v_a_892_);
v_tks_879_ = v_a_892_;
goto v___jp_878_;
}
default: 
{
lean_object* v_leadingTable_893_; lean_object* v_leadingParsers_894_; lean_object* v_trailingTable_895_; lean_object* v_trailingParsers_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_908_; 
lean_del_object(v___x_874_);
lean_del_object(v___x_866_);
v_leadingTable_893_ = lean_ctor_get(v_tables_871_, 0);
v_leadingParsers_894_ = lean_ctor_get(v_tables_871_, 1);
v_trailingTable_895_ = lean_ctor_get(v_tables_871_, 2);
v_trailingParsers_896_ = lean_ctor_get(v_tables_871_, 3);
v_isSharedCheck_908_ = !lean_is_exclusive(v_tables_871_);
if (v_isSharedCheck_908_ == 0)
{
v___x_898_ = v_tables_871_;
v_isShared_899_ = v_isSharedCheck_908_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_trailingParsers_896_);
lean_inc(v_trailingTable_895_);
lean_inc(v_leadingParsers_894_);
lean_inc(v_leadingTable_893_);
lean_dec(v_tables_871_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_908_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_tables_903_; 
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v_p_860_);
lean_ctor_set(v___x_900_, 1, v_prio_861_);
v___x_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v_leadingParsers_894_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_901_);
v_tables_903_ = v___x_898_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_leadingTable_893_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_trailingTable_895_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_trailingParsers_896_);
v_tables_903_ = v_reuseFailAlloc_907_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_904_, 0, v_declName_869_);
lean_ctor_set(v___x_904_, 1, v_kinds_877_);
lean_ctor_set(v___x_904_, 2, v_tables_903_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*3, v_behavior_872_);
v___x_905_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_857_, v_catName_858_, v___x_904_);
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
return v___x_906_;
}
}
}
}
v___jp_878_:
{
lean_object* v___x_880_; lean_object* v_tks_881_; lean_object* v___x_882_; lean_object* v_tables_883_; lean_object* v___x_885_; 
v___x_880_ = lean_box(0);
v_tks_881_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_879_, v___x_880_);
v___x_882_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_881_);
v_tables_883_ = l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(v_p_860_, v_prio_861_, v_tables_871_, v___x_882_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 2, v_tables_883_);
lean_ctor_set(v___x_874_, 1, v_kinds_877_);
v___x_885_ = v___x_874_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_declName_869_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_kinds_877_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_tables_883_);
lean_ctor_set_uint8(v_reuseFailAlloc_890_, sizeof(void*)*3, v_behavior_872_);
v___x_885_ = v_reuseFailAlloc_890_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_886_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_857_, v_catName_858_, v___x_885_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_886_);
v___x_888_ = v___x_866_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(lean_object* v_00_u03b2_911_, lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_912_, v_x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___boxed(lean_object* v_00_u03b2_915_, lean_object* v_x_916_, lean_object* v_x_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(v_00_u03b2_915_, v_x_916_, v_x_917_);
lean_dec(v_x_917_);
lean_dec_ref(v_x_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_object* v_00_u03b2_919_, lean_object* v_x_920_, size_t v_x_921_, lean_object* v_x_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_920_, v_x_921_, v_x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___boxed(lean_object* v_00_u03b2_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
size_t v_x_665__boxed_928_; lean_object* v_res_929_; 
v_x_665__boxed_928_ = lean_unbox_usize(v_x_926_);
lean_dec(v_x_926_);
v_res_929_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(v_00_u03b2_924_, v_x_925_, v_x_665__boxed_928_, v_x_927_);
lean_dec(v_x_927_);
lean_dec_ref(v_x_925_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_930_, lean_object* v_keys_931_, lean_object* v_vals_932_, lean_object* v_heq_933_, lean_object* v_i_934_, lean_object* v_k_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_931_, v_vals_932_, v_i_934_, v_k_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_937_, lean_object* v_keys_938_, lean_object* v_vals_939_, lean_object* v_heq_940_, lean_object* v_i_941_, lean_object* v_k_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(v_00_u03b2_937_, v_keys_938_, v_vals_939_, v_heq_940_, v_i_941_, v_k_942_);
lean_dec(v_k_942_);
lean_dec_ref(v_vals_939_);
lean_dec_ref(v_keys_938_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(lean_object* v_p_944_, lean_object* v_prio_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
if (lean_obj_tag(v_x_947_) == 0)
{
lean_dec(v_prio_945_);
lean_dec_ref(v_p_944_);
return v_x_946_;
}
else
{
lean_object* v_head_948_; lean_object* v_tail_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_969_; 
v_head_948_ = lean_ctor_get(v_x_947_, 0);
v_tail_949_ = lean_ctor_get(v_x_947_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_x_947_);
if (v_isSharedCheck_969_ == 0)
{
v___x_951_ = v_x_947_;
v_isShared_952_ = v_isSharedCheck_969_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_tail_949_);
lean_inc(v_head_948_);
lean_dec(v_x_947_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_969_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_leadingTable_953_; lean_object* v_leadingParsers_954_; lean_object* v_trailingTable_955_; lean_object* v_trailingParsers_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_968_; 
v_leadingTable_953_ = lean_ctor_get(v_x_946_, 0);
v_leadingParsers_954_ = lean_ctor_get(v_x_946_, 1);
v_trailingTable_955_ = lean_ctor_get(v_x_946_, 2);
v_trailingParsers_956_ = lean_ctor_get(v_x_946_, 3);
v_isSharedCheck_968_ = !lean_is_exclusive(v_x_946_);
if (v_isSharedCheck_968_ == 0)
{
v___x_958_ = v_x_946_;
v_isShared_959_ = v_isSharedCheck_968_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_trailingParsers_956_);
lean_inc(v_trailingTable_955_);
lean_inc(v_leadingParsers_954_);
lean_inc(v_leadingTable_953_);
lean_dec(v_x_946_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_968_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
lean_inc(v_prio_945_);
lean_inc_ref(v_p_944_);
if (v_isShared_952_ == 0)
{
lean_ctor_set_tag(v___x_951_, 0);
lean_ctor_set(v___x_951_, 1, v_prio_945_);
lean_ctor_set(v___x_951_, 0, v_p_944_);
v___x_961_ = v___x_951_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_p_944_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_prio_945_);
v___x_961_ = v_reuseFailAlloc_967_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = l_Lean_Parser_TokenMap_insert___redArg(v_trailingTable_955_, v_head_948_, v___x_961_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 2, v___x_962_);
v___x_964_ = v___x_958_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_leadingTable_953_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_leadingParsers_954_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_trailingParsers_956_);
v___x_964_ = v_reuseFailAlloc_966_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
v_x_946_ = v___x_964_;
v_x_947_ = v_tail_949_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object* v_tables_970_, lean_object* v_p_971_, lean_object* v_prio_972_){
_start:
{
lean_object* v_tks_974_; lean_object* v_info_979_; lean_object* v_firstTokens_980_; 
v_info_979_ = lean_ctor_get(v_p_971_, 0);
v_firstTokens_980_ = lean_ctor_get(v_info_979_, 2);
switch(lean_obj_tag(v_firstTokens_980_))
{
case 2:
{
lean_object* v_a_981_; 
v_a_981_ = lean_ctor_get(v_firstTokens_980_, 0);
lean_inc(v_a_981_);
v_tks_974_ = v_a_981_;
goto v___jp_973_;
}
case 3:
{
lean_object* v_a_982_; 
v_a_982_ = lean_ctor_get(v_firstTokens_980_, 0);
lean_inc(v_a_982_);
v_tks_974_ = v_a_982_;
goto v___jp_973_;
}
default: 
{
lean_object* v_leadingTable_983_; lean_object* v_leadingParsers_984_; lean_object* v_trailingTable_985_; lean_object* v_trailingParsers_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_995_; 
v_leadingTable_983_ = lean_ctor_get(v_tables_970_, 0);
v_leadingParsers_984_ = lean_ctor_get(v_tables_970_, 1);
v_trailingTable_985_ = lean_ctor_get(v_tables_970_, 2);
v_trailingParsers_986_ = lean_ctor_get(v_tables_970_, 3);
v_isSharedCheck_995_ = !lean_is_exclusive(v_tables_970_);
if (v_isSharedCheck_995_ == 0)
{
v___x_988_ = v_tables_970_;
v_isShared_989_ = v_isSharedCheck_995_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_trailingParsers_986_);
lean_inc(v_trailingTable_985_);
lean_inc(v_leadingParsers_984_);
lean_inc(v_leadingTable_983_);
lean_dec(v_tables_970_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_995_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v_p_971_);
lean_ctor_set(v___x_990_, 1, v_prio_972_);
v___x_991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v_trailingParsers_986_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 3, v___x_991_);
v___x_993_ = v___x_988_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_leadingTable_983_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_leadingParsers_984_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_trailingTable_985_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
v___jp_973_:
{
lean_object* v___x_975_; lean_object* v_tks_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_975_ = lean_box(0);
v_tks_976_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_974_, v___x_975_);
v___x_977_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_976_);
v___x_978_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(v_p_971_, v_prio_972_, v_tables_970_, v___x_977_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object* v_categories_996_, lean_object* v_catName_997_, lean_object* v_declName_998_, lean_object* v_p_999_, lean_object* v_prio_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_996_, v_catName_997_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v___x_1002_; 
lean_dec(v_prio_1000_);
lean_dec_ref(v_p_999_);
lean_dec(v_declName_998_);
lean_dec_ref(v_categories_996_);
v___x_1002_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_997_);
return v___x_1002_;
}
else
{
lean_object* v_val_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1024_; 
v_val_1003_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1005_ = v___x_1001_;
v_isShared_1006_ = v_isSharedCheck_1024_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_val_1003_);
lean_dec(v___x_1001_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1024_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_declName_1007_; lean_object* v_kinds_1008_; lean_object* v_tables_1009_; uint8_t v_behavior_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1023_; 
v_declName_1007_ = lean_ctor_get(v_val_1003_, 0);
v_kinds_1008_ = lean_ctor_get(v_val_1003_, 1);
v_tables_1009_ = lean_ctor_get(v_val_1003_, 2);
v_behavior_1010_ = lean_ctor_get_uint8(v_val_1003_, sizeof(void*)*3);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_val_1003_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1012_ = v_val_1003_;
v_isShared_1013_ = v_isSharedCheck_1023_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_tables_1009_);
lean_inc(v_kinds_1008_);
lean_inc(v_declName_1007_);
lean_dec(v_val_1003_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1023_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v_kinds_1014_; lean_object* v_tables_1015_; lean_object* v___x_1017_; 
v_kinds_1014_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_1008_, v_declName_998_);
v_tables_1015_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(v_tables_1009_, v_p_999_, v_prio_1000_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 2, v_tables_1015_);
lean_ctor_set(v___x_1012_, 1, v_kinds_1014_);
v___x_1017_ = v___x_1012_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_declName_1007_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_kinds_1014_);
lean_ctor_set(v_reuseFailAlloc_1022_, 2, v_tables_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, sizeof(void*)*3, v_behavior_1010_);
v___x_1017_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_996_, v_catName_997_, v___x_1017_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1018_);
v___x_1020_ = v___x_1005_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object* v_categories_1025_, lean_object* v_catName_1026_, lean_object* v_declName_1027_, uint8_t v_leading_1028_, lean_object* v_p_1029_, lean_object* v_prio_1030_){
_start:
{
if (v_leading_1028_ == 0)
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_Parser_addTrailingParser(v_categories_1025_, v_catName_1026_, v_declName_1027_, v_p_1029_, v_prio_1030_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Parser_addLeadingParser(v_categories_1025_, v_catName_1026_, v_declName_1027_, v_p_1029_, v_prio_1030_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object* v_categories_1033_, lean_object* v_catName_1034_, lean_object* v_declName_1035_, lean_object* v_leading_1036_, lean_object* v_p_1037_, lean_object* v_prio_1038_){
_start:
{
uint8_t v_leading_boxed_1039_; lean_object* v_res_1040_; 
v_leading_boxed_1039_ = lean_unbox(v_leading_1036_);
v_res_1040_ = l_Lean_Parser_addParser(v_categories_1033_, v_catName_1034_, v_declName_1035_, v_leading_boxed_1039_, v_p_1037_, v_prio_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
if (lean_obj_tag(v_x_1042_) == 0)
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_x_1041_);
return v___x_1043_;
}
else
{
lean_object* v_head_1044_; lean_object* v_tail_1045_; lean_object* v___x_1046_; 
v_head_1044_ = lean_ctor_get(v_x_1042_, 0);
lean_inc(v_head_1044_);
v_tail_1045_ = lean_ctor_get(v_x_1042_, 1);
lean_inc(v_tail_1045_);
lean_dec_ref_known(v_x_1042_, 2);
v___x_1046_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_x_1041_, v_head_1044_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_dec(v_tail_1045_);
return v___x_1046_;
}
else
{
lean_object* v_a_1047_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v_x_1041_ = v_a_1047_;
v_x_1042_ = v_tail_1045_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object* v_tokenTable_1049_, lean_object* v_info_1050_){
_start:
{
lean_object* v_collectTokens_1051_; lean_object* v___x_1052_; lean_object* v_newTokens_1053_; lean_object* v___x_1054_; 
v_collectTokens_1051_ = lean_ctor_get(v_info_1050_, 0);
lean_inc_ref(v_collectTokens_1051_);
lean_dec_ref(v_info_1050_);
v___x_1052_ = lean_box(0);
v_newTokens_1053_ = lean_apply_1(v_collectTokens_1051_, v___x_1052_);
v___x_1054_ = l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(v_tokenTable_1049_, v_newTokens_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object* v_info_1057_, lean_object* v_declName_1058_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1060_ = l_Lean_Parser_builtinTokenTable;
v___x_1061_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_1062_ = lean_st_ref_swap(v___x_1060_, v___x_1061_);
v___x_1063_ = l_Lean_Parser_addParserTokens(v___x_1062_, v_info_1057_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1080_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1080_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1080_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1068_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0));
v___x_1069_ = l_Lean_privateToUserName(v_declName_1058_);
v___x_1070_ = 1;
v___x_1071_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1069_, v___x_1070_);
v___x_1072_ = lean_string_append(v___x_1068_, v___x_1071_);
lean_dec_ref(v___x_1071_);
v___x_1073_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_1074_ = lean_string_append(v___x_1072_, v___x_1073_);
v___x_1075_ = lean_string_append(v___x_1074_, v_a_1064_);
lean_dec(v_a_1064_);
v___x_1076_ = lean_mk_io_user_error(v___x_1075_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 1);
lean_ctor_set(v___x_1066_, 0, v___x_1076_);
v___x_1078_ = v___x_1066_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1090_; 
lean_dec(v_declName_1058_);
v_a_1081_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1083_ = v___x_1063_;
v_isShared_1084_ = v_isSharedCheck_1090_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1063_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1090_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_st_ref_swap(v___x_1060_, v_a_1081_);
lean_dec(v___x_1086_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set_tag(v___x_1083_, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1085_);
v___x_1088_ = v___x_1083_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1085_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___boxed(lean_object* v_info_1091_, lean_object* v_declName_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_1091_, v_declName_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(lean_object* v_msg_1095_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1097_ = lean_panic_fn_borrowed(v___x_1096_, v_msg_1095_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object* v_s_1101_, lean_object* v_e_1102_){
_start:
{
switch(lean_obj_tag(v_e_1102_))
{
case 0:
{
lean_object* v_val_1103_; lean_object* v_tokens_1104_; lean_object* v_kinds_1105_; lean_object* v_categories_1106_; lean_object* v_aliases_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1125_; 
v_val_1103_ = lean_ctor_get(v_e_1102_, 0);
lean_inc_ref(v_val_1103_);
lean_dec_ref_known(v_e_1102_, 1);
v_tokens_1104_ = lean_ctor_get(v_s_1101_, 0);
v_kinds_1105_ = lean_ctor_get(v_s_1101_, 1);
v_categories_1106_ = lean_ctor_get(v_s_1101_, 2);
v_aliases_1107_ = lean_ctor_get(v_s_1101_, 3);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_s_1101_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1109_ = v_s_1101_;
v_isShared_1110_ = v_isSharedCheck_1125_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_aliases_1107_);
lean_inc(v_categories_1106_);
lean_inc(v_kinds_1105_);
lean_inc(v_tokens_1104_);
lean_dec(v_s_1101_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1125_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; 
v___x_1111_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_1104_, v_val_1103_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_del_object(v___x_1109_);
lean_dec(v_aliases_1107_);
lean_dec_ref(v_categories_1106_);
lean_dec_ref(v_kinds_1105_);
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
v___x_1113_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1114_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1115_ = lean_unsigned_to_nat(175u);
v___x_1116_ = lean_unsigned_to_nat(26u);
v___x_1117_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1118_ = lean_string_append(v___x_1117_, v_a_1112_);
lean_dec(v_a_1112_);
v___x_1119_ = l_mkPanicMessageWithDecl(v___x_1113_, v___x_1114_, v___x_1115_, v___x_1116_, v___x_1118_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1119_);
return v___x_1120_;
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; 
v_a_1121_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1111_, 1);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v_a_1121_);
v___x_1123_ = v___x_1109_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1121_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_kinds_1105_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_categories_1106_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_aliases_1107_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
case 1:
{
lean_object* v_val_1126_; lean_object* v_tokens_1127_; lean_object* v_kinds_1128_; lean_object* v_categories_1129_; lean_object* v_aliases_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
v_val_1126_ = lean_ctor_get(v_e_1102_, 0);
lean_inc(v_val_1126_);
lean_dec_ref_known(v_e_1102_, 1);
v_tokens_1127_ = lean_ctor_get(v_s_1101_, 0);
v_kinds_1128_ = lean_ctor_get(v_s_1101_, 1);
v_categories_1129_ = lean_ctor_get(v_s_1101_, 2);
v_aliases_1130_ = lean_ctor_get(v_s_1101_, 3);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_s_1101_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1132_ = v_s_1101_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_aliases_1130_);
lean_inc(v_categories_1129_);
lean_inc(v_kinds_1128_);
lean_inc(v_tokens_1127_);
lean_dec(v_s_1101_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_1128_, v_val_1126_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v___x_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_tokens_1127_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v_categories_1129_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v_aliases_1130_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
case 2:
{
lean_object* v_catName_1139_; lean_object* v_declName_1140_; uint8_t v_behavior_1141_; lean_object* v_tokens_1142_; lean_object* v_kinds_1143_; lean_object* v_categories_1144_; lean_object* v_aliases_1145_; uint8_t v___x_1146_; 
v_catName_1139_ = lean_ctor_get(v_e_1102_, 0);
lean_inc(v_catName_1139_);
v_declName_1140_ = lean_ctor_get(v_e_1102_, 1);
lean_inc(v_declName_1140_);
v_behavior_1141_ = lean_ctor_get_uint8(v_e_1102_, sizeof(void*)*2);
lean_dec_ref_known(v_e_1102_, 2);
v_tokens_1142_ = lean_ctor_get(v_s_1101_, 0);
v_kinds_1143_ = lean_ctor_get(v_s_1101_, 1);
v_categories_1144_ = lean_ctor_get(v_s_1101_, 2);
v_aliases_1145_ = lean_ctor_get(v_s_1101_, 3);
v___x_1146_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_1144_, v_catName_1139_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1157_; 
lean_inc(v_aliases_1145_);
lean_inc_ref(v_categories_1144_);
lean_inc_ref(v_kinds_1143_);
lean_inc_ref(v_tokens_1142_);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_s_1101_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; lean_object* v_unused_1159_; lean_object* v_unused_1160_; lean_object* v_unused_1161_; 
v_unused_1158_ = lean_ctor_get(v_s_1101_, 3);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v_s_1101_, 2);
lean_dec(v_unused_1159_);
v_unused_1160_ = lean_ctor_get(v_s_1101_, 1);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_s_1101_, 0);
lean_dec(v_unused_1161_);
v___x_1148_ = v_s_1101_;
v_isShared_1149_ = v_isSharedCheck_1157_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v_s_1101_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1157_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1150_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_1151_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_1152_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1152_, 0, v_declName_1140_);
lean_ctor_set(v___x_1152_, 1, v___x_1150_);
lean_ctor_set(v___x_1152_, 2, v___x_1151_);
lean_ctor_set_uint8(v___x_1152_, sizeof(void*)*3, v_behavior_1141_);
v___x_1153_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_1144_, v_catName_1139_, v___x_1152_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 2, v___x_1153_);
v___x_1155_ = v___x_1148_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_tokens_1142_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_kinds_1143_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v_aliases_1145_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
lean_dec(v_declName_1140_);
lean_dec(v_catName_1139_);
return v_s_1101_;
}
}
default: 
{
lean_object* v_catName_1162_; lean_object* v_declName_1163_; uint8_t v_leading_1164_; lean_object* v_p_1165_; lean_object* v_prio_1166_; lean_object* v_tokens_1167_; lean_object* v_kinds_1168_; lean_object* v_categories_1169_; lean_object* v_aliases_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1188_; 
v_catName_1162_ = lean_ctor_get(v_e_1102_, 0);
lean_inc(v_catName_1162_);
v_declName_1163_ = lean_ctor_get(v_e_1102_, 1);
lean_inc(v_declName_1163_);
v_leading_1164_ = lean_ctor_get_uint8(v_e_1102_, sizeof(void*)*4);
v_p_1165_ = lean_ctor_get(v_e_1102_, 2);
lean_inc_ref(v_p_1165_);
v_prio_1166_ = lean_ctor_get(v_e_1102_, 3);
lean_inc(v_prio_1166_);
lean_dec_ref_known(v_e_1102_, 4);
v_tokens_1167_ = lean_ctor_get(v_s_1101_, 0);
v_kinds_1168_ = lean_ctor_get(v_s_1101_, 1);
v_categories_1169_ = lean_ctor_get(v_s_1101_, 2);
v_aliases_1170_ = lean_ctor_get(v_s_1101_, 3);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_s_1101_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1172_ = v_s_1101_;
v_isShared_1173_ = v_isSharedCheck_1188_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_aliases_1170_);
lean_inc(v_categories_1169_);
lean_inc(v_kinds_1168_);
lean_inc(v_tokens_1167_);
lean_dec(v_s_1101_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1188_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_Parser_addParser(v_categories_1169_, v_catName_1162_, v_declName_1163_, v_leading_1164_, v_p_1165_, v_prio_1166_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_del_object(v___x_1172_);
lean_dec(v_aliases_1170_);
lean_dec_ref(v_kinds_1168_);
lean_dec_ref(v_tokens_1167_);
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1177_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1178_ = lean_unsigned_to_nat(185u);
v___x_1179_ = lean_unsigned_to_nat(30u);
v___x_1180_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1181_ = lean_string_append(v___x_1180_, v_a_1175_);
lean_dec(v_a_1175_);
v___x_1182_ = l_mkPanicMessageWithDecl(v___x_1176_, v___x_1177_, v___x_1178_, v___x_1179_, v___x_1181_);
lean_dec_ref(v___x_1181_);
v___x_1183_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1182_);
return v___x_1183_;
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; 
v_a_1184_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1174_, 1);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 2, v_a_1184_);
v___x_1186_ = v___x_1172_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_tokens_1167_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_kinds_1168_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_a_1184_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_aliases_1170_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getConst___redArg(lean_object* v_aliases_1255_, lean_object* v_aliasName_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_aliases_1255_, v_aliasName_1256_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1258_ = ((lean_object*)(l_Lean_Parser_AliasTable_getConst___redArg___closed__0));
v___x_1259_ = 1;
v___x_1260_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1256_, v___x_1259_);
v___x_1261_ = lean_string_append(v___x_1258_, v___x_1260_);
lean_dec_ref(v___x_1260_);
v___x_1262_ = ((lean_object*)(l_Lean_Parser_AliasTable_getConst___redArg___closed__1));
v___x_1263_ = lean_string_append(v___x_1261_, v___x_1262_);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
else
{
lean_object* v_val_1265_; 
v_val_1265_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v___x_1257_, 1);
switch(lean_obj_tag(v_val_1265_))
{
case 0:
{
lean_object* v_p_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_aliasName_1256_);
v_p_1266_ = lean_ctor_get(v_val_1265_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_val_1265_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v_val_1265_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_p_1266_);
lean_dec(v_val_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_p_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
case 1:
{
lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1286_; 
v_isSharedCheck_1286_ = !lean_is_exclusive(v_val_1265_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v_val_1265_, 0);
lean_dec(v_unused_1287_);
v___x_1275_ = v_val_1265_;
v_isShared_1276_ = v_isSharedCheck_1286_;
goto v_resetjp_1274_;
}
else
{
lean_dec(v_val_1265_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1286_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1277_ = ((lean_object*)(l_Lean_Parser_AliasTable_getConst___redArg___closed__0));
v___x_1278_ = 1;
v___x_1279_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1256_, v___x_1278_);
v___x_1280_ = lean_string_append(v___x_1277_, v___x_1279_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = ((lean_object*)(l_Lean_Parser_AliasTable_getConst___redArg___closed__2));
v___x_1282_ = lean_string_append(v___x_1280_, v___x_1281_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set_tag(v___x_1275_, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1282_);
v___x_1284_ = v___x_1275_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
default: 
{
lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1300_; 
v_isSharedCheck_1300_ = !lean_is_exclusive(v_val_1265_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v_val_1265_, 0);
lean_dec(v_unused_1301_);
v___x_1289_ = v_val_1265_;
v_isShared_1290_ = v_isSharedCheck_1300_;
goto v_resetjp_1288_;
}
else
{
lean_dec(v_val_1265_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1300_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1291_ = ((lean_object*)(l_Lean_Parser_AliasTable_getConst___redArg___closed__0));
v___x_1292_ = 1;
v___x_1293_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1256_, v___x_1292_);
v___x_1294_ = lean_string_append(v___x_1291_, v___x_1293_);
lean_dec_ref(v___x_1293_);
v___x_1295_ = ((lean_object*)(l_Lean_Parser_AliasTable_getConst___redArg___closed__3));
v___x_1296_ = lean_string_append(v___x_1294_, v___x_1295_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set_tag(v___x_1289_, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1296_);
v___x_1298_ = v___x_1289_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getConst___redArg___boxed(lean_object* v_aliases_1302_, lean_object* v_aliasName_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Parser_AliasTable_getConst___redArg(v_aliases_1302_, v_aliasName_1303_);
lean_dec(v_aliases_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getConst(lean_object* v_00_u03b1_1305_, lean_object* v_aliases_1306_, lean_object* v_aliasName_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Parser_AliasTable_getConst___redArg(v_aliases_1306_, v_aliasName_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getConst___boxed(lean_object* v_00_u03b1_1309_, lean_object* v_aliases_1310_, lean_object* v_aliasName_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Parser_AliasTable_getConst(v_00_u03b1_1309_, v_aliases_1310_, v_aliasName_1311_);
lean_dec(v_aliases_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getUnary___redArg(lean_object* v_aliases_1314_, lean_object* v_aliasName_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_aliases_1314_, v_aliasName_1315_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v___x_1317_; uint8_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1317_ = ((lean_object*)(l_Lean_Parser_AliasTable_getConst___redArg___closed__0));
v___x_1318_ = 1;
v___x_1319_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1315_, v___x_1318_);
v___x_1320_ = lean_string_append(v___x_1317_, v___x_1319_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = ((lean_object*)(l_Lean_Parser_AliasTable_getConst___redArg___closed__1));
v___x_1322_ = lean_string_append(v___x_1320_, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
return v___x_1323_;
}
else
{
lean_object* v_val_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1345_; 
v_val_1324_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1326_ = v___x_1316_;
v_isShared_1327_ = v_isSharedCheck_1345_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_val_1324_);
lean_dec(v___x_1316_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1345_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
if (lean_obj_tag(v_val_1324_) == 1)
{
lean_object* v_p_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_del_object(v___x_1326_);
lean_dec(v_aliasName_1315_);
v_p_1328_ = lean_ctor_get(v_val_1324_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_val_1324_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v_val_1324_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_p_1328_);
lean_dec(v_val_1324_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_p_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
else
{
lean_object* v___x_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
lean_dec(v_val_1324_);
v___x_1336_ = ((lean_object*)(l_Lean_Parser_AliasTable_getConst___redArg___closed__0));
v___x_1337_ = 1;
v___x_1338_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1315_, v___x_1337_);
v___x_1339_ = lean_string_append(v___x_1336_, v___x_1338_);
lean_dec_ref(v___x_1338_);
v___x_1340_ = ((lean_object*)(l_Lean_Parser_AliasTable_getUnary___redArg___closed__0));
v___x_1341_ = lean_string_append(v___x_1339_, v___x_1340_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1341_);
v___x_1343_ = v___x_1326_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getUnary___redArg___boxed(lean_object* v_aliases_1346_, lean_object* v_aliasName_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Parser_AliasTable_getUnary___redArg(v_aliases_1346_, v_aliasName_1347_);
lean_dec(v_aliases_1346_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getUnary(lean_object* v_00_u03b1_1349_, lean_object* v_aliases_1350_, lean_object* v_aliasName_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_Parser_AliasTable_getUnary___redArg(v_aliases_1350_, v_aliasName_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getUnary___boxed(lean_object* v_00_u03b1_1353_, lean_object* v_aliases_1354_, lean_object* v_aliasName_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_Parser_AliasTable_getUnary(v_00_u03b1_1353_, v_aliases_1354_, v_aliasName_1355_);
lean_dec(v_aliases_1354_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getBinary___redArg(lean_object* v_aliases_1358_, lean_object* v_aliasName_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_aliases_1358_, v_aliasName_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1361_ = ((lean_object*)(l_Lean_Parser_AliasTable_getConst___redArg___closed__0));
v___x_1362_ = 1;
v___x_1363_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1359_, v___x_1362_);
v___x_1364_ = lean_string_append(v___x_1361_, v___x_1363_);
lean_dec_ref(v___x_1363_);
v___x_1365_ = ((lean_object*)(l_Lean_Parser_AliasTable_getConst___redArg___closed__1));
v___x_1366_ = lean_string_append(v___x_1364_, v___x_1365_);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
else
{
lean_object* v_val_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1389_; 
v_val_1368_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1370_ = v___x_1360_;
v_isShared_1371_ = v_isSharedCheck_1389_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_val_1368_);
lean_dec(v___x_1360_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1389_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
if (lean_obj_tag(v_val_1368_) == 2)
{
lean_object* v_p_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_del_object(v___x_1370_);
lean_dec(v_aliasName_1359_);
v_p_1372_ = lean_ctor_get(v_val_1368_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_val_1368_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v_val_1368_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_p_1372_);
lean_dec(v_val_1368_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set_tag(v___x_1374_, 1);
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_p_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_object* v___x_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_dec(v_val_1368_);
v___x_1380_ = ((lean_object*)(l_Lean_Parser_AliasTable_getConst___redArg___closed__0));
v___x_1381_ = 1;
v___x_1382_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1359_, v___x_1381_);
v___x_1383_ = lean_string_append(v___x_1380_, v___x_1382_);
lean_dec_ref(v___x_1382_);
v___x_1384_ = ((lean_object*)(l_Lean_Parser_AliasTable_getBinary___redArg___closed__0));
v___x_1385_ = lean_string_append(v___x_1383_, v___x_1384_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1385_);
v___x_1387_ = v___x_1370_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getBinary___redArg___boxed(lean_object* v_aliases_1390_, lean_object* v_aliasName_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Parser_AliasTable_getBinary___redArg(v_aliases_1390_, v_aliasName_1391_);
lean_dec(v_aliases_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getBinary(lean_object* v_00_u03b1_1393_, lean_object* v_aliases_1394_, lean_object* v_aliasName_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Parser_AliasTable_getBinary___redArg(v_aliases_1394_, v_aliasName_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasTable_getBinary___boxed(lean_object* v_00_u03b1_1397_, lean_object* v_aliases_1398_, lean_object* v_aliasName_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Parser_AliasTable_getBinary(v_00_u03b1_1397_, v_aliases_1398_, v_aliasName_1399_);
lean_dec(v_aliases_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object* v_mapRef_1401_, lean_object* v_aliasName_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_st_ref_get(v_mapRef_1401_);
v___x_1405_ = l_Lean_Parser_AliasTable_getConst___redArg(v___x_1404_, v_aliasName_1402_);
lean_dec(v___x_1404_);
v___x_1406_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object* v_mapRef_1407_, lean_object* v_aliasName_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1407_, v_aliasName_1408_);
lean_dec(v_mapRef_1407_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object* v_00_u03b1_1411_, lean_object* v_mapRef_1412_, lean_object* v_aliasName_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1412_, v_aliasName_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_mapRef_1417_, lean_object* v_aliasName_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_Parser_getConstAlias(v_00_u03b1_1416_, v_mapRef_1417_, v_aliasName_1418_);
lean_dec(v_mapRef_1417_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object* v_mapRef_1421_, lean_object* v_aliasName_1422_){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = lean_st_ref_get(v_mapRef_1421_);
v___x_1425_ = l_Lean_Parser_AliasTable_getUnary___redArg(v___x_1424_, v_aliasName_1422_);
lean_dec(v___x_1424_);
v___x_1426_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object* v_mapRef_1427_, lean_object* v_aliasName_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1427_, v_aliasName_1428_);
lean_dec(v_mapRef_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object* v_00_u03b1_1431_, lean_object* v_mapRef_1432_, lean_object* v_aliasName_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1432_, v_aliasName_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object* v_00_u03b1_1436_, lean_object* v_mapRef_1437_, lean_object* v_aliasName_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_Parser_getUnaryAlias(v_00_u03b1_1436_, v_mapRef_1437_, v_aliasName_1438_);
lean_dec(v_mapRef_1437_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object* v_mapRef_1441_, lean_object* v_aliasName_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1444_ = lean_st_ref_get(v_mapRef_1441_);
v___x_1445_ = l_Lean_Parser_AliasTable_getBinary___redArg(v___x_1444_, v_aliasName_1442_);
lean_dec(v___x_1444_);
v___x_1446_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg___boxed(lean_object* v_mapRef_1447_, lean_object* v_aliasName_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1447_, v_aliasName_1448_);
lean_dec(v_mapRef_1447_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object* v_00_u03b1_1451_, lean_object* v_mapRef_1452_, lean_object* v_aliasName_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1452_, v_aliasName_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___boxed(lean_object* v_00_u03b1_1456_, lean_object* v_mapRef_1457_, lean_object* v_aliasName_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_Parser_getBinaryAlias(v_00_u03b1_1456_, v_mapRef_1457_, v_aliasName_1458_);
lean_dec(v_mapRef_1457_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = lean_box(1);
v___x_1463_ = lean_st_mk_ref(v___x_1462_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = lean_box(1);
v___x_1469_ = lean_st_mk_ref(v___x_1468_);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = lean_box(1);
v___x_1475_ = lean_st_mk_ref(v___x_1474_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(lean_object* v_t_1479_, lean_object* v_k_1480_, lean_object* v_fallback_1481_){
_start:
{
if (lean_obj_tag(v_t_1479_) == 0)
{
lean_object* v_k_1482_; lean_object* v_v_1483_; lean_object* v_l_1484_; lean_object* v_r_1485_; uint8_t v___x_1486_; 
v_k_1482_ = lean_ctor_get(v_t_1479_, 1);
v_v_1483_ = lean_ctor_get(v_t_1479_, 2);
v_l_1484_ = lean_ctor_get(v_t_1479_, 3);
v_r_1485_ = lean_ctor_get(v_t_1479_, 4);
v___x_1486_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1480_, v_k_1482_);
switch(v___x_1486_)
{
case 0:
{
v_t_1479_ = v_l_1484_;
goto _start;
}
case 1:
{
lean_inc(v_v_1483_);
return v_v_1483_;
}
default: 
{
v_t_1479_ = v_r_1485_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_1481_);
return v_fallback_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg___boxed(lean_object* v_t_1489_, lean_object* v_k_1490_, lean_object* v_fallback_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1489_, v_k_1490_, v_fallback_1491_);
lean_dec(v_fallback_1491_);
lean_dec(v_k_1490_);
lean_dec(v_t_1489_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo(lean_object* v_aliasName_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1501_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1502_ = lean_st_ref_get(v___x_1501_);
v___x_1503_ = ((lean_object*)(l_Lean_Parser_getParserAliasInfo___closed__1));
v___x_1504_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v___x_1502_, v_aliasName_1499_, v___x_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo___boxed(lean_object* v_aliasName_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_Parser_getParserAliasInfo(v_aliasName_1506_);
lean_dec(v_aliasName_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(lean_object* v_00_u03b4_1509_, lean_object* v_t_1510_, lean_object* v_k_1511_, lean_object* v_fallback_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1510_, v_k_1511_, v_fallback_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___boxed(lean_object* v_00_u03b4_1514_, lean_object* v_t_1515_, lean_object* v_k_1516_, lean_object* v_fallback_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(v_00_u03b4_1514_, v_t_1515_, v_k_1516_, v_fallback_1517_);
lean_dec(v_fallback_1517_);
lean_dec(v_k_1516_);
lean_dec(v_t_1515_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object* v_aliasName_1519_, lean_object* v_declName_1520_, lean_object* v_p_1521_, lean_object* v_kind_x3f_1522_, lean_object* v_info_1523_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = l_Lean_Parser_parserAliasesRef;
lean_inc(v_aliasName_1519_);
v___x_1542_ = l_Lean_Parser_registerAliasCore___redArg(v___x_1541_, v_aliasName_1519_, v_p_1521_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_dec_ref_known(v___x_1542_, 1);
if (lean_obj_tag(v_kind_x3f_1522_) == 1)
{
lean_object* v_val_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_val_1543_ = lean_ctor_get(v_kind_x3f_1522_, 0);
lean_inc(v_val_1543_);
lean_dec_ref_known(v_kind_x3f_1522_, 1);
v___x_1544_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1545_ = lean_st_ref_take(v___x_1544_);
lean_inc(v_aliasName_1519_);
v___x_1546_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1519_, v_val_1543_, v___x_1545_);
v___x_1547_ = lean_st_ref_put(v___x_1544_, v___x_1546_);
goto v___jp_1525_;
}
else
{
lean_dec(v_kind_x3f_1522_);
goto v___jp_1525_;
}
}
else
{
lean_dec_ref(v_info_1523_);
lean_dec(v_kind_x3f_1522_);
lean_dec(v_declName_1520_);
lean_dec(v_aliasName_1519_);
return v___x_1542_;
}
v___jp_1525_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v_stackSz_x3f_1528_; uint8_t v_autoGroupArgs_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1539_; 
v___x_1526_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1527_ = lean_st_ref_take(v___x_1526_);
v_stackSz_x3f_1528_ = lean_ctor_get(v_info_1523_, 1);
v_autoGroupArgs_1529_ = lean_ctor_get_uint8(v_info_1523_, sizeof(void*)*2);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_info_1523_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v_info_1523_, 0);
lean_dec(v_unused_1540_);
v___x_1531_ = v_info_1523_;
v_isShared_1532_ = v_isSharedCheck_1539_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_stackSz_x3f_1528_);
lean_dec(v_info_1523_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1539_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v_declName_1520_);
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_declName_1520_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_stackSz_x3f_1528_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*2, v_autoGroupArgs_1529_);
v___x_1534_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1519_, v___x_1534_, v___x_1527_);
v___x_1536_ = lean_st_ref_put(v___x_1526_, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias___boxed(lean_object* v_aliasName_1548_, lean_object* v_declName_1549_, lean_object* v_p_1550_, lean_object* v_kind_x3f_1551_, lean_object* v_info_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Parser_registerAlias(v_aliasName_1548_, v_declName_1549_, v_p_1550_, v_kind_x3f_1551_, v_info_1552_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue___lam__0(lean_object* v_p_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_p_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0(lean_object* v_p_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1560_, 0, v_p_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0(lean_object* v_p_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1564_, 0, v_p_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object* v_aliasName_1567_){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1585_; 
v___x_1569_ = l_Lean_Parser_parserAliasesRef;
v___x_1570_ = l_Lean_Parser_getAlias___redArg(v___x_1569_, v_aliasName_1567_);
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1585_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1585_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
if (lean_obj_tag(v_a_1571_) == 1)
{
uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
lean_dec_ref_known(v_a_1571_, 1);
v___x_1575_ = 1;
v___x_1576_ = lean_box(v___x_1575_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1576_);
v___x_1578_ = v___x_1573_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
else
{
uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
lean_dec(v_a_1571_);
v___x_1580_ = 0;
v___x_1581_ = lean_box(v___x_1580_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1581_);
v___x_1583_ = v___x_1573_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object* v_aliasName_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_Parser_isParserAlias(v_aliasName_1586_);
lean_dec(v_aliasName_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object* v_aliasName_1589_){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1591_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1592_ = lean_st_ref_get(v___x_1591_);
v___x_1593_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1592_, v_aliasName_1589_);
lean_dec(v___x_1592_);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f___boxed(lean_object* v_aliasName_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v_aliasName_1595_);
lean_dec(v_aliasName_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object* v_aliasName_1598_){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = l_Lean_Parser_parserAliasesRef;
v___x_1601_ = lean_box(0);
v___x_1602_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1600_, v_aliasName_1598_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v___x_1602_, 0);
lean_dec(v_unused_1610_);
v___x_1604_ = v___x_1602_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_dec(v___x_1602_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1601_);
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1601_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1602_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1602_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias___boxed(lean_object* v_aliasName_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Parser_ensureUnaryParserAlias(v_aliasName_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object* v_aliasName_1622_){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = l_Lean_Parser_parserAliasesRef;
v___x_1625_ = lean_box(0);
v___x_1626_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1624_, v_aliasName_1622_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; 
v_unused_1634_ = lean_ctor_get(v___x_1626_, 0);
lean_dec(v_unused_1634_);
v___x_1628_ = v___x_1626_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_dec(v___x_1626_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1625_);
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1625_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
v_a_1635_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1626_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1626_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias___boxed(lean_object* v_aliasName_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_Parser_ensureBinaryParserAlias(v_aliasName_1643_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object* v_aliasName_1646_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = l_Lean_Parser_parserAliasesRef;
v___x_1649_ = lean_box(0);
v___x_1650_ = l_Lean_Parser_getConstAlias___redArg(v___x_1648_, v_aliasName_1646_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v___x_1650_, 0);
lean_dec(v_unused_1658_);
v___x_1652_ = v___x_1650_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_dec(v___x_1650_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1649_);
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1649_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
v_a_1659_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1650_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1650_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias___boxed(lean_object* v_aliasName_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_Parser_ensureConstantParserAlias(v_aliasName_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* v_env_1678_, lean_object* v_opts_1679_, lean_object* v_constName_1680_, lean_object* v_compileParserDescr_1681_){
_start:
{
uint8_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = 0;
lean_inc(v_constName_1680_);
lean_inc_ref(v_env_1678_);
v___x_1691_ = l_Lean_Environment_find_x3f(v_env_1678_, v_constName_1680_, v___x_1690_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v___x_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_dec_ref(v_compileParserDescr_1681_);
lean_dec_ref(v_env_1678_);
v___x_1692_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_1693_ = 1;
v___x_1694_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1680_, v___x_1693_);
v___x_1695_ = lean_string_append(v___x_1692_, v___x_1694_);
lean_dec_ref(v___x_1694_);
v___x_1696_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_1697_ = lean_string_append(v___x_1695_, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
return v___x_1698_;
}
else
{
lean_object* v_val_1699_; lean_object* v___x_1700_; 
v_val_1699_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_val_1699_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1700_ = l_Lean_ConstantInfo_type(v_val_1699_);
lean_dec(v_val_1699_);
if (lean_obj_tag(v___x_1700_) == 4)
{
lean_object* v_declName_1701_; 
v_declName_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_declName_1701_);
lean_dec_ref_known(v___x_1700_, 2);
if (lean_obj_tag(v_declName_1701_) == 1)
{
lean_object* v_pre_1702_; 
v_pre_1702_ = lean_ctor_get(v_declName_1701_, 0);
lean_inc(v_pre_1702_);
if (lean_obj_tag(v_pre_1702_) == 1)
{
lean_object* v_pre_1703_; 
v_pre_1703_ = lean_ctor_get(v_pre_1702_, 0);
switch(lean_obj_tag(v_pre_1703_))
{
case 1:
{
lean_object* v_pre_1704_; 
lean_inc_ref(v_pre_1703_);
lean_dec_ref(v_compileParserDescr_1681_);
v_pre_1704_ = lean_ctor_get(v_pre_1703_, 0);
if (lean_obj_tag(v_pre_1704_) == 0)
{
lean_object* v_str_1705_; lean_object* v_str_1706_; lean_object* v_str_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_str_1705_ = lean_ctor_get(v_declName_1701_, 1);
lean_inc_ref(v_str_1705_);
lean_dec_ref_known(v_declName_1701_, 2);
v_str_1706_ = lean_ctor_get(v_pre_1702_, 1);
lean_inc_ref(v_str_1706_);
lean_dec_ref_known(v_pre_1702_, 2);
v_str_1707_ = lean_ctor_get(v_pre_1703_, 1);
lean_inc_ref(v_str_1707_);
lean_dec_ref_known(v_pre_1703_, 2);
v___x_1708_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1709_ = lean_string_dec_eq(v_str_1707_, v___x_1708_);
lean_dec_ref(v_str_1707_);
if (v___x_1709_ == 0)
{
lean_dec_ref(v_str_1706_);
lean_dec_ref(v_str_1705_);
lean_dec_ref(v_env_1678_);
goto v___jp_1682_;
}
else
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_1711_ = lean_string_dec_eq(v_str_1706_, v___x_1710_);
lean_dec_ref(v_str_1706_);
if (v___x_1711_ == 0)
{
lean_dec_ref(v_str_1705_);
lean_dec_ref(v_env_1678_);
goto v___jp_1682_;
}
else
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_1713_ = lean_string_dec_eq(v_str_1705_, v___x_1712_);
if (v___x_1713_ == 0)
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_string_dec_eq(v_str_1705_, v___x_1710_);
lean_dec_ref(v_str_1705_);
if (v___x_1714_ == 0)
{
lean_dec_ref(v_env_1678_);
goto v___jp_1682_;
}
else
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_Environment_evalConst___redArg(v_env_1678_, v_opts_1679_, v_constName_1680_, v___x_1714_);
lean_dec(v_constName_1680_);
lean_dec_ref(v_env_1678_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
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
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1733_; 
v_a_1724_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1726_ = v___x_1715_;
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1715_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1728_ = lean_box(v___x_1714_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v_a_1724_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1729_);
v___x_1731_ = v___x_1726_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
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
lean_object* v___x_1734_; 
lean_dec_ref(v_str_1705_);
v___x_1734_ = l_Lean_Environment_evalConst___redArg(v_env_1678_, v_opts_1679_, v_constName_1680_, v___x_1713_);
lean_dec(v_constName_1680_);
lean_dec_ref(v_env_1678_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1752_; 
v_a_1743_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1745_ = v___x_1734_;
v_isShared_1746_ = v_isSharedCheck_1752_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1734_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1752_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1747_ = lean_box(v___x_1690_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v_a_1743_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1748_);
v___x_1750_ = v___x_1745_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1703_, 2);
lean_dec_ref_known(v_pre_1702_, 2);
lean_dec_ref_known(v_declName_1701_, 2);
lean_dec_ref(v_env_1678_);
goto v___jp_1682_;
}
}
case 0:
{
lean_object* v_str_1753_; lean_object* v_str_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_str_1753_ = lean_ctor_get(v_declName_1701_, 1);
lean_inc_ref(v_str_1753_);
lean_dec_ref_known(v_declName_1701_, 2);
v_str_1754_ = lean_ctor_get(v_pre_1702_, 1);
lean_inc_ref(v_str_1754_);
lean_dec_ref_known(v_pre_1702_, 2);
v___x_1755_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1756_ = lean_string_dec_eq(v_str_1754_, v___x_1755_);
lean_dec_ref(v_str_1754_);
if (v___x_1756_ == 0)
{
lean_dec_ref(v_str_1753_);
lean_dec_ref(v_compileParserDescr_1681_);
lean_dec_ref(v_env_1678_);
goto v___jp_1682_;
}
else
{
lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_1758_ = lean_string_dec_eq(v_str_1753_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_1760_ = lean_string_dec_eq(v_str_1753_, v___x_1759_);
lean_dec_ref(v_str_1753_);
if (v___x_1760_ == 0)
{
lean_dec_ref(v_compileParserDescr_1681_);
lean_dec_ref(v_env_1678_);
goto v___jp_1682_;
}
else
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_Environment_evalConst___redArg(v_env_1678_, v_opts_1679_, v_constName_1680_, v___x_1760_);
lean_dec(v_constName_1680_);
lean_dec_ref(v_env_1678_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref(v_compileParserDescr_1681_);
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1771_; 
v_a_1770_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1771_ = lean_apply_1(v_compileParserDescr_1681_, v_a_1770_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1789_; 
v_a_1780_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1782_ = v___x_1771_;
v_isShared_1783_ = v_isSharedCheck_1789_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1771_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1789_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1784_ = lean_box(v___x_1758_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v_a_1780_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1785_);
v___x_1787_ = v___x_1782_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v___x_1790_; 
lean_dec_ref(v_str_1753_);
v___x_1790_ = l_Lean_Environment_evalConst___redArg(v_env_1678_, v_opts_1679_, v_constName_1680_, v___x_1758_);
lean_dec(v_constName_1680_);
lean_dec_ref(v_env_1678_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec_ref(v_compileParserDescr_1681_);
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1800_; 
v_a_1799_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1790_, 1);
v___x_1800_ = lean_apply_1(v_compileParserDescr_1681_, v_a_1799_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
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
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1818_; 
v_a_1809_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1811_ = v___x_1800_;
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1800_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1813_ = lean_box(v___x_1758_);
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
lean_ctor_set(v___x_1814_, 1, v_a_1809_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1814_);
v___x_1816_ = v___x_1811_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_pre_1702_, 2);
lean_dec_ref_known(v_declName_1701_, 2);
lean_dec_ref(v_compileParserDescr_1681_);
lean_dec_ref(v_env_1678_);
goto v___jp_1682_;
}
}
}
else
{
lean_dec(v_pre_1702_);
lean_dec_ref_known(v_declName_1701_, 2);
lean_dec_ref(v_compileParserDescr_1681_);
lean_dec_ref(v_env_1678_);
goto v___jp_1682_;
}
}
else
{
lean_dec(v_declName_1701_);
lean_dec_ref(v_compileParserDescr_1681_);
lean_dec_ref(v_env_1678_);
goto v___jp_1682_;
}
}
else
{
lean_dec_ref(v___x_1700_);
lean_dec_ref(v_compileParserDescr_1681_);
lean_dec_ref(v_env_1678_);
goto v___jp_1682_;
}
}
v___jp_1682_:
{
lean_object* v___x_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1683_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__0));
v___x_1684_ = 1;
v___x_1685_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1680_, v___x_1684_);
v___x_1686_ = lean_string_append(v___x_1683_, v___x_1685_);
lean_dec_ref(v___x_1685_);
v___x_1687_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1));
v___x_1688_ = lean_string_append(v___x_1686_, v___x_1687_);
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
return v___x_1689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object* v_env_1819_, lean_object* v_opts_1820_, lean_object* v_constName_1821_, lean_object* v_compileParserDescr_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_env_1819_, v_opts_1820_, v_constName_1821_, v_compileParserDescr_1822_);
lean_dec_ref(v_opts_1820_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(lean_object* v_env_1824_, lean_object* v_opts_1825_, lean_object* v_aliases_1826_, lean_object* v_categories_1827_, lean_object* v_a_1828_){
_start:
{
switch(lean_obj_tag(v_a_1828_))
{
case 0:
{
lean_object* v_name_1829_; lean_object* v___x_1830_; 
lean_dec_ref(v_categories_1827_);
lean_dec_ref(v_opts_1825_);
lean_dec_ref(v_env_1824_);
v_name_1829_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_name_1829_);
lean_dec_ref_known(v_a_1828_, 1);
v___x_1830_ = l_Lean_Parser_AliasTable_getConst___redArg(v_aliases_1826_, v_name_1829_);
lean_dec(v_aliases_1826_);
return v___x_1830_;
}
case 1:
{
lean_object* v_name_1831_; lean_object* v_p_1832_; lean_object* v___x_1833_; 
v_name_1831_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_name_1831_);
v_p_1832_ = lean_ctor_get(v_a_1828_, 1);
lean_inc_ref(v_p_1832_);
lean_dec_ref_known(v_a_1828_, 2);
v___x_1833_ = l_Lean_Parser_AliasTable_getUnary___redArg(v_aliases_1826_, v_name_1831_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v_p_1832_);
lean_dec_ref(v_categories_1827_);
lean_dec(v_aliases_1826_);
lean_dec_ref(v_opts_1825_);
lean_dec_ref(v_env_1824_);
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
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
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1842_; lean_object* v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1843_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_1824_, v_opts_1825_, v_aliases_1826_, v_categories_1827_, v_p_1832_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_dec(v_a_1842_);
return v___x_1843_;
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1852_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = lean_apply_1(v_a_1842_, v_a_1844_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1848_);
v___x_1850_ = v___x_1846_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
case 2:
{
lean_object* v_name_1853_; lean_object* v_p_u2081_1854_; lean_object* v_p_u2082_1855_; lean_object* v___x_1856_; 
v_name_1853_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_name_1853_);
v_p_u2081_1854_ = lean_ctor_get(v_a_1828_, 1);
lean_inc_ref(v_p_u2081_1854_);
v_p_u2082_1855_ = lean_ctor_get(v_a_1828_, 2);
lean_inc_ref(v_p_u2082_1855_);
lean_dec_ref_known(v_a_1828_, 3);
v___x_1856_ = l_Lean_Parser_AliasTable_getBinary___redArg(v_aliases_1826_, v_name_1853_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v_p_u2082_1855_);
lean_dec_ref(v_p_u2081_1854_);
lean_dec_ref(v_categories_1827_);
lean_dec(v_aliases_1826_);
lean_dec_ref(v_opts_1825_);
lean_dec_ref(v_env_1824_);
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1866_; 
v_a_1865_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1856_, 1);
lean_inc_ref(v_categories_1827_);
lean_inc(v_aliases_1826_);
lean_inc_ref(v_opts_1825_);
lean_inc_ref(v_env_1824_);
v___x_1866_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_1824_, v_opts_1825_, v_aliases_1826_, v_categories_1827_, v_p_u2081_1854_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_dec(v_a_1865_);
lean_dec_ref(v_p_u2082_1855_);
lean_dec_ref(v_categories_1827_);
lean_dec(v_aliases_1826_);
lean_dec_ref(v_opts_1825_);
lean_dec_ref(v_env_1824_);
return v___x_1866_;
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1868_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1866_, 1);
v___x_1868_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_1824_, v_opts_1825_, v_aliases_1826_, v_categories_1827_, v_p_u2082_1855_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_dec(v_a_1867_);
lean_dec(v_a_1865_);
return v___x_1868_;
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1877_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = lean_apply_2(v_a_1865_, v_a_1867_, v_a_1869_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1873_);
v___x_1875_ = v___x_1871_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
case 3:
{
lean_object* v_kind_1878_; lean_object* v_prec_1879_; lean_object* v_p_1880_; lean_object* v___x_1881_; 
v_kind_1878_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_kind_1878_);
v_prec_1879_ = lean_ctor_get(v_a_1828_, 1);
lean_inc(v_prec_1879_);
v_p_1880_ = lean_ctor_get(v_a_1828_, 2);
lean_inc_ref(v_p_1880_);
lean_dec_ref_known(v_a_1828_, 3);
v___x_1881_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_1824_, v_opts_1825_, v_aliases_1826_, v_categories_1827_, v_p_1880_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_dec(v_prec_1879_);
lean_dec(v_kind_1878_);
return v___x_1881_;
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1890_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1890_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1890_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1886_ = l_Lean_Parser_leadingNode(v_kind_1878_, v_prec_1879_, v_a_1882_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1886_);
v___x_1888_ = v___x_1884_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
case 4:
{
lean_object* v_kind_1891_; lean_object* v_prec_1892_; lean_object* v_lhsPrec_1893_; lean_object* v_p_1894_; lean_object* v___x_1895_; 
v_kind_1891_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_kind_1891_);
v_prec_1892_ = lean_ctor_get(v_a_1828_, 1);
lean_inc(v_prec_1892_);
v_lhsPrec_1893_ = lean_ctor_get(v_a_1828_, 2);
lean_inc(v_lhsPrec_1893_);
v_p_1894_ = lean_ctor_get(v_a_1828_, 3);
lean_inc_ref(v_p_1894_);
lean_dec_ref_known(v_a_1828_, 4);
v___x_1895_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_1824_, v_opts_1825_, v_aliases_1826_, v_categories_1827_, v_p_1894_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_dec(v_lhsPrec_1893_);
lean_dec(v_prec_1892_);
lean_dec(v_kind_1891_);
return v___x_1895_;
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1904_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1904_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1904_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v___x_1902_; 
v___x_1900_ = l_Lean_Parser_trailingNode(v_kind_1891_, v_prec_1892_, v_lhsPrec_1893_, v_a_1896_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1900_);
v___x_1902_ = v___x_1898_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
case 5:
{
lean_object* v_val_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1913_; 
lean_dec_ref(v_categories_1827_);
lean_dec(v_aliases_1826_);
lean_dec_ref(v_opts_1825_);
lean_dec_ref(v_env_1824_);
v_val_1905_ = lean_ctor_get(v_a_1828_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_a_1828_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1907_ = v_a_1828_;
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_val_1905_);
lean_dec(v_a_1828_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = l_Lean_Parser_symbol(v_val_1905_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 1);
lean_ctor_set(v___x_1907_, 0, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
case 6:
{
lean_object* v_val_1914_; uint8_t v_includeIdent_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec_ref(v_categories_1827_);
lean_dec(v_aliases_1826_);
lean_dec_ref(v_opts_1825_);
lean_dec_ref(v_env_1824_);
v_val_1914_ = lean_ctor_get(v_a_1828_, 0);
lean_inc_ref(v_val_1914_);
v_includeIdent_1915_ = lean_ctor_get_uint8(v_a_1828_, sizeof(void*)*1);
lean_dec_ref_known(v_a_1828_, 1);
v___x_1916_ = l_Lean_Parser_nonReservedSymbol(v_val_1914_, v_includeIdent_1915_);
v___x_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
return v___x_1917_;
}
case 7:
{
lean_object* v_catName_1918_; lean_object* v_rbp_1919_; lean_object* v___x_1920_; 
lean_dec(v_aliases_1826_);
lean_dec_ref(v_opts_1825_);
lean_dec_ref(v_env_1824_);
v_catName_1918_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_catName_1918_);
v_rbp_1919_ = lean_ctor_get(v_a_1828_, 1);
lean_inc(v_rbp_1919_);
lean_dec_ref_known(v_a_1828_, 2);
v___x_1920_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_1827_, v_catName_1918_);
lean_dec_ref(v_categories_1827_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v___x_1921_; 
lean_dec(v_rbp_1919_);
v___x_1921_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_1918_);
return v___x_1921_;
}
else
{
lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1929_; 
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; 
v_unused_1930_ = lean_ctor_get(v___x_1920_, 0);
lean_dec(v_unused_1930_);
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
else
{
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = l_Lean_Parser_categoryParser(v_catName_1918_, v_rbp_1919_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
case 8:
{
lean_object* v_declName_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_declName_1931_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_declName_1931_);
lean_dec_ref_known(v_a_1828_, 1);
lean_inc_ref(v_opts_1825_);
lean_inc_ref(v_env_1824_);
v___x_1932_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit), 5, 4);
lean_closure_set(v___x_1932_, 0, v_env_1824_);
lean_closure_set(v___x_1932_, 1, v_opts_1825_);
lean_closure_set(v___x_1932_, 2, v_aliases_1826_);
lean_closure_set(v___x_1932_, 3, v_categories_1827_);
v___x_1933_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_env_1824_, v_opts_1825_, v_declName_1931_, v___x_1932_);
lean_dec_ref(v_opts_1825_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1950_; 
v_a_1942_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1944_ = v___x_1933_;
v_isShared_1945_ = v_isSharedCheck_1950_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1933_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1950_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v_snd_1946_; lean_object* v___x_1948_; 
v_snd_1946_ = lean_ctor_get(v_a_1942_, 1);
lean_inc(v_snd_1946_);
lean_dec(v_a_1942_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v_snd_1946_);
v___x_1948_ = v___x_1944_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_snd_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
case 9:
{
lean_object* v_name_1951_; lean_object* v_kind_1952_; lean_object* v_p_1953_; lean_object* v___x_1954_; 
v_name_1951_ = lean_ctor_get(v_a_1828_, 0);
lean_inc_ref(v_name_1951_);
v_kind_1952_ = lean_ctor_get(v_a_1828_, 1);
lean_inc(v_kind_1952_);
v_p_1953_ = lean_ctor_get(v_a_1828_, 2);
lean_inc_ref(v_p_1953_);
lean_dec_ref_known(v_a_1828_, 3);
v___x_1954_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_1824_, v_opts_1825_, v_aliases_1826_, v_categories_1827_, v_p_1953_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_dec(v_kind_1952_);
lean_dec_ref(v_name_1951_);
return v___x_1954_;
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1965_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1959_ = 1;
lean_inc(v_kind_1952_);
v___x_1960_ = l_Lean_Parser_nodeWithAntiquot(v_name_1951_, v_kind_1952_, v_a_1955_, v___x_1959_);
v___x_1961_ = l_Lean_Parser_withCache(v_kind_1952_, v___x_1960_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1961_);
v___x_1963_ = v___x_1957_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
case 10:
{
lean_object* v_p_1966_; lean_object* v_sep_1967_; lean_object* v_psep_1968_; uint8_t v_allowTrailingSep_1969_; lean_object* v___x_1970_; 
v_p_1966_ = lean_ctor_get(v_a_1828_, 0);
lean_inc_ref(v_p_1966_);
v_sep_1967_ = lean_ctor_get(v_a_1828_, 1);
lean_inc_ref(v_sep_1967_);
v_psep_1968_ = lean_ctor_get(v_a_1828_, 2);
lean_inc_ref(v_psep_1968_);
v_allowTrailingSep_1969_ = lean_ctor_get_uint8(v_a_1828_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1828_, 3);
lean_inc_ref(v_categories_1827_);
lean_inc(v_aliases_1826_);
lean_inc_ref(v_opts_1825_);
lean_inc_ref(v_env_1824_);
v___x_1970_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_1824_, v_opts_1825_, v_aliases_1826_, v_categories_1827_, v_p_1966_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_dec_ref(v_psep_1968_);
lean_dec_ref(v_sep_1967_);
lean_dec_ref(v_categories_1827_);
lean_dec(v_aliases_1826_);
lean_dec_ref(v_opts_1825_);
lean_dec_ref(v_env_1824_);
return v___x_1970_;
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1972_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
v___x_1972_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_1824_, v_opts_1825_, v_aliases_1826_, v_categories_1827_, v_psep_1968_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_dec(v_a_1971_);
lean_dec_ref(v_sep_1967_);
return v___x_1972_;
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1981_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1981_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1981_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = l_Lean_Parser_sepBy(v_a_1971_, v_sep_1967_, v_a_1973_, v_allowTrailingSep_1969_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1977_);
v___x_1979_ = v___x_1975_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
case 11:
{
lean_object* v_p_1982_; lean_object* v_sep_1983_; lean_object* v_psep_1984_; uint8_t v_allowTrailingSep_1985_; lean_object* v___x_1986_; 
v_p_1982_ = lean_ctor_get(v_a_1828_, 0);
lean_inc_ref(v_p_1982_);
v_sep_1983_ = lean_ctor_get(v_a_1828_, 1);
lean_inc_ref(v_sep_1983_);
v_psep_1984_ = lean_ctor_get(v_a_1828_, 2);
lean_inc_ref(v_psep_1984_);
v_allowTrailingSep_1985_ = lean_ctor_get_uint8(v_a_1828_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1828_, 3);
lean_inc_ref(v_categories_1827_);
lean_inc(v_aliases_1826_);
lean_inc_ref(v_opts_1825_);
lean_inc_ref(v_env_1824_);
v___x_1986_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_1824_, v_opts_1825_, v_aliases_1826_, v_categories_1827_, v_p_1982_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_dec_ref(v_psep_1984_);
lean_dec_ref(v_sep_1983_);
lean_dec_ref(v_categories_1827_);
lean_dec(v_aliases_1826_);
lean_dec_ref(v_opts_1825_);
lean_dec_ref(v_env_1824_);
return v___x_1986_;
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1988_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v___x_1988_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_1824_, v_opts_1825_, v_aliases_1826_, v_categories_1827_, v_psep_1984_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_dec(v_a_1987_);
lean_dec_ref(v_sep_1983_);
return v___x_1988_;
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1997_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_1997_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1997_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1993_ = l_Lean_Parser_sepBy1(v_a_1987_, v_sep_1983_, v_a_1989_, v_allowTrailingSep_1985_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1993_);
v___x_1995_ = v___x_1991_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
default: 
{
lean_object* v_val_1998_; lean_object* v_asciiVal_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec_ref(v_categories_1827_);
lean_dec(v_aliases_1826_);
lean_dec_ref(v_opts_1825_);
lean_dec_ref(v_env_1824_);
v_val_1998_ = lean_ctor_get(v_a_1828_, 0);
lean_inc_ref(v_val_1998_);
v_asciiVal_1999_ = lean_ctor_get(v_a_1828_, 1);
lean_inc_ref(v_asciiVal_1999_);
lean_dec_ref_known(v_a_1828_, 2);
v___x_2000_ = l_Lean_Parser_unicodeSymbol___redArg(v_val_1998_, v_asciiVal_1999_);
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
return v___x_2001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescrCore(lean_object* v_env_2002_, lean_object* v_opts_2003_, lean_object* v_aliases_2004_, lean_object* v_categories_2005_, lean_object* v_d_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_2002_, v_opts_2003_, v_aliases_2004_, v_categories_2005_, v_d_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object* v_categories_2008_, lean_object* v_d_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_env_2012_; lean_object* v_opts_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_env_2012_ = lean_ctor_get(v_a_2010_, 0);
v_opts_2013_ = lean_ctor_get(v_a_2010_, 1);
v___x_2014_ = l_Lean_Parser_parserAliasesRef;
v___x_2015_ = lean_st_ref_get(v___x_2014_);
lean_inc_ref(v_opts_2013_);
lean_inc_ref(v_env_2012_);
v___x_2016_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_2012_, v_opts_2013_, v___x_2015_, v_categories_2008_, v_d_2009_);
v___x_2017_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object* v_categories_2018_, lean_object* v_d_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_Parser_compileParserDescr(v_categories_2018_, v_d_2019_, v_a_2020_);
lean_dec_ref(v_a_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantCore___lam__0(lean_object* v_env_2023_, lean_object* v_opts_2024_, lean_object* v_aliases_2025_, lean_object* v_categories_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescrCore_visit(v_env_2023_, v_opts_2024_, v_aliases_2025_, v_categories_2026_, v___y_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantCore(lean_object* v_env_2029_, lean_object* v_opts_2030_, lean_object* v_aliases_2031_, lean_object* v_categories_2032_, lean_object* v_constName_2033_){
_start:
{
lean_object* v___f_2034_; lean_object* v___x_2035_; 
lean_inc_ref(v_opts_2030_);
lean_inc_ref(v_env_2029_);
v___f_2034_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserOfConstantCore___lam__0), 5, 4);
lean_closure_set(v___f_2034_, 0, v_env_2029_);
lean_closure_set(v___f_2034_, 1, v_opts_2030_);
lean_closure_set(v___f_2034_, 2, v_aliases_2031_);
lean_closure_set(v___f_2034_, 3, v_categories_2032_);
v___x_2035_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_env_2029_, v_opts_2030_, v_constName_2033_, v___f_2034_);
lean_dec_ref(v_opts_2030_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* v_categories_2036_, lean_object* v_constName_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v_env_2040_; lean_object* v_opts_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_env_2040_ = lean_ctor_get(v_a_2038_, 0);
v_opts_2041_ = lean_ctor_get(v_a_2038_, 1);
v___x_2042_ = l_Lean_Parser_parserAliasesRef;
v___x_2043_ = lean_st_ref_get(v___x_2042_);
lean_inc_ref(v_opts_2041_);
lean_inc_ref(v_env_2040_);
v___x_2044_ = l_Lean_Parser_mkParserOfConstantCore(v_env_2040_, v_opts_2041_, v___x_2043_, v_categories_2036_, v_constName_2037_);
v___x_2045_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___boxed(lean_object* v_categories_2046_, lean_object* v_constName_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_Parser_mkParserOfConstant(v_categories_2046_, v_constName_2047_, v_a_2048_);
lean_dec_ref(v_a_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = lean_box(0);
v___x_2053_ = lean_st_mk_ref(v___x_2052_);
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object* v_a_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object* v_hook_2057_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2059_ = l_Lean_Parser_parserAttributeHooks;
v___x_2060_ = lean_st_ref_take(v___x_2059_);
v___x_2061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2061_, 0, v_hook_2057_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = lean_st_ref_put(v___x_2059_, v___x_2061_);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook___boxed(lean_object* v_hook_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Parser_registerParserAttributeHook(v_hook_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(lean_object* v_catName_2067_, lean_object* v_declName_2068_, uint8_t v_builtin_2069_, lean_object* v_as_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
if (lean_obj_tag(v_as_2070_) == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec(v_declName_2068_);
lean_dec(v_catName_2067_);
v___x_2074_ = lean_box(0);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
return v___x_2075_;
}
else
{
lean_object* v_head_2076_; lean_object* v_tail_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_head_2076_ = lean_ctor_get(v_as_2070_, 0);
lean_inc(v_head_2076_);
v_tail_2077_ = lean_ctor_get(v_as_2070_, 1);
lean_inc(v_tail_2077_);
lean_dec_ref_known(v_as_2070_, 2);
v___x_2078_ = lean_box(v_builtin_2069_);
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
lean_inc(v_declName_2068_);
lean_inc(v_catName_2067_);
v___x_2079_ = lean_apply_6(v_head_2076_, v_catName_2067_, v_declName_2068_, v___x_2078_, v___y_2071_, v___y_2072_, lean_box(0));
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_dec_ref_known(v___x_2079_, 1);
v_as_2070_ = v_tail_2077_;
goto _start;
}
else
{
lean_dec(v_tail_2077_);
lean_dec(v_declName_2068_);
lean_dec(v_catName_2067_);
return v___x_2079_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0___boxed(lean_object* v_catName_2081_, lean_object* v_declName_2082_, lean_object* v_builtin_2083_, lean_object* v_as_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
uint8_t v_builtin_boxed_2088_; lean_object* v_res_2089_; 
v_builtin_boxed_2088_ = lean_unbox(v_builtin_2083_);
v_res_2089_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2081_, v_declName_2082_, v_builtin_boxed_2088_, v_as_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object* v_catName_2090_, lean_object* v_declName_2091_, uint8_t v_builtin_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = l_Lean_Parser_parserAttributeHooks;
v___x_2097_ = lean_st_ref_get(v___x_2096_);
v___x_2098_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2090_, v_declName_2091_, v_builtin_2092_, v___x_2097_, v_a_2093_, v_a_2094_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object* v_catName_2099_, lean_object* v_declName_2100_, lean_object* v_builtin_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
uint8_t v_builtin_boxed_2105_; lean_object* v_res_2106_; 
v_builtin_boxed_2105_ = lean_unbox(v_builtin_2101_);
v_res_2106_ = l_Lean_Parser_runParserAttributeHooks(v_catName_2099_, v_declName_2100_, v_builtin_boxed_2105_, v_a_2102_, v_a_2103_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2107_, lean_object* v_decl_2108_, lean_object* v_stx_2109_, uint8_t v_x_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2109_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2114_) == 0)
{
uint8_t v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref_known(v___x_2114_, 1);
v___x_2115_ = 1;
v___x_2116_ = l_Lean_Parser_runParserAttributeHooks(v___x_2107_, v_decl_2108_, v___x_2115_, v___y_2111_, v___y_2112_);
return v___x_2116_;
}
else
{
lean_dec(v_decl_2108_);
lean_dec(v___x_2107_);
return v___x_2114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2117_, lean_object* v_decl_2118_, lean_object* v_stx_2119_, lean_object* v_x_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
uint8_t v_x_1099__boxed_2124_; lean_object* v_res_2125_; 
v_x_1099__boxed_2124_ = lean_unbox(v_x_2120_);
v_res_2125_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2117_, v_decl_2118_, v_stx_2119_, v_x_1099__boxed_2124_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
return v_res_2125_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2129_ = lean_unsigned_to_nat(0u);
v___x_2130_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
lean_ctor_set(v___x_2130_, 2, v___x_2129_);
lean_ctor_set(v___x_2130_, 3, v___x_2129_);
lean_ctor_set(v___x_2130_, 4, v___x_2128_);
lean_ctor_set(v___x_2130_, 5, v___x_2128_);
lean_ctor_set(v___x_2130_, 6, v___x_2128_);
lean_ctor_set(v___x_2130_, 7, v___x_2128_);
lean_ctor_set(v___x_2130_, 8, v___x_2128_);
lean_ctor_set(v___x_2130_, 9, v___x_2128_);
lean_ctor_set(v___x_2130_, 10, v___x_2128_);
return v___x_2130_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2131_ = lean_unsigned_to_nat(32u);
v___x_2132_ = lean_mk_empty_array_with_capacity(v___x_2131_);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
return v___x_2133_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2134_ = ((size_t)5ULL);
v___x_2135_ = lean_unsigned_to_nat(0u);
v___x_2136_ = lean_unsigned_to_nat(32u);
v___x_2137_ = lean_mk_empty_array_with_capacity(v___x_2136_);
v___x_2138_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_2139_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
lean_ctor_set(v___x_2139_, 1, v___x_2137_);
lean_ctor_set(v___x_2139_, 2, v___x_2135_);
lean_ctor_set(v___x_2139_, 3, v___x_2135_);
lean_ctor_set_usize(v___x_2139_, 4, v___x_2134_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2140_ = lean_box(1);
v___x_2141_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2142_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
lean_ctor_set(v___x_2143_, 1, v___x_2141_);
lean_ctor_set(v___x_2143_, 2, v___x_2140_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; lean_object* v_toCold_2149_; lean_object* v_env_2150_; lean_object* v_options_2151_; uint8_t v___x_2152_; lean_object* v_env_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2148_ = lean_st_ref_get(v___y_2146_);
v_toCold_2149_ = lean_ctor_get(v___y_2145_, 0);
v_env_2150_ = lean_ctor_get(v___x_2148_, 0);
lean_inc_ref(v_env_2150_);
lean_dec(v___x_2148_);
v_options_2151_ = lean_ctor_get(v_toCold_2149_, 2);
v___x_2152_ = 0;
v_env_2153_ = l_Lean_Environment_setRecordingDeps(v_env_2150_, v___x_2152_);
v___x_2154_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_2151_);
v___x_2156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2156_, 0, v_env_2153_);
lean_ctor_set(v___x_2156_, 1, v___x_2154_);
lean_ctor_set(v___x_2156_, 2, v___x_2155_);
lean_ctor_set(v___x_2156_, 3, v_options_2151_);
v___x_2157_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v_msgData_2144_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_ref_2168_; lean_object* v___x_2169_; lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2178_; 
v_ref_2168_ = lean_ctor_get(v___y_2165_, 2);
v___x_2169_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msg_2164_, v___y_2165_, v___y_2166_);
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2178_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2178_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
lean_inc(v_ref_2168_);
v___x_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2174_, 0, v_ref_2168_);
lean_ctor_set(v___x_2174_, 1, v_a_2170_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set_tag(v___x_2172_, 1);
lean_ctor_set(v___x_2172_, 0, v___x_2174_);
v___x_2176_ = v___x_2172_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2183_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2186_ = l_Lean_stringToMessageData(v___x_2185_);
return v___x_2186_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2189_ = l_Lean_stringToMessageData(v___x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2190_, lean_object* v_decl_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2195_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2196_ = l_Lean_MessageData_ofName(v___x_2190_);
v___x_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2199_, v___y_2192_, v___y_2193_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2201_, lean_object* v_decl_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2201_, v_decl_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v_decl_2202_);
return v_res_2206_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = lean_unsigned_to_nat(3646333153u);
v___x_2250_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2251_ = l_Lean_Name_num___override(v___x_2250_, v___x_2249_);
return v___x_2251_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2254_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2255_ = l_Lean_Name_str___override(v___x_2254_, v___x_2253_);
return v___x_2255_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2258_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2259_ = l_Lean_Name_str___override(v___x_2258_, v___x_2257_);
return v___x_2259_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_unsigned_to_nat(2u);
v___x_2261_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2262_ = l_Lean_Name_num___override(v___x_2261_, v___x_2260_);
return v___x_2262_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2269_ = 0;
v___x_2270_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2271_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2272_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2273_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v___x_2271_);
lean_ctor_set(v___x_2273_, 2, v___x_2270_);
lean_ctor_set_uint8(v___x_2273_, sizeof(void*)*3, v___x_2269_);
return v___x_2273_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2274_; lean_object* v___f_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___f_2274_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___f_2275_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2276_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v___f_2275_);
lean_ctor_set(v___x_2277_, 2, v___f_2274_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2280_ = l_Lean_registerBuiltinAttribute(v___x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v_a_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2283_, lean_object* v_msg_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2284_, v___y_2285_, v___y_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2289_, lean_object* v_msg_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(v_00_u03b1_2289_, v_msg_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2295_, lean_object* v_decl_2296_, lean_object* v_stx_2297_, uint8_t v_x_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2297_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2302_) == 0)
{
uint8_t v___x_2303_; lean_object* v___x_2304_; 
lean_dec_ref_known(v___x_2302_, 1);
v___x_2303_ = 0;
v___x_2304_ = l_Lean_Parser_runParserAttributeHooks(v___x_2295_, v_decl_2296_, v___x_2303_, v___y_2299_, v___y_2300_);
return v___x_2304_;
}
else
{
lean_dec(v_decl_2296_);
lean_dec(v___x_2295_);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2305_, lean_object* v_decl_2306_, lean_object* v_stx_2307_, lean_object* v_x_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
uint8_t v_x_212__boxed_2312_; lean_object* v_res_2313_; 
v_x_212__boxed_2312_ = lean_unbox(v_x_2308_);
v_res_2313_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2305_, v_decl_2306_, v_stx_2307_, v_x_212__boxed_2312_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
return v_res_2313_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = lean_unsigned_to_nat(3789407938u);
v___x_2317_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2318_ = l_Lean_Name_num___override(v___x_2317_, v___x_2316_);
return v___x_2318_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2320_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2321_ = l_Lean_Name_str___override(v___x_2320_, v___x_2319_);
return v___x_2321_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2323_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2324_ = l_Lean_Name_str___override(v___x_2323_, v___x_2322_);
return v___x_2324_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = lean_unsigned_to_nat(2u);
v___x_2326_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2327_ = l_Lean_Name_num___override(v___x_2326_, v___x_2325_);
return v___x_2327_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2334_ = 0;
v___x_2335_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2336_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2337_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2338_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
lean_ctor_set(v___x_2338_, 1, v___x_2336_);
lean_ctor_set(v___x_2338_, 2, v___x_2335_);
lean_ctor_set_uint8(v___x_2338_, sizeof(void*)*3, v___x_2334_);
return v___x_2338_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2339_; lean_object* v___f_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___f_2339_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___f_2340_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2341_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
lean_ctor_set(v___x_2342_, 1, v___f_2340_);
lean_ctor_set(v___x_2342_, 2, v___f_2339_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2345_ = l_Lean_registerBuiltinAttribute(v___x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__0(lean_object* v_env_2350_, lean_object* v_opts_2351_, lean_object* v_aliases_2352_, lean_object* v_categories_2353_, lean_object* v_declName_2354_, lean_object* v_x_2355_){
_start:
{
lean_object* v___x_2356_; 
lean_inc(v_declName_2354_);
v___x_2356_ = l_Lean_Parser_mkParserOfConstantCore(v_env_2350_, v_opts_2351_, v_aliases_2352_, v_categories_2353_, v_declName_2354_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2371_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2371_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2371_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2361_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__0___closed__0));
v___x_2362_ = 1;
v___x_2363_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2354_, v___x_2362_);
v___x_2364_ = lean_string_append(v___x_2361_, v___x_2363_);
lean_dec_ref(v___x_2363_);
v___x_2365_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__0___closed__1));
v___x_2366_ = lean_string_append(v___x_2364_, v___x_2365_);
v___x_2367_ = lean_string_append(v___x_2366_, v_a_2357_);
lean_dec(v_a_2357_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2367_);
v___x_2369_ = v___x_2359_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_declName_2354_);
v_a_2372_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2374_ = v___x_2356_;
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2356_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v_snd_2376_; lean_object* v___x_2378_; 
v_snd_2376_ = lean_ctor_get(v_a_2372_, 1);
lean_inc(v_snd_2376_);
lean_dec(v_a_2372_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v_snd_2376_);
v___x_2378_ = v___x_2374_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_snd_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__1(lean_object* v_p_2381_, lean_object* v_tks_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_thunk_get_own(v_p_2381_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_dec_ref_known(v___x_2383_, 1);
return v_tks_2382_;
}
else
{
lean_object* v_a_2384_; lean_object* v_info_2385_; lean_object* v_collectTokens_2386_; lean_object* v___x_2387_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v_info_2385_ = lean_ctor_get(v_a_2384_, 0);
lean_inc_ref(v_info_2385_);
lean_dec(v_a_2384_);
v_collectTokens_2386_ = lean_ctor_get(v_info_2385_, 0);
lean_inc_ref(v_collectTokens_2386_);
lean_dec_ref(v_info_2385_);
v___x_2387_ = lean_apply_1(v_collectTokens_2386_, v_tks_2382_);
return v___x_2387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__1___boxed(lean_object* v_p_2388_, lean_object* v_tks_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__1(v_p_2388_, v_tks_2389_);
lean_dec_ref(v_p_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__2(lean_object* v_p_2391_, lean_object* v_ks_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_thunk_get_own(v_p_2391_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_dec_ref_known(v___x_2393_, 1);
return v_ks_2392_;
}
else
{
lean_object* v_a_2394_; lean_object* v_info_2395_; lean_object* v_collectKinds_2396_; lean_object* v___x_2397_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v_info_2395_ = lean_ctor_get(v_a_2394_, 0);
lean_inc_ref(v_info_2395_);
lean_dec(v_a_2394_);
v_collectKinds_2396_ = lean_ctor_get(v_info_2395_, 1);
lean_inc_ref(v_collectKinds_2396_);
lean_dec_ref(v_info_2395_);
v___x_2397_ = lean_apply_1(v_collectKinds_2396_, v_ks_2392_);
return v___x_2397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__2___boxed(lean_object* v_p_2398_, lean_object* v_ks_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__2(v_p_2398_, v_ks_2399_);
lean_dec_ref(v_p_2398_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__3(lean_object* v_p_2401_, lean_object* v_c_2402_, lean_object* v_s_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_thunk_get_own(v_p_2401_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; lean_object* v___x_2408_; 
lean_dec_ref(v_c_2402_);
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v___x_2406_ = lean_box(0);
v___x_2407_ = 1;
v___x_2408_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2403_, v_a_2405_, v___x_2406_, v___x_2407_);
return v___x_2408_;
}
else
{
lean_object* v_a_2409_; lean_object* v_fn_2410_; lean_object* v___x_2411_; 
v_a_2409_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2404_, 1);
v_fn_2410_ = lean_ctor_get(v_a_2409_, 1);
lean_inc_ref(v_fn_2410_);
lean_dec(v_a_2409_);
v___x_2411_ = lean_apply_2(v_fn_2410_, v_c_2402_, v_s_2403_);
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__3___boxed(lean_object* v_p_2412_, lean_object* v_c_2413_, lean_object* v_s_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__3(v_p_2412_, v_c_2413_, v_s_2414_);
lean_dec_ref(v_p_2412_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser(lean_object* v_env_2416_, lean_object* v_opts_2417_, lean_object* v_aliases_2418_, lean_object* v_categories_2419_, lean_object* v_declName_2420_, lean_object* v_firstTokens_2421_){
_start:
{
lean_object* v___f_2422_; lean_object* v_p_2423_; lean_object* v___f_2424_; lean_object* v___f_2425_; lean_object* v___f_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___f_2422_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__0), 6, 5);
lean_closure_set(v___f_2422_, 0, v_env_2416_);
lean_closure_set(v___f_2422_, 1, v_opts_2417_);
lean_closure_set(v___f_2422_, 2, v_aliases_2418_);
lean_closure_set(v___f_2422_, 3, v_categories_2419_);
lean_closure_set(v___f_2422_, 4, v_declName_2420_);
v_p_2423_ = lean_mk_thunk(v___f_2422_);
lean_inc_ref_n(v_p_2423_, 2);
v___f_2424_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2424_, 0, v_p_2423_);
v___f_2425_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__2___boxed), 2, 1);
lean_closure_set(v___f_2425_, 0, v_p_2423_);
v___f_2426_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2426_, 0, v_p_2423_);
v___x_2427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2427_, 0, v___f_2424_);
lean_ctor_set(v___x_2427_, 1, v___f_2425_);
lean_ctor_set(v___x_2427_, 2, v_firstTokens_2421_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v___f_2426_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object* v_s_2429_, lean_object* v_x_2430_, lean_object* v_a_2431_){
_start:
{
switch(lean_obj_tag(v_x_2430_))
{
case 0:
{
lean_object* v_val_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2441_; 
lean_dec_ref(v_s_2429_);
v_val_2433_ = lean_ctor_get(v_x_2430_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_x_2430_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2435_ = v_x_2430_;
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_val_2433_);
lean_dec(v_x_2430_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2441_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_val_2433_);
v___x_2438_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2439_; 
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
return v___x_2439_;
}
}
}
case 1:
{
lean_object* v_val_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2450_; 
lean_dec_ref(v_s_2429_);
v_val_2442_ = lean_ctor_get(v_x_2430_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_x_2430_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2444_ = v_x_2430_;
v_isShared_2445_ = v_isSharedCheck_2450_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_val_2442_);
lean_dec(v_x_2430_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2450_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_val_2442_);
v___x_2447_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
return v___x_2448_;
}
}
}
case 2:
{
lean_object* v_catName_2451_; lean_object* v_declName_2452_; uint8_t v_behavior_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2461_; 
lean_dec_ref(v_s_2429_);
v_catName_2451_ = lean_ctor_get(v_x_2430_, 0);
v_declName_2452_ = lean_ctor_get(v_x_2430_, 1);
v_behavior_2453_ = lean_ctor_get_uint8(v_x_2430_, sizeof(void*)*2);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_x_2430_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2455_ = v_x_2430_;
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_declName_2452_);
lean_inc(v_catName_2451_);
lean_dec(v_x_2430_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_catName_2451_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_declName_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, sizeof(void*)*2, v_behavior_2453_);
v___x_2458_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
return v___x_2459_;
}
}
}
default: 
{
lean_object* v_catName_2462_; lean_object* v_declName_2463_; uint8_t v_leading_2464_; lean_object* v_firstTokens_2465_; lean_object* v_prio_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2479_; 
v_catName_2462_ = lean_ctor_get(v_x_2430_, 0);
v_declName_2463_ = lean_ctor_get(v_x_2430_, 1);
v_leading_2464_ = lean_ctor_get_uint8(v_x_2430_, sizeof(void*)*4);
v_firstTokens_2465_ = lean_ctor_get(v_x_2430_, 2);
v_prio_2466_ = lean_ctor_get(v_x_2430_, 3);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_x_2430_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2468_ = v_x_2430_;
v_isShared_2469_ = v_isSharedCheck_2479_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_prio_2466_);
lean_inc(v_firstTokens_2465_);
lean_inc(v_declName_2463_);
lean_inc(v_catName_2462_);
lean_dec(v_x_2430_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2479_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v_env_2470_; lean_object* v_opts_2471_; lean_object* v_categories_2472_; lean_object* v_aliases_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v_env_2470_ = lean_ctor_get(v_a_2431_, 0);
v_opts_2471_ = lean_ctor_get(v_a_2431_, 1);
v_categories_2472_ = lean_ctor_get(v_s_2429_, 2);
lean_inc_ref(v_categories_2472_);
v_aliases_2473_ = lean_ctor_get(v_s_2429_, 3);
lean_inc(v_aliases_2473_);
lean_dec_ref(v_s_2429_);
lean_inc(v_declName_2463_);
lean_inc_ref(v_opts_2471_);
lean_inc_ref(v_env_2470_);
v___x_2474_ = l___private_Lean_Parser_Extension_0__Lean_Parser_mkLazyImportedParser(v_env_2470_, v_opts_2471_, v_aliases_2473_, v_categories_2472_, v_declName_2463_, v_firstTokens_2465_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 2, v___x_2474_);
v___x_2476_ = v___x_2468_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_catName_2462_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_declName_2463_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v_prio_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2478_, sizeof(void*)*4, v_leading_2464_);
v___x_2476_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
return v___x_2477_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object* v_s_2480_, lean_object* v_x_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(v_s_2480_, v_x_2481_, v_a_2482_);
lean_dec_ref(v_a_2482_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2486_ = l_Lean_Parser_builtinTokenTable;
v___x_2487_ = lean_st_ref_get(v___x_2486_);
v___x_2488_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_2489_ = lean_st_ref_get(v___x_2488_);
v___x_2490_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_2491_ = lean_st_ref_get(v___x_2490_);
v___x_2492_ = l_Lean_Parser_parserAliasesRef;
v___x_2493_ = lean_st_ref_get(v___x_2492_);
v___x_2494_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2487_);
lean_ctor_set(v___x_2494_, 1, v___x_2489_);
lean_ctor_set(v___x_2494_, 2, v___x_2491_);
lean_ctor_set(v___x_2494_, 3, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v_x_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_a_2499_);
lean_inc_ref_n(v___x_2500_, 2);
v___x_2501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
lean_ctor_set(v___x_2501_, 2, v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_x_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v_x_2502_, v_a_2503_);
lean_dec_ref(v_x_2502_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v___y_2505_){
_start:
{
lean_inc_ref(v___y_2505_);
return v___y_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v___y_2506_);
lean_dec_ref(v___y_2506_);
return v_res_2507_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2518_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2519_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2520_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed), 1, 0);
v___x_2521_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedGlobals___boxed), 9, 6);
lean_closure_set(v___x_2521_, 0, lean_box(0));
lean_closure_set(v___x_2521_, 1, lean_box(0));
lean_closure_set(v___x_2521_, 2, lean_box(0));
lean_closure_set(v___x_2521_, 3, v___x_2520_);
lean_closure_set(v___x_2521_, 4, v___x_2519_);
lean_closure_set(v___x_2521_, 5, v___x_2518_);
return v___x_2521_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; lean_object* v___f_2525_; lean_object* v___f_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2522_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_);
v___x_2523_ = lean_box(0);
v___x_2524_ = 0;
v___f_2525_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___f_2526_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2527_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2528_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2529_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2530_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed), 1, 0);
v___x_2531_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2532_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v___x_2530_);
lean_ctor_set(v___x_2532_, 2, v___x_2529_);
lean_ctor_set(v___x_2532_, 3, v___x_2528_);
lean_ctor_set(v___x_2532_, 4, v___x_2527_);
lean_ctor_set(v___x_2532_, 5, v___x_2527_);
lean_ctor_set(v___x_2532_, 6, v___f_2526_);
lean_ctor_set(v___x_2532_, 7, v___f_2525_);
lean_ctor_set(v___x_2532_, 8, v___x_2523_);
lean_ctor_set(v___x_2532_, 9, v___x_2522_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*10, v___x_2524_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*10 + 1, v___x_2524_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_);
v___x_2535_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_a_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object* v_env_2538_, lean_object* v_catName_2539_){
_start:
{
lean_object* v___x_2540_; lean_object* v_ext_2541_; lean_object* v_toEnvExtension_2542_; lean_object* v_asyncMode_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; lean_object* v___x_2546_; lean_object* v_categories_2547_; lean_object* v___x_2548_; 
v___x_2540_ = l_Lean_Parser_parserExtension;
v_ext_2541_ = lean_ctor_get(v___x_2540_, 1);
v_toEnvExtension_2542_ = lean_ctor_get(v_ext_2541_, 0);
v_asyncMode_2543_ = lean_ctor_get(v_toEnvExtension_2542_, 2);
v___x_2544_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2545_ = 0;
v___x_2546_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2544_, v___x_2540_, v_env_2538_, v_asyncMode_2543_, v___x_2545_);
v_categories_2547_ = lean_ctor_get(v___x_2546_, 2);
lean_inc_ref(v_categories_2547_);
lean_dec(v___x_2546_);
v___x_2548_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2547_, v_catName_2539_);
lean_dec_ref(v_categories_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object* v_env_2549_, lean_object* v_catName_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_Parser_getParserCategory_x3f(v_env_2549_, v_catName_2550_);
lean_dec(v_catName_2550_);
return v_res_2551_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object* v_env_2552_, lean_object* v_catName_2553_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_Parser_getParserCategory_x3f(v_env_2552_, v_catName_2553_);
if (lean_obj_tag(v___x_2554_) == 0)
{
uint8_t v___x_2555_; 
v___x_2555_ = 0;
return v___x_2555_;
}
else
{
uint8_t v___x_2556_; 
lean_dec_ref_known(v___x_2554_, 1);
v___x_2556_ = 1;
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object* v_env_2557_, lean_object* v_catName_2558_){
_start:
{
uint8_t v_res_2559_; lean_object* v_r_2560_; 
v_res_2559_ = l_Lean_Parser_isParserCategory(v_env_2557_, v_catName_2558_);
lean_dec(v_catName_2558_);
v_r_2560_ = lean_box(v_res_2559_);
return v_r_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKindCategories___lam__0(lean_object* v_kind_2561_, lean_object* v_x_2562_, lean_object* v_____s_2563_){
_start:
{
lean_object* v_snd_2564_; lean_object* v_fst_2565_; lean_object* v_kinds_2566_; uint8_t v___x_2567_; 
v_snd_2564_ = lean_ctor_get(v_x_2562_, 1);
lean_inc(v_snd_2564_);
v_fst_2565_ = lean_ctor_get(v_x_2562_, 0);
lean_inc(v_fst_2565_);
lean_dec_ref(v_x_2562_);
v_kinds_2566_ = lean_ctor_get(v_snd_2564_, 1);
lean_inc_ref(v_kinds_2566_);
lean_dec(v_snd_2564_);
v___x_2567_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_2566_, v_kind_2561_);
lean_dec_ref(v_kinds_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; 
lean_dec(v_fst_2565_);
v___x_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_____s_2563_);
return v___x_2568_;
}
else
{
lean_object* v_cats_2569_; lean_object* v___x_2570_; 
v_cats_2569_ = lean_array_push(v_____s_2563_, v_fst_2565_);
v___x_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_cats_2569_);
return v___x_2570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKindCategories___lam__0___boxed(lean_object* v_kind_2571_, lean_object* v_x_2572_, lean_object* v_____s_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_Parser_getSyntaxNodeKindCategories___lam__0(v_kind_2571_, v_x_2572_, v_____s_2573_);
lean_dec(v_kind_2571_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2575_, lean_object* v_keys_2576_, lean_object* v_vals_2577_, lean_object* v_i_2578_, lean_object* v_acc_2579_){
_start:
{
lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2580_ = lean_array_get_size(v_keys_2576_);
v___x_2581_ = lean_nat_dec_lt(v_i_2578_, v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; 
lean_dec(v_i_2578_);
lean_dec_ref(v_f_2575_);
v___x_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2582_, 0, v_acc_2579_);
return v___x_2582_;
}
else
{
lean_object* v_k_2583_; lean_object* v_v_2584_; lean_object* v___x_2585_; 
v_k_2583_ = lean_array_fget_borrowed(v_keys_2576_, v_i_2578_);
v_v_2584_ = lean_array_fget_borrowed(v_vals_2577_, v_i_2578_);
lean_inc_ref(v_f_2575_);
lean_inc(v_v_2584_);
lean_inc(v_k_2583_);
v___x_2585_ = lean_apply_3(v_f_2575_, v_acc_2579_, v_k_2583_, v_v_2584_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_dec(v_i_2578_);
lean_dec_ref(v_f_2575_);
return v___x_2585_;
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___x_2585_, 1);
v___x_2587_ = lean_unsigned_to_nat(1u);
v___x_2588_ = lean_nat_add(v_i_2578_, v___x_2587_);
lean_dec(v_i_2578_);
v_i_2578_ = v___x_2588_;
v_acc_2579_ = v_a_2586_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2590_, lean_object* v_keys_2591_, lean_object* v_vals_2592_, lean_object* v_i_2593_, lean_object* v_acc_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2590_, v_keys_2591_, v_vals_2592_, v_i_2593_, v_acc_2594_);
lean_dec_ref(v_vals_2592_);
lean_dec_ref(v_keys_2591_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2596_, lean_object* v_as_2597_, size_t v_i_2598_, size_t v_stop_2599_, lean_object* v_b_2600_){
_start:
{
lean_object* v_a_2602_; lean_object* v___y_2607_; uint8_t v___x_2609_; 
v___x_2609_ = lean_usize_dec_eq(v_i_2598_, v_stop_2599_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_array_uget_borrowed(v_as_2597_, v_i_2598_);
switch(lean_obj_tag(v___x_2610_))
{
case 0:
{
lean_object* v_key_2611_; lean_object* v_val_2612_; lean_object* v___x_2613_; 
v_key_2611_ = lean_ctor_get(v___x_2610_, 0);
v_val_2612_ = lean_ctor_get(v___x_2610_, 1);
lean_inc_ref(v_f_2596_);
lean_inc(v_val_2612_);
lean_inc(v_key_2611_);
v___x_2613_ = lean_apply_3(v_f_2596_, v_b_2600_, v_key_2611_, v_val_2612_);
v___y_2607_ = v___x_2613_;
goto v___jp_2606_;
}
case 1:
{
lean_object* v_node_2614_; lean_object* v___x_2615_; 
v_node_2614_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_node_2614_);
lean_inc_ref(v_f_2596_);
v___x_2615_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(v_f_2596_, v_node_2614_, v_b_2600_);
v___y_2607_ = v___x_2615_;
goto v___jp_2606_;
}
default: 
{
v_a_2602_ = v_b_2600_;
goto v___jp_2601_;
}
}
}
else
{
lean_object* v___x_2616_; 
lean_dec_ref(v_f_2596_);
v___x_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_b_2600_);
return v___x_2616_;
}
v___jp_2601_:
{
size_t v___x_2603_; size_t v___x_2604_; 
v___x_2603_ = ((size_t)1ULL);
v___x_2604_ = lean_usize_add(v_i_2598_, v___x_2603_);
v_i_2598_ = v___x_2604_;
v_b_2600_ = v_a_2602_;
goto _start;
}
v___jp_2606_:
{
if (lean_obj_tag(v___y_2607_) == 0)
{
lean_dec_ref(v_f_2596_);
return v___y_2607_;
}
else
{
lean_object* v_a_2608_; 
v_a_2608_ = lean_ctor_get(v___y_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___y_2607_, 1);
v_a_2602_ = v_a_2608_;
goto v___jp_2601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_){
_start:
{
if (lean_obj_tag(v_x_2618_) == 0)
{
lean_object* v_es_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2633_; 
v_es_2620_ = lean_ctor_get(v_x_2618_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_x_2618_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2622_ = v_x_2618_;
v_isShared_2623_ = v_isSharedCheck_2633_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_es_2620_);
lean_dec(v_x_2618_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2633_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v___x_2624_ = lean_unsigned_to_nat(0u);
v___x_2625_ = lean_array_get_size(v_es_2620_);
v___x_2626_ = lean_nat_dec_lt(v___x_2624_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2628_; 
lean_dec_ref(v_es_2620_);
lean_dec_ref(v_f_2617_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set_tag(v___x_2622_, 1);
lean_ctor_set(v___x_2622_, 0, v_x_2619_);
v___x_2628_ = v___x_2622_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_x_2619_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
else
{
size_t v___x_2630_; size_t v___x_2631_; lean_object* v___x_2632_; 
lean_del_object(v___x_2622_);
v___x_2630_ = ((size_t)0ULL);
v___x_2631_ = lean_usize_of_nat(v___x_2625_);
v___x_2632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2617_, v_es_2620_, v___x_2630_, v___x_2631_, v_x_2619_);
lean_dec_ref(v_es_2620_);
return v___x_2632_;
}
}
}
else
{
lean_object* v_ks_2634_; lean_object* v_vs_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_ks_2634_ = lean_ctor_get(v_x_2618_, 0);
lean_inc_ref(v_ks_2634_);
v_vs_2635_ = lean_ctor_get(v_x_2618_, 1);
lean_inc_ref(v_vs_2635_);
lean_dec_ref_known(v_x_2618_, 2);
v___x_2636_ = lean_unsigned_to_nat(0u);
v___x_2637_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2617_, v_ks_2634_, v_vs_2635_, v___x_2636_, v_x_2619_);
lean_dec_ref(v_vs_2635_);
lean_dec_ref(v_ks_2634_);
return v___x_2637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_2638_, lean_object* v_as_2639_, lean_object* v_i_2640_, lean_object* v_stop_2641_, lean_object* v_b_2642_){
_start:
{
size_t v_i_boxed_2643_; size_t v_stop_boxed_2644_; lean_object* v_res_2645_; 
v_i_boxed_2643_ = lean_unbox_usize(v_i_2640_);
lean_dec(v_i_2640_);
v_stop_boxed_2644_ = lean_unbox_usize(v_stop_2641_);
lean_dec(v_stop_2641_);
v_res_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2638_, v_as_2639_, v_i_boxed_2643_, v_stop_boxed_2644_, v_b_2642_);
lean_dec_ref(v_as_2639_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg___lam__0(lean_object* v_f_2646_, lean_object* v_s_2647_, lean_object* v_a_2648_, lean_object* v_b_2649_){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v_a_2648_);
lean_ctor_set(v___x_2650_, 1, v_b_2649_);
v___x_2651_ = lean_apply_2(v_f_2646_, v___x_2650_, v_s_2647_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2651_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2651_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
v_a_2660_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2651_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2651_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg(lean_object* v_map_2668_, lean_object* v_init_2669_, lean_object* v_f_2670_){
_start:
{
lean_object* v___f_2671_; lean_object* v___x_2672_; lean_object* v_a_2673_; 
v___f_2671_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2671_, 0, v_f_2670_);
lean_inc_ref(v_map_2668_);
v___x_2672_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(v___f_2671_, v_map_2668_, v_init_2669_);
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref(v___x_2672_);
return v_a_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg___boxed(lean_object* v_map_2674_, lean_object* v_init_2675_, lean_object* v_f_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg(v_map_2674_, v_init_2675_, v_f_2676_);
lean_dec_ref(v_map_2674_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKindCategories(lean_object* v_env_2680_, lean_object* v_kind_2681_){
_start:
{
lean_object* v___x_2682_; lean_object* v_ext_2683_; lean_object* v_toEnvExtension_2684_; lean_object* v_asyncMode_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; lean_object* v___x_2688_; lean_object* v_categories_2689_; lean_object* v___f_2690_; lean_object* v_cats_2691_; lean_object* v___x_2692_; 
v___x_2682_ = l_Lean_Parser_parserExtension;
v_ext_2683_ = lean_ctor_get(v___x_2682_, 1);
v_toEnvExtension_2684_ = lean_ctor_get(v_ext_2683_, 0);
v_asyncMode_2685_ = lean_ctor_get(v_toEnvExtension_2684_, 2);
v___x_2686_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2687_ = 0;
v___x_2688_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2686_, v___x_2682_, v_env_2680_, v_asyncMode_2685_, v___x_2687_);
v_categories_2689_ = lean_ctor_get(v___x_2688_, 2);
lean_inc_ref(v_categories_2689_);
lean_dec(v___x_2688_);
v___f_2690_ = lean_alloc_closure((void*)(l_Lean_Parser_getSyntaxNodeKindCategories___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2690_, 0, v_kind_2681_);
v_cats_2691_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKindCategories___closed__0));
v___x_2692_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg(v_categories_2689_, v_cats_2691_, v___f_2690_);
lean_dec_ref(v_categories_2689_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0(lean_object* v_00_u03c3_2693_, lean_object* v_00_u03b2_2694_, lean_object* v_map_2695_, lean_object* v_init_2696_, lean_object* v_f_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg(v_map_2695_, v_init_2696_, v_f_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___boxed(lean_object* v_00_u03c3_2699_, lean_object* v_00_u03b2_2700_, lean_object* v_map_2701_, lean_object* v_init_2702_, lean_object* v_f_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0(v_00_u03c3_2699_, v_00_u03b2_2700_, v_map_2701_, v_init_2702_, v_f_2703_);
lean_dec_ref(v_map_2701_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0___redArg(lean_object* v_map_2705_, lean_object* v_f_2706_, lean_object* v_init_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(v_f_2706_, v_map_2705_, v_init_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0(lean_object* v_00_u03c3_2709_, lean_object* v_00_u03c3_2710_, lean_object* v_00_u03b2_2711_, lean_object* v_map_2712_, lean_object* v_f_2713_, lean_object* v_init_2714_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(v_f_2713_, v_map_2712_, v_init_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2716_, lean_object* v_00_u03c3_2717_, lean_object* v_00_u03b1_2718_, lean_object* v_00_u03b2_2719_, lean_object* v_f_2720_, lean_object* v_x_2721_, lean_object* v_x_2722_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(v_f_2720_, v_x_2721_, v_x_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2724_, lean_object* v_00_u03b2_2725_, lean_object* v_00_u03c3_2726_, lean_object* v_00_u03c3_2727_, lean_object* v_f_2728_, lean_object* v_as_2729_, size_t v_i_2730_, size_t v_stop_2731_, lean_object* v_b_2732_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2728_, v_as_2729_, v_i_2730_, v_stop_2731_, v_b_2732_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2734_, lean_object* v_00_u03b2_2735_, lean_object* v_00_u03c3_2736_, lean_object* v_00_u03c3_2737_, lean_object* v_f_2738_, lean_object* v_as_2739_, lean_object* v_i_2740_, lean_object* v_stop_2741_, lean_object* v_b_2742_){
_start:
{
size_t v_i_boxed_2743_; size_t v_stop_boxed_2744_; lean_object* v_res_2745_; 
v_i_boxed_2743_ = lean_unbox_usize(v_i_2740_);
lean_dec(v_i_2740_);
v_stop_boxed_2744_ = lean_unbox_usize(v_stop_2741_);
lean_dec(v_stop_2741_);
v_res_2745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2734_, v_00_u03b2_2735_, v_00_u03c3_2736_, v_00_u03c3_2737_, v_f_2738_, v_as_2739_, v_i_boxed_2743_, v_stop_boxed_2744_, v_b_2742_);
lean_dec_ref(v_as_2739_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_2746_, lean_object* v_00_u03c3_2747_, lean_object* v_00_u03b1_2748_, lean_object* v_00_u03b2_2749_, lean_object* v_f_2750_, lean_object* v_keys_2751_, lean_object* v_vals_2752_, lean_object* v_heq_2753_, lean_object* v_i_2754_, lean_object* v_acc_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2750_, v_keys_2751_, v_vals_2752_, v_i_2754_, v_acc_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_2757_, lean_object* v_00_u03c3_2758_, lean_object* v_00_u03b1_2759_, lean_object* v_00_u03b2_2760_, lean_object* v_f_2761_, lean_object* v_keys_2762_, lean_object* v_vals_2763_, lean_object* v_heq_2764_, lean_object* v_i_2765_, lean_object* v_acc_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_2757_, v_00_u03c3_2758_, v_00_u03b1_2759_, v_00_u03b2_2760_, v_f_2761_, v_keys_2762_, v_vals_2763_, v_heq_2764_, v_i_2765_, v_acc_2766_);
lean_dec_ref(v_vals_2763_);
lean_dec_ref(v_keys_2762_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object* v_env_2768_, lean_object* v_catName_2769_, lean_object* v_declName_2770_, uint8_t v_behavior_2771_){
_start:
{
uint8_t v___x_2772_; 
lean_inc_ref(v_env_2768_);
v___x_2772_ = l_Lean_Parser_isParserCategory(v_env_2768_, v_catName_2769_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2773_ = l_Lean_Parser_parserExtension;
v___x_2774_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2774_, 0, v_catName_2769_);
lean_ctor_set(v___x_2774_, 1, v_declName_2770_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*2, v_behavior_2771_);
v___x_2775_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2773_, v_env_2768_, v___x_2774_);
v___x_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
return v___x_2776_;
}
else
{
lean_object* v___x_2777_; 
lean_dec(v_declName_2770_);
lean_dec_ref(v_env_2768_);
v___x_2777_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_2769_);
return v___x_2777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* v_env_2778_, lean_object* v_catName_2779_, lean_object* v_declName_2780_, lean_object* v_behavior_2781_){
_start:
{
uint8_t v_behavior_boxed_2782_; lean_object* v_res_2783_; 
v_behavior_boxed_2782_ = lean_unbox(v_behavior_2781_);
v_res_2783_ = l_Lean_Parser_addParserCategory(v_env_2778_, v_catName_2779_, v_declName_2780_, v_behavior_boxed_2782_);
return v_res_2783_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object* v_env_2784_, lean_object* v_catName_2785_){
_start:
{
lean_object* v___x_2786_; lean_object* v_ext_2787_; lean_object* v_toEnvExtension_2788_; lean_object* v_asyncMode_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; lean_object* v___x_2792_; lean_object* v_categories_2793_; lean_object* v___x_2794_; 
v___x_2786_ = l_Lean_Parser_parserExtension;
v_ext_2787_ = lean_ctor_get(v___x_2786_, 1);
v_toEnvExtension_2788_ = lean_ctor_get(v_ext_2787_, 0);
v_asyncMode_2789_ = lean_ctor_get(v_toEnvExtension_2788_, 2);
v___x_2790_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2791_ = 0;
v___x_2792_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2790_, v___x_2786_, v_env_2784_, v_asyncMode_2789_, v___x_2791_);
v_categories_2793_ = lean_ctor_get(v___x_2792_, 2);
lean_inc_ref(v_categories_2793_);
lean_dec(v___x_2792_);
v___x_2794_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2793_, v_catName_2785_);
lean_dec_ref(v_categories_2793_);
if (lean_obj_tag(v___x_2794_) == 0)
{
uint8_t v___x_2795_; 
v___x_2795_ = 0;
return v___x_2795_;
}
else
{
lean_object* v_val_2796_; uint8_t v_behavior_2797_; 
v_val_2796_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_val_2796_);
lean_dec_ref_known(v___x_2794_, 1);
v_behavior_2797_ = lean_ctor_get_uint8(v_val_2796_, sizeof(void*)*3);
lean_dec(v_val_2796_);
return v_behavior_2797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object* v_env_2798_, lean_object* v_catName_2799_){
_start:
{
uint8_t v_res_2800_; lean_object* v_r_2801_; 
v_res_2800_ = l_Lean_Parser_leadingIdentBehavior(v_env_2798_, v_catName_2799_);
lean_dec(v_catName_2799_);
v_r_2801_ = lean_box(v_res_2800_);
return v_r_2801_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConst_spec__0(lean_object* v_x_2802_, lean_object* v_x_2803_){
_start:
{
if (lean_obj_tag(v_x_2803_) == 0)
{
return v_x_2802_;
}
else
{
lean_object* v_head_2804_; lean_object* v_tail_2805_; lean_object* v___x_2806_; 
v_head_2804_ = lean_ctor_get(v_x_2803_, 0);
lean_inc_n(v_head_2804_, 2);
v_tail_2805_ = lean_ctor_get(v_x_2803_, 1);
lean_inc(v_tail_2805_);
lean_dec_ref_known(v_x_2803_, 2);
v___x_2806_ = l_Lean_Data_Trie_insert___redArg(v_x_2802_, v_head_2804_, v_head_2804_);
lean_dec(v_head_2804_);
v_x_2802_ = v___x_2806_;
v_x_2803_ = v_tail_2805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConst___lam__0(lean_object* v_info_2808_, lean_object* v_ctx_2809_){
_start:
{
lean_object* v_toInputContext_2810_; lean_object* v_toParserModuleContext_2811_; lean_object* v_toCacheableParserContext_2812_; lean_object* v_tokens_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2824_; 
v_toInputContext_2810_ = lean_ctor_get(v_ctx_2809_, 0);
v_toParserModuleContext_2811_ = lean_ctor_get(v_ctx_2809_, 1);
v_toCacheableParserContext_2812_ = lean_ctor_get(v_ctx_2809_, 2);
v_tokens_2813_ = lean_ctor_get(v_ctx_2809_, 3);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_ctx_2809_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2815_ = v_ctx_2809_;
v_isShared_2816_ = v_isSharedCheck_2824_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_tokens_2813_);
lean_inc(v_toCacheableParserContext_2812_);
lean_inc(v_toParserModuleContext_2811_);
lean_inc(v_toInputContext_2810_);
lean_dec(v_ctx_2809_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2824_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_collectTokens_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2822_; 
v_collectTokens_2817_ = lean_ctor_get(v_info_2808_, 0);
lean_inc_ref(v_collectTokens_2817_);
lean_dec_ref(v_info_2808_);
v___x_2818_ = lean_box(0);
v___x_2819_ = lean_apply_1(v_collectTokens_2817_, v___x_2818_);
v___x_2820_ = l_List_foldl___at___00Lean_Parser_evalParserConst_spec__0(v_tokens_2813_, v___x_2819_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 3, v___x_2820_);
v___x_2822_ = v___x_2815_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_toInputContext_2810_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_toParserModuleContext_2811_);
lean_ctor_set(v_reuseFailAlloc_2823_, 2, v_toCacheableParserContext_2812_);
lean_ctor_set(v_reuseFailAlloc_2823_, 3, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConst(lean_object* v_declName_2825_, lean_object* v_evalFallback_x3f_2826_, lean_object* v_ctx_2827_, lean_object* v_s_2828_){
_start:
{
lean_object* v_toParserModuleContext_2829_; lean_object* v_env_2830_; lean_object* v_options_2831_; lean_object* v___x_2832_; lean_object* v_ext_2833_; lean_object* v_toEnvExtension_2834_; lean_object* v_asyncMode_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; lean_object* v___x_2838_; lean_object* v_categories_2839_; lean_object* v_aliases_2840_; lean_object* v___x_2841_; 
v_toParserModuleContext_2829_ = lean_ctor_get(v_ctx_2827_, 1);
v_env_2830_ = lean_ctor_get(v_toParserModuleContext_2829_, 0);
v_options_2831_ = lean_ctor_get(v_toParserModuleContext_2829_, 1);
v___x_2832_ = l_Lean_Parser_parserExtension;
v_ext_2833_ = lean_ctor_get(v___x_2832_, 1);
v_toEnvExtension_2834_ = lean_ctor_get(v_ext_2833_, 0);
v_asyncMode_2835_ = lean_ctor_get(v_toEnvExtension_2834_, 2);
v___x_2836_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2837_ = 0;
lean_inc_ref_n(v_env_2830_, 2);
v___x_2838_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2836_, v___x_2832_, v_env_2830_, v_asyncMode_2835_, v___x_2837_);
v_categories_2839_ = lean_ctor_get(v___x_2838_, 2);
lean_inc_ref(v_categories_2839_);
v_aliases_2840_ = lean_ctor_get(v___x_2838_, 3);
lean_inc(v_aliases_2840_);
lean_dec(v___x_2838_);
lean_inc_ref(v_options_2831_);
v___x_2841_ = l_Lean_Parser_mkParserOfConstantCore(v_env_2830_, v_options_2831_, v_aliases_2840_, v_categories_2839_, v_declName_2825_);
if (lean_obj_tag(v___x_2841_) == 0)
{
if (lean_obj_tag(v_evalFallback_x3f_2826_) == 1)
{
lean_object* v_val_2842_; lean_object* v___x_2843_; 
lean_dec_ref_known(v___x_2841_, 1);
v_val_2842_ = lean_ctor_get(v_evalFallback_x3f_2826_, 0);
lean_inc(v_val_2842_);
lean_dec_ref_known(v_evalFallback_x3f_2826_, 1);
v___x_2843_ = lean_apply_2(v_val_2842_, v_ctx_2827_, v_s_2828_);
return v___x_2843_;
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; 
lean_dec_ref(v_ctx_2827_);
lean_dec(v_evalFallback_x3f_2826_);
v_a_2844_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2841_, 1);
v___x_2845_ = lean_box(0);
v___x_2846_ = 1;
v___x_2847_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2828_, v_a_2844_, v___x_2845_, v___x_2846_);
return v___x_2847_;
}
}
else
{
lean_object* v_a_2848_; lean_object* v_snd_2849_; lean_object* v_info_2850_; lean_object* v_fn_2851_; lean_object* v___f_2852_; lean_object* v___x_2853_; 
lean_dec(v_evalFallback_x3f_2826_);
v_a_2848_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2841_, 1);
v_snd_2849_ = lean_ctor_get(v_a_2848_, 1);
lean_inc(v_snd_2849_);
lean_dec(v_a_2848_);
v_info_2850_ = lean_ctor_get(v_snd_2849_, 0);
lean_inc_ref(v_info_2850_);
v_fn_2851_ = lean_ctor_get(v_snd_2849_, 1);
lean_inc_ref(v_fn_2851_);
lean_dec(v_snd_2849_);
v___f_2852_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConst___lam__0), 2, 1);
lean_closure_set(v___f_2852_, 0, v_info_2850_);
v___x_2853_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2852_, v_fn_2851_, v_ctx_2827_, v_s_2828_);
return v___x_2853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object* v_name_2854_, lean_object* v_decl_2855_, lean_object* v_ref_2856_){
_start:
{
lean_object* v_defValue_2858_; lean_object* v_descr_2859_; lean_object* v_deprecation_x3f_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_defValue_2858_ = lean_ctor_get(v_decl_2855_, 0);
v_descr_2859_ = lean_ctor_get(v_decl_2855_, 1);
v_deprecation_x3f_2860_ = lean_ctor_get(v_decl_2855_, 2);
v___x_2861_ = lean_alloc_ctor(1, 0, 1);
v___x_2862_ = lean_unbox(v_defValue_2858_);
lean_ctor_set_uint8(v___x_2861_, 0, v___x_2862_);
lean_inc(v_deprecation_x3f_2860_);
lean_inc_ref(v_descr_2859_);
lean_inc_n(v_name_2854_, 2);
v___x_2863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2863_, 0, v_name_2854_);
lean_ctor_set(v___x_2863_, 1, v_ref_2856_);
lean_ctor_set(v___x_2863_, 2, v___x_2861_);
lean_ctor_set(v___x_2863_, 3, v_descr_2859_);
lean_ctor_set(v___x_2863_, 4, v_deprecation_x3f_2860_);
v___x_2864_ = lean_register_option(v_name_2854_, v___x_2863_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2872_; 
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v___x_2864_, 0);
lean_dec(v_unused_2873_);
v___x_2866_ = v___x_2864_;
v_isShared_2867_ = v_isSharedCheck_2872_;
goto v_resetjp_2865_;
}
else
{
lean_dec(v___x_2864_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2872_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2870_; 
lean_inc(v_defValue_2858_);
v___x_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2868_, 0, v_name_2854_);
lean_ctor_set(v___x_2868_, 1, v_defValue_2858_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2868_);
v___x_2870_ = v___x_2866_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_name_2854_);
v_a_2874_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2864_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2864_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2882_, lean_object* v_decl_2883_, lean_object* v_ref_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v_name_2882_, v_decl_2883_, v_ref_2884_);
lean_dec_ref(v_decl_2883_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2904_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2905_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2906_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2907_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v___x_2904_, v___x_2905_, v___x_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(lean_object* v_o_2913_, lean_object* v_k_2914_, uint8_t v_v_2915_){
_start:
{
lean_object* v_map_2916_; uint8_t v_hasTrace_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2931_; 
v_map_2916_ = lean_ctor_get(v_o_2913_, 0);
v_hasTrace_2917_ = lean_ctor_get_uint8(v_o_2913_, sizeof(void*)*1);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_o_2913_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2919_ = v_o_2913_;
v_isShared_2920_ = v_isSharedCheck_2931_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_map_2916_);
lean_dec(v_o_2913_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2931_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2921_, 0, v_v_2915_);
lean_inc(v_k_2914_);
v___x_2922_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2914_, v___x_2921_, v_map_2916_);
if (v_hasTrace_2917_ == 0)
{
lean_object* v___x_2923_; uint8_t v___x_2924_; lean_object* v___x_2926_; 
v___x_2923_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_2924_ = l_Lean_Name_isPrefixOf(v___x_2923_, v_k_2914_);
lean_dec(v_k_2914_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v___x_2922_);
v___x_2926_ = v___x_2919_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2922_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*1, v___x_2924_);
return v___x_2926_;
}
}
else
{
lean_object* v___x_2929_; 
lean_dec(v_k_2914_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v___x_2922_);
v___x_2929_ = v___x_2919_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2922_);
lean_ctor_set_uint8(v_reuseFailAlloc_2930_, sizeof(void*)*1, v_hasTrace_2917_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___boxed(lean_object* v_o_2932_, lean_object* v_k_2933_, lean_object* v_v_2934_){
_start:
{
uint8_t v_v_boxed_2935_; lean_object* v_res_2936_; 
v_v_boxed_2935_ = lean_unbox(v_v_2934_);
v_res_2936_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_o_2932_, v_k_2933_, v_v_boxed_2935_);
return v_res_2936_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(lean_object* v_opts_2937_, lean_object* v_opt_2938_){
_start:
{
lean_object* v_name_2939_; lean_object* v_defValue_2940_; lean_object* v_map_2941_; lean_object* v___x_2942_; 
v_name_2939_ = lean_ctor_get(v_opt_2938_, 0);
v_defValue_2940_ = lean_ctor_get(v_opt_2938_, 1);
v_map_2941_ = lean_ctor_get(v_opts_2937_, 0);
v___x_2942_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2941_, v_name_2939_);
if (lean_obj_tag(v___x_2942_) == 0)
{
uint8_t v___x_2943_; 
v___x_2943_ = lean_unbox(v_defValue_2940_);
return v___x_2943_;
}
else
{
lean_object* v_val_2944_; 
v_val_2944_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_val_2944_);
lean_dec_ref_known(v___x_2942_, 1);
if (lean_obj_tag(v_val_2944_) == 1)
{
uint8_t v_v_2945_; 
v_v_2945_ = lean_ctor_get_uint8(v_val_2944_, 0);
lean_dec_ref_known(v_val_2944_, 0);
return v_v_2945_;
}
else
{
uint8_t v___x_2946_; 
lean_dec(v_val_2944_);
v___x_2946_ = lean_unbox(v_defValue_2940_);
return v___x_2946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1___boxed(lean_object* v_opts_2947_, lean_object* v_opt_2948_){
_start:
{
uint8_t v_res_2949_; lean_object* v_r_2950_; 
v_res_2949_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_opts_2947_, v_opt_2948_);
lean_dec_ref(v_opt_2948_);
lean_dec_ref(v_opts_2947_);
v_r_2950_ = lean_box(v_res_2949_);
return v_r_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0(uint8_t v_suppressInsideQuot_2956_, lean_object* v_ctx_2957_){
_start:
{
lean_object* v_toParserModuleContext_2958_; lean_object* v_toInputContext_2959_; lean_object* v_toCacheableParserContext_2960_; lean_object* v_tokens_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2981_; 
v_toParserModuleContext_2958_ = lean_ctor_get(v_ctx_2957_, 1);
v_toInputContext_2959_ = lean_ctor_get(v_ctx_2957_, 0);
v_toCacheableParserContext_2960_ = lean_ctor_get(v_ctx_2957_, 2);
v_tokens_2961_ = lean_ctor_get(v_ctx_2957_, 3);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_ctx_2957_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2963_ = v_ctx_2957_;
v_isShared_2964_ = v_isSharedCheck_2981_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_tokens_2961_);
lean_inc(v_toCacheableParserContext_2960_);
lean_inc(v_toParserModuleContext_2958_);
lean_inc(v_toInputContext_2959_);
lean_dec(v_ctx_2957_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2981_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v_env_2965_; lean_object* v_options_2966_; lean_object* v_currNamespace_2967_; lean_object* v_openDecls_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2980_; 
v_env_2965_ = lean_ctor_get(v_toParserModuleContext_2958_, 0);
v_options_2966_ = lean_ctor_get(v_toParserModuleContext_2958_, 1);
v_currNamespace_2967_ = lean_ctor_get(v_toParserModuleContext_2958_, 2);
v_openDecls_2968_ = lean_ctor_get(v_toParserModuleContext_2958_, 3);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_toParserModuleContext_2958_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2970_ = v_toParserModuleContext_2958_;
v_isShared_2971_ = v_isSharedCheck_2980_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_openDecls_2968_);
lean_inc(v_currNamespace_2967_);
lean_inc(v_options_2966_);
lean_inc(v_env_2965_);
lean_dec(v_toParserModuleContext_2958_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2980_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2972_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_2973_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_2966_, v___x_2972_, v_suppressInsideQuot_2956_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 1, v___x_2973_);
v___x_2975_ = v___x_2970_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_env_2965_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2973_);
lean_ctor_set(v_reuseFailAlloc_2979_, 2, v_currNamespace_2967_);
lean_ctor_set(v_reuseFailAlloc_2979_, 3, v_openDecls_2968_);
v___x_2975_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2977_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_2975_);
v___x_2977_ = v___x_2963_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_toInputContext_2959_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v___x_2975_);
lean_ctor_set(v_reuseFailAlloc_2978_, 2, v_toCacheableParserContext_2960_);
lean_ctor_set(v_reuseFailAlloc_2978_, 3, v_tokens_2961_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0___boxed(lean_object* v_suppressInsideQuot_2982_, lean_object* v_ctx_2983_){
_start:
{
uint8_t v_suppressInsideQuot_boxed_2984_; lean_object* v_res_2985_; 
v_suppressInsideQuot_boxed_2984_ = lean_unbox(v_suppressInsideQuot_2982_);
v_res_2985_ = l_Lean_Parser_evalInsideQuot___lam__0(v_suppressInsideQuot_boxed_2984_, v_ctx_2983_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object* v_fn_2986_, lean_object* v_declName_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v_toCacheableParserContext_2990_; lean_object* v_toParserModuleContext_2991_; lean_object* v_quotDepth_2992_; uint8_t v_suppressInsideQuot_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v_toCacheableParserContext_2990_ = lean_ctor_get(v___y_2988_, 2);
v_toParserModuleContext_2991_ = lean_ctor_get(v___y_2988_, 1);
v_quotDepth_2992_ = lean_ctor_get(v_toCacheableParserContext_2990_, 1);
v_suppressInsideQuot_2993_ = lean_ctor_get_uint8(v_toCacheableParserContext_2990_, sizeof(void*)*4);
v___x_2994_ = lean_unsigned_to_nat(0u);
v___x_2995_ = lean_nat_dec_lt(v___x_2994_, v_quotDepth_2992_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
lean_dec(v_declName_2987_);
v___x_2996_ = lean_apply_2(v_fn_2986_, v___y_2988_, v___y_2989_);
return v___x_2996_;
}
else
{
if (v_suppressInsideQuot_2993_ == 0)
{
lean_object* v_env_2997_; lean_object* v_options_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v_env_2997_ = lean_ctor_get(v_toParserModuleContext_2991_, 0);
v_options_2998_ = lean_ctor_get(v_toParserModuleContext_2991_, 1);
v___x_2999_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_3000_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_2998_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
lean_dec(v_declName_2987_);
v___x_3001_ = lean_apply_2(v_fn_2986_, v___y_2988_, v___y_2989_);
return v___x_3001_;
}
else
{
uint8_t v___x_3002_; 
lean_inc(v_declName_2987_);
lean_inc_ref(v_env_2997_);
v___x_3002_ = l_Lean_Environment_contains(v_env_2997_, v_declName_2987_, v___x_3000_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; 
lean_dec(v_declName_2987_);
v___x_3003_ = lean_apply_2(v_fn_2986_, v___y_2988_, v___y_2989_);
return v___x_3003_;
}
else
{
lean_object* v___x_3004_; lean_object* v___f_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3004_ = lean_box(v_suppressInsideQuot_2993_);
v___f_3005_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3005_, 0, v___x_3004_);
v___x_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3006_, 0, v_fn_2986_);
v___x_3007_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConst), 4, 2);
lean_closure_set(v___x_3007_, 0, v_declName_2987_);
lean_closure_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_3005_, v___x_3007_, v___y_2988_, v___y_2989_);
return v___x_3008_;
}
}
}
else
{
lean_object* v___x_3009_; 
lean_dec(v_declName_2987_);
v___x_3009_ = lean_apply_2(v_fn_2986_, v___y_2988_, v___y_2989_);
return v___x_3009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object* v_declName_3010_, lean_object* v_p_3011_){
_start:
{
lean_object* v_info_3012_; lean_object* v_fn_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3021_; 
v_info_3012_ = lean_ctor_get(v_p_3011_, 0);
v_fn_3013_ = lean_ctor_get(v_p_3011_, 1);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_p_3011_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3015_ = v_p_3011_;
v_isShared_3016_ = v_isSharedCheck_3021_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_fn_3013_);
lean_inc(v_info_3012_);
lean_dec(v_p_3011_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3021_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___f_3017_; lean_object* v___x_3019_; 
v___f_3017_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__1), 4, 2);
lean_closure_set(v___f_3017_, 0, v_fn_3013_);
lean_closure_set(v___f_3017_, 1, v_declName_3010_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 1, v___f_3017_);
v___x_3019_ = v___x_3015_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_info_3012_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v___f_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object* v_catName_3022_, lean_object* v_declName_3023_, uint8_t v_leading_3024_, lean_object* v_p_3025_, lean_object* v_prio_3026_){
_start:
{
lean_object* v_p_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
lean_inc_n(v_declName_3023_, 2);
v_p_3028_ = l_Lean_Parser_evalInsideQuot(v_declName_3023_, v_p_3025_);
v___x_3029_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_3030_ = lean_st_ref_get(v___x_3029_);
lean_inc_ref(v_p_3028_);
v___x_3031_ = l_Lean_Parser_addParser(v___x_3030_, v_catName_3022_, v_declName_3023_, v_leading_3024_, v_p_3028_, v_prio_3026_);
v___x_3032_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_3031_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3034_; lean_object* v_info_3035_; lean_object* v_collectKinds_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v___x_3034_ = lean_st_ref_swap(v___x_3029_, v_a_3033_);
lean_dec(v___x_3034_);
v_info_3035_ = lean_ctor_get(v_p_3028_, 0);
lean_inc_ref(v_info_3035_);
lean_dec_ref(v_p_3028_);
v_collectKinds_3036_ = lean_ctor_get(v_info_3035_, 1);
v___x_3037_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_3038_ = lean_st_ref_take(v___x_3037_);
lean_inc_ref(v_collectKinds_3036_);
v___x_3039_ = lean_apply_1(v_collectKinds_3036_, v___x_3038_);
v___x_3040_ = lean_st_ref_put(v___x_3037_, v___x_3039_);
v___x_3041_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_3035_, v_declName_3023_);
return v___x_3041_;
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec_ref(v_p_3028_);
lean_dec(v_declName_3023_);
v_a_3042_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3032_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3032_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* v_catName_3050_, lean_object* v_declName_3051_, lean_object* v_leading_3052_, lean_object* v_p_3053_, lean_object* v_prio_3054_, lean_object* v_a_3055_){
_start:
{
uint8_t v_leading_boxed_3056_; lean_object* v_res_3057_; 
v_leading_boxed_3056_ = lean_unbox(v_leading_3052_);
v_res_3057_ = l_Lean_Parser_addBuiltinParser(v_catName_3050_, v_declName_3051_, v_leading_boxed_3056_, v_p_3053_, v_prio_3054_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* v_catName_3058_, lean_object* v_declName_3059_, lean_object* v_p_3060_, lean_object* v_prio_3061_){
_start:
{
uint8_t v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = 1;
v___x_3064_ = l_Lean_Parser_addBuiltinParser(v_catName_3058_, v_declName_3059_, v___x_3063_, v_p_3060_, v_prio_3061_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object* v_catName_3065_, lean_object* v_declName_3066_, lean_object* v_p_3067_, lean_object* v_prio_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_Parser_addBuiltinLeadingParser(v_catName_3065_, v_declName_3066_, v_p_3067_, v_prio_3068_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* v_catName_3071_, lean_object* v_declName_3072_, lean_object* v_p_3073_, lean_object* v_prio_3074_){
_start:
{
uint8_t v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = 0;
v___x_3077_ = l_Lean_Parser_addBuiltinParser(v_catName_3071_, v_declName_3072_, v___x_3076_, v_p_3073_, v_prio_3074_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object* v_catName_3078_, lean_object* v_declName_3079_, lean_object* v_p_3080_, lean_object* v_prio_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_Lean_Parser_addBuiltinTrailingParser(v_catName_3078_, v_declName_3079_, v_p_3080_, v_prio_3081_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object* v_kind_3084_){
_start:
{
uint8_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = 1;
lean_inc(v_kind_3084_);
v___x_3086_ = l_Lean_Name_toString(v_kind_3084_, v___x_3085_);
v___x_3087_ = l_Lean_Parser_mkAntiquot(v___x_3086_, v_kind_3084_, v___x_3085_, v___x_3085_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object* v_kind_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v___x_3091_; lean_object* v_fn_3092_; lean_object* v___x_3093_; 
v___x_3091_ = l_Lean_Parser_mkCategoryAntiquotParser(v_kind_3088_);
v_fn_3092_ = lean_ctor_get(v___x_3091_, 1);
lean_inc_ref(v_fn_3092_);
lean_dec_ref(v___x_3091_);
v___x_3093_ = lean_apply_2(v_fn_3092_, v_a_3089_, v_a_3090_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl___lam__0(lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v___x_3097_; lean_object* v_fn_3098_; lean_object* v___x_3099_; 
v___x_3097_ = l_Lean_Parser_mkCategoryAntiquotParser(v___y_3094_);
v_fn_3098_ = lean_ctor_get(v___x_3097_, 1);
lean_inc_ref(v_fn_3098_);
lean_dec_ref(v___x_3097_);
v___x_3099_ = lean_apply_2(v_fn_3098_, v___y_3095_, v___y_3096_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* v_catName_3108_, lean_object* v_ctx_3109_, lean_object* v_s_3110_){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; uint8_t v___x_3114_; lean_object* v___y_3116_; 
v___x_3111_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3112_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__1));
v___x_3113_ = lean_name_eq(v_catName_3108_, v___x_3112_);
v___x_3114_ = 1;
if (v___x_3113_ == 0)
{
v___y_3116_ = v_catName_3108_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3139_; 
lean_dec(v_catName_3108_);
v___x_3139_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__5));
v___y_3116_ = v___x_3139_;
goto v___jp_3115_;
}
v___jp_3115_:
{
lean_object* v_toParserModuleContext_3117_; lean_object* v_env_3118_; lean_object* v___x_3119_; lean_object* v_ext_3120_; lean_object* v_toEnvExtension_3121_; lean_object* v_asyncMode_3122_; uint8_t v___x_3123_; lean_object* v___x_3124_; lean_object* v_categories_3125_; lean_object* v___x_3126_; 
v_toParserModuleContext_3117_ = lean_ctor_get(v_ctx_3109_, 1);
v_env_3118_ = lean_ctor_get(v_toParserModuleContext_3117_, 0);
v___x_3119_ = l_Lean_Parser_parserExtension;
v_ext_3120_ = lean_ctor_get(v___x_3119_, 1);
v_toEnvExtension_3121_ = lean_ctor_get(v_ext_3120_, 0);
v_asyncMode_3122_ = lean_ctor_get(v_toEnvExtension_3121_, 2);
v___x_3123_ = 0;
lean_inc_ref(v_env_3118_);
v___x_3124_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3111_, v___x_3119_, v_env_3118_, v_asyncMode_3122_, v___x_3123_);
v_categories_3125_ = lean_ctor_get(v___x_3124_, 2);
lean_inc_ref(v_categories_3125_);
lean_dec(v___x_3124_);
v___x_3126_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_3125_, v___y_3116_);
lean_dec_ref(v_categories_3125_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_dec_ref(v_ctx_3109_);
v___x_3127_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__2));
v___x_3128_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3116_, v___x_3114_);
v___x_3129_ = lean_string_append(v___x_3127_, v___x_3128_);
lean_dec_ref(v___x_3128_);
v___x_3130_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__3));
v___x_3131_ = lean_string_append(v___x_3129_, v___x_3130_);
v___x_3132_ = lean_box(0);
v___x_3133_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_3110_, v___x_3131_, v___x_3132_, v___x_3114_);
return v___x_3133_;
}
else
{
lean_object* v_val_3134_; lean_object* v_tables_3135_; uint8_t v_behavior_3136_; lean_object* v___f_3137_; lean_object* v___x_3138_; 
v_val_3134_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_val_3134_);
lean_dec_ref_known(v___x_3126_, 1);
v_tables_3135_ = lean_ctor_get(v_val_3134_, 2);
lean_inc_ref(v_tables_3135_);
v_behavior_3136_ = lean_ctor_get_uint8(v_val_3134_, sizeof(void*)*3);
lean_dec(v_val_3134_);
lean_inc(v___y_3116_);
v___f_3137_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl___lam__0), 3, 1);
lean_closure_set(v___f_3137_, 0, v___y_3116_);
v___x_3138_ = l_Lean_Parser_prattParser(v___y_3116_, v_tables_3135_, v_behavior_3136_, v___f_3137_, v_ctx_3109_, v_s_3110_);
return v___x_3138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3142_ = l_Lean_Parser_categoryParserFnRef;
v___x_3143_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_));
v___x_3144_ = lean_box(0);
v___x_3145_ = lean_st_ref_swap(v___x_3142_, v___x_3143_);
lean_dec(v___x_3145_);
v___x_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object* v_a_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
return v_res_3148_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object* v_ext_3153_, lean_object* v_b_3154_, uint8_t v_kind_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_toCold_3159_; lean_object* v_currNamespace_3160_; lean_object* v___x_3161_; lean_object* v_env_3162_; lean_object* v_nextMacroScope_3163_; lean_object* v_ngen_3164_; lean_object* v_auxDeclNGen_3165_; lean_object* v_traceState_3166_; lean_object* v_recordedDeps_3167_; lean_object* v_messages_3168_; lean_object* v_infoState_3169_; lean_object* v_snapshotTasks_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3182_; 
v_toCold_3159_ = lean_ctor_get(v___y_3156_, 0);
v_currNamespace_3160_ = lean_ctor_get(v_toCold_3159_, 4);
v___x_3161_ = lean_st_ref_take(v___y_3157_);
v_env_3162_ = lean_ctor_get(v___x_3161_, 0);
v_nextMacroScope_3163_ = lean_ctor_get(v___x_3161_, 1);
v_ngen_3164_ = lean_ctor_get(v___x_3161_, 2);
v_auxDeclNGen_3165_ = lean_ctor_get(v___x_3161_, 3);
v_traceState_3166_ = lean_ctor_get(v___x_3161_, 4);
v_recordedDeps_3167_ = lean_ctor_get(v___x_3161_, 6);
v_messages_3168_ = lean_ctor_get(v___x_3161_, 7);
v_infoState_3169_ = lean_ctor_get(v___x_3161_, 8);
v_snapshotTasks_3170_ = lean_ctor_get(v___x_3161_, 9);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3182_ == 0)
{
lean_object* v_unused_3183_; 
v_unused_3183_ = lean_ctor_get(v___x_3161_, 5);
lean_dec(v_unused_3183_);
v___x_3172_ = v___x_3161_;
v_isShared_3173_ = v_isSharedCheck_3182_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_snapshotTasks_3170_);
lean_inc(v_infoState_3169_);
lean_inc(v_messages_3168_);
lean_inc(v_recordedDeps_3167_);
lean_inc(v_traceState_3166_);
lean_inc(v_auxDeclNGen_3165_);
lean_inc(v_ngen_3164_);
lean_inc(v_nextMacroScope_3163_);
lean_inc(v_env_3162_);
lean_dec(v___x_3161_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3182_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3174_ = lean_box(0);
lean_inc(v_currNamespace_3160_);
v___x_3175_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3162_, v_ext_3153_, v_b_3154_, v_kind_3155_, v_currNamespace_3160_);
v___x_3176_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 5, v___x_3176_);
lean_ctor_set(v___x_3172_, 0, v___x_3175_);
v___x_3178_ = v___x_3172_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3175_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_nextMacroScope_3163_);
lean_ctor_set(v_reuseFailAlloc_3181_, 2, v_ngen_3164_);
lean_ctor_set(v_reuseFailAlloc_3181_, 3, v_auxDeclNGen_3165_);
lean_ctor_set(v_reuseFailAlloc_3181_, 4, v_traceState_3166_);
lean_ctor_set(v_reuseFailAlloc_3181_, 5, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3181_, 6, v_recordedDeps_3167_);
lean_ctor_set(v_reuseFailAlloc_3181_, 7, v_messages_3168_);
lean_ctor_set(v_reuseFailAlloc_3181_, 8, v_infoState_3169_);
lean_ctor_set(v_reuseFailAlloc_3181_, 9, v_snapshotTasks_3170_);
v___x_3178_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = lean_st_ref_put(v___y_3157_, v___x_3178_);
v___x_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3174_);
return v___x_3180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object* v_ext_3184_, lean_object* v_b_3185_, lean_object* v_kind_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
uint8_t v_kind_boxed_3190_; lean_object* v_res_3191_; 
v_kind_boxed_3190_ = lean_unbox(v_kind_3186_);
v_res_3191_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_3184_, v_b_3185_, v_kind_boxed_3190_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object* v_00_u03b1_3192_, lean_object* v_00_u03b2_3193_, lean_object* v_00_u03c3_3194_, lean_object* v_ext_3195_, lean_object* v_b_3196_, uint8_t v_kind_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_3195_, v_b_3196_, v_kind_3197_, v___y_3198_, v___y_3199_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object* v_00_u03b1_3202_, lean_object* v_00_u03b2_3203_, lean_object* v_00_u03c3_3204_, lean_object* v_ext_3205_, lean_object* v_b_3206_, lean_object* v_kind_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
uint8_t v_kind_boxed_3211_; lean_object* v_res_3212_; 
v_kind_boxed_3211_ = lean_unbox(v_kind_3207_);
v_res_3212_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(v_00_u03b1_3202_, v_00_u03b2_3203_, v_00_u03c3_3204_, v_ext_3205_, v_b_3206_, v_kind_boxed_3211_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object* v_x_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
if (lean_obj_tag(v_x_3213_) == 0)
{
lean_object* v_a_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v_a_3217_ = lean_ctor_get(v_x_3213_, 0);
lean_inc(v_a_3217_);
lean_dec_ref_known(v_x_3213_, 1);
v___x_3218_ = l_Lean_stringToMessageData(v_a_3217_);
v___x_3219_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3218_, v___y_3214_, v___y_3215_);
return v___x_3219_;
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
v_a_3220_ = lean_ctor_get(v_x_3213_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_x_3213_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v_x_3213_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v_x_3213_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
lean_ctor_set_tag(v___x_3222_, 0);
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object* v_x_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_3228_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object* v_tk_3233_, uint8_t v_kind_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v_env_3240_; lean_object* v___x_3241_; lean_object* v_ext_3242_; lean_object* v_toEnvExtension_3243_; lean_object* v_asyncMode_3244_; uint8_t v___x_3245_; lean_object* v___x_3246_; lean_object* v_tokens_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3238_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3239_ = lean_st_ref_get(v_a_3236_);
v_env_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc_ref(v_env_3240_);
lean_dec(v___x_3239_);
v___x_3241_ = l_Lean_Parser_parserExtension;
v_ext_3242_ = lean_ctor_get(v___x_3241_, 1);
v_toEnvExtension_3243_ = lean_ctor_get(v_ext_3242_, 0);
v_asyncMode_3244_ = lean_ctor_get(v_toEnvExtension_3243_, 2);
v___x_3245_ = 0;
v___x_3246_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3238_, v___x_3241_, v_env_3240_, v_asyncMode_3244_, v___x_3245_);
v_tokens_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc_ref(v_tokens_3247_);
lean_dec(v___x_3246_);
lean_inc_ref(v_tk_3233_);
v___x_3248_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_3247_, v_tk_3233_);
v___x_3249_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v___x_3248_, v_a_3235_, v_a_3236_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_dec_ref_known(v___x_3249_, 1);
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v_tk_3233_);
v___x_3251_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_3241_, v___x_3250_, v_kind_3234_, v_a_3235_, v_a_3236_);
return v___x_3251_;
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v_tk_3233_);
v_a_3252_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3249_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3249_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object* v_tk_3260_, lean_object* v_kind_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
uint8_t v_kind_boxed_3265_; lean_object* v_res_3266_; 
v_kind_boxed_3265_ = lean_unbox(v_kind_3261_);
v_res_3266_ = l_Lean_Parser_addToken(v_tk_3260_, v_kind_boxed_3265_, v_a_3262_, v_a_3263_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_object* v_00_u03b1_3267_, lean_object* v_x_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_3268_, v___y_3269_, v___y_3270_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___boxed(lean_object* v_00_u03b1_3273_, lean_object* v_x_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(v_00_u03b1_3273_, v_x_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object* v_env_3279_, lean_object* v_k_3280_){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = l_Lean_Parser_parserExtension;
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v_k_3280_);
v___x_3283_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_3281_, v_env_3279_, v___x_3282_);
return v___x_3283_;
}
}
static uint8_t _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0(void){
_start:
{
lean_object* v___x_3284_; uint8_t v___x_3285_; 
v___x_3284_ = lean_box(0);
v___x_3285_ = lean_internal_is_stage0(v___x_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object* v_env_3286_, lean_object* v_k_3287_){
_start:
{
lean_object* v___x_3288_; lean_object* v_ext_3289_; lean_object* v_toEnvExtension_3290_; lean_object* v_asyncMode_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; lean_object* v___x_3294_; lean_object* v_kinds_3295_; uint8_t v___x_3296_; 
v___x_3288_ = l_Lean_Parser_parserExtension;
v_ext_3289_ = lean_ctor_get(v___x_3288_, 1);
v_toEnvExtension_3290_ = lean_ctor_get(v_ext_3289_, 0);
v_asyncMode_3291_ = lean_ctor_get(v_toEnvExtension_3290_, 2);
v___x_3292_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3293_ = 0;
lean_inc_ref(v_env_3286_);
v___x_3294_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3292_, v___x_3288_, v_env_3286_, v_asyncMode_3291_, v___x_3293_);
v_kinds_3295_ = lean_ctor_get(v___x_3294_, 1);
lean_inc_ref(v_kinds_3295_);
lean_dec(v___x_3294_);
v___x_3296_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_3295_, v_k_3287_);
lean_dec_ref(v_kinds_3295_);
if (v___x_3296_ == 0)
{
uint8_t v___x_3297_; 
v___x_3297_ = lean_uint8_once(&l_Lean_Parser_isValidSyntaxNodeKind___closed__0, &l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once, _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0);
if (v___x_3297_ == 0)
{
lean_dec(v_k_3287_);
lean_dec_ref(v_env_3286_);
return v___x_3293_;
}
else
{
uint8_t v___x_3298_; 
v___x_3298_ = l_Lean_Environment_contains(v_env_3286_, v_k_3287_, v___x_3297_);
return v___x_3298_;
}
}
else
{
lean_dec(v_k_3287_);
lean_dec_ref(v_env_3286_);
return v___x_3296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* v_env_3299_, lean_object* v_k_3300_){
_start:
{
uint8_t v_res_3301_; lean_object* v_r_3302_; 
v_res_3301_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_3299_, v_k_3300_);
v_r_3302_ = lean_box(v_res_3301_);
return v_r_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds___lam__0(lean_object* v_ks_3303_, lean_object* v_k_3304_, lean_object* v_x_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3306_, 0, v_k_3304_);
lean_ctor_set(v___x_3306_, 1, v_ks_3303_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3307_, lean_object* v_keys_3308_, lean_object* v_vals_3309_, lean_object* v_i_3310_, lean_object* v_acc_3311_){
_start:
{
lean_object* v___x_3312_; uint8_t v___x_3313_; 
v___x_3312_ = lean_array_get_size(v_keys_3308_);
v___x_3313_ = lean_nat_dec_lt(v_i_3310_, v___x_3312_);
if (v___x_3313_ == 0)
{
lean_dec(v_i_3310_);
lean_dec(v_f_3307_);
return v_acc_3311_;
}
else
{
lean_object* v_k_3314_; lean_object* v_v_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v_k_3314_ = lean_array_fget_borrowed(v_keys_3308_, v_i_3310_);
v_v_3315_ = lean_array_fget_borrowed(v_vals_3309_, v_i_3310_);
lean_inc(v_f_3307_);
lean_inc(v_v_3315_);
lean_inc(v_k_3314_);
v___x_3316_ = lean_apply_3(v_f_3307_, v_acc_3311_, v_k_3314_, v_v_3315_);
v___x_3317_ = lean_unsigned_to_nat(1u);
v___x_3318_ = lean_nat_add(v_i_3310_, v___x_3317_);
lean_dec(v_i_3310_);
v_i_3310_ = v___x_3318_;
v_acc_3311_ = v___x_3316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3320_, lean_object* v_keys_3321_, lean_object* v_vals_3322_, lean_object* v_i_3323_, lean_object* v_acc_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3320_, v_keys_3321_, v_vals_3322_, v_i_3323_, v_acc_3324_);
lean_dec_ref(v_vals_3322_);
lean_dec_ref(v_keys_3321_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3326_, lean_object* v_as_3327_, size_t v_i_3328_, size_t v_stop_3329_, lean_object* v_b_3330_){
_start:
{
lean_object* v___y_3332_; uint8_t v___x_3336_; 
v___x_3336_ = lean_usize_dec_eq(v_i_3328_, v_stop_3329_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; 
v___x_3337_ = lean_array_uget_borrowed(v_as_3327_, v_i_3328_);
switch(lean_obj_tag(v___x_3337_))
{
case 0:
{
lean_object* v_key_3338_; lean_object* v_val_3339_; lean_object* v___x_3340_; 
v_key_3338_ = lean_ctor_get(v___x_3337_, 0);
v_val_3339_ = lean_ctor_get(v___x_3337_, 1);
lean_inc(v_f_3326_);
lean_inc(v_val_3339_);
lean_inc(v_key_3338_);
v___x_3340_ = lean_apply_3(v_f_3326_, v_b_3330_, v_key_3338_, v_val_3339_);
v___y_3332_ = v___x_3340_;
goto v___jp_3331_;
}
case 1:
{
lean_object* v_node_3341_; lean_object* v___x_3342_; 
v_node_3341_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_f_3326_);
v___x_3342_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3326_, v_node_3341_, v_b_3330_);
v___y_3332_ = v___x_3342_;
goto v___jp_3331_;
}
default: 
{
v___y_3332_ = v_b_3330_;
goto v___jp_3331_;
}
}
}
else
{
lean_dec(v_f_3326_);
return v_b_3330_;
}
v___jp_3331_:
{
size_t v___x_3333_; size_t v___x_3334_; 
v___x_3333_ = ((size_t)1ULL);
v___x_3334_ = lean_usize_add(v_i_3328_, v___x_3333_);
v_i_3328_ = v___x_3334_;
v_b_3330_ = v___y_3332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3343_, lean_object* v_x_3344_, lean_object* v_x_3345_){
_start:
{
if (lean_obj_tag(v_x_3344_) == 0)
{
lean_object* v_es_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
v_es_3346_ = lean_ctor_get(v_x_3344_, 0);
v___x_3347_ = lean_unsigned_to_nat(0u);
v___x_3348_ = lean_array_get_size(v_es_3346_);
v___x_3349_ = lean_nat_dec_lt(v___x_3347_, v___x_3348_);
if (v___x_3349_ == 0)
{
lean_dec(v_f_3343_);
return v_x_3345_;
}
else
{
size_t v___x_3350_; size_t v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = ((size_t)0ULL);
v___x_3351_ = lean_usize_of_nat(v___x_3348_);
v___x_3352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3343_, v_es_3346_, v___x_3350_, v___x_3351_, v_x_3345_);
return v___x_3352_;
}
}
else
{
lean_object* v_ks_3353_; lean_object* v_vs_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_ks_3353_ = lean_ctor_get(v_x_3344_, 0);
v_vs_3354_ = lean_ctor_get(v_x_3344_, 1);
v___x_3355_ = lean_unsigned_to_nat(0u);
v___x_3356_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3343_, v_ks_3353_, v_vs_3354_, v___x_3355_, v_x_3345_);
return v___x_3356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3357_, lean_object* v_x_3358_, lean_object* v_x_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3357_, v_x_3358_, v_x_3359_);
lean_dec_ref(v_x_3358_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3361_, lean_object* v_as_3362_, lean_object* v_i_3363_, lean_object* v_stop_3364_, lean_object* v_b_3365_){
_start:
{
size_t v_i_boxed_3366_; size_t v_stop_boxed_3367_; lean_object* v_res_3368_; 
v_i_boxed_3366_ = lean_unbox_usize(v_i_3363_);
lean_dec(v_i_3363_);
v_stop_boxed_3367_ = lean_unbox_usize(v_stop_3364_);
lean_dec(v_stop_3364_);
v_res_3368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3361_, v_as_3362_, v_i_boxed_3366_, v_stop_boxed_3367_, v_b_3365_);
lean_dec_ref(v_as_3362_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object* v_f_3369_, lean_object* v_x1_3370_, lean_object* v_x2_3371_, lean_object* v_x3_3372_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = lean_apply_3(v_f_3369_, v_x1_3370_, v_x2_3371_, v_x3_3372_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object* v_map_3374_, lean_object* v_f_3375_, lean_object* v_init_3376_){
_start:
{
lean_object* v___f_3377_; lean_object* v___x_3378_; 
v___f_3377_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3377_, 0, v_f_3375_);
v___x_3378_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v___f_3377_, v_map_3374_, v_init_3376_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object* v_map_3379_, lean_object* v_f_3380_, lean_object* v_init_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3379_, v_f_3380_, v_init_3381_);
lean_dec_ref(v_map_3379_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* v_env_3384_){
_start:
{
lean_object* v___x_3385_; lean_object* v_ext_3386_; lean_object* v_toEnvExtension_3387_; lean_object* v_asyncMode_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; lean_object* v___x_3391_; lean_object* v_kinds_3392_; lean_object* v___f_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3385_ = l_Lean_Parser_parserExtension;
v_ext_3386_ = lean_ctor_get(v___x_3385_, 1);
v_toEnvExtension_3387_ = lean_ctor_get(v_ext_3386_, 0);
v_asyncMode_3388_ = lean_ctor_get(v_toEnvExtension_3387_, 2);
v___x_3389_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3390_ = 0;
v___x_3391_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3389_, v___x_3385_, v_env_3384_, v_asyncMode_3388_, v___x_3390_);
v_kinds_3392_ = lean_ctor_get(v___x_3391_, 1);
lean_inc_ref(v_kinds_3392_);
lean_dec(v___x_3391_);
v___f_3393_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKinds___closed__0));
v___x_3394_ = lean_box(0);
v___x_3395_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_kinds_3392_, v___f_3393_, v___x_3394_);
lean_dec_ref(v_kinds_3392_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object* v_00_u03c3_3396_, lean_object* v_00_u03b2_3397_, lean_object* v_map_3398_, lean_object* v_f_3399_, lean_object* v_init_3400_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3398_, v_f_3399_, v_init_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object* v_00_u03c3_3402_, lean_object* v_00_u03b2_3403_, lean_object* v_map_3404_, lean_object* v_f_3405_, lean_object* v_init_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(v_00_u03c3_3402_, v_00_u03b2_3403_, v_map_3404_, v_f_3405_, v_init_3406_);
lean_dec_ref(v_map_3404_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object* v_map_3408_, lean_object* v_f_3409_, lean_object* v_init_3410_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3409_, v_map_3408_, v_init_3410_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object* v_map_3412_, lean_object* v_f_3413_, lean_object* v_init_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(v_map_3412_, v_f_3413_, v_init_3414_);
lean_dec_ref(v_map_3412_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object* v_00_u03c3_3416_, lean_object* v_00_u03b2_3417_, lean_object* v_map_3418_, lean_object* v_f_3419_, lean_object* v_init_3420_){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3419_, v_map_3418_, v_init_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3422_, lean_object* v_00_u03b2_3423_, lean_object* v_map_3424_, lean_object* v_f_3425_, lean_object* v_init_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(v_00_u03c3_3422_, v_00_u03b2_3423_, v_map_3424_, v_f_3425_, v_init_3426_);
lean_dec_ref(v_map_3424_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3428_, lean_object* v_00_u03b1_3429_, lean_object* v_00_u03b2_3430_, lean_object* v_f_3431_, lean_object* v_x_3432_, lean_object* v_x_3433_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3431_, v_x_3432_, v_x_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3435_, lean_object* v_00_u03b1_3436_, lean_object* v_00_u03b2_3437_, lean_object* v_f_3438_, lean_object* v_x_3439_, lean_object* v_x_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(v_00_u03c3_3435_, v_00_u03b1_3436_, v_00_u03b2_3437_, v_f_3438_, v_x_3439_, v_x_3440_);
lean_dec_ref(v_x_3439_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3442_, lean_object* v_00_u03b2_3443_, lean_object* v_00_u03c3_3444_, lean_object* v_f_3445_, lean_object* v_as_3446_, size_t v_i_3447_, size_t v_stop_3448_, lean_object* v_b_3449_){
_start:
{
lean_object* v___x_3450_; 
v___x_3450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3445_, v_as_3446_, v_i_3447_, v_stop_3448_, v_b_3449_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3451_, lean_object* v_00_u03b2_3452_, lean_object* v_00_u03c3_3453_, lean_object* v_f_3454_, lean_object* v_as_3455_, lean_object* v_i_3456_, lean_object* v_stop_3457_, lean_object* v_b_3458_){
_start:
{
size_t v_i_boxed_3459_; size_t v_stop_boxed_3460_; lean_object* v_res_3461_; 
v_i_boxed_3459_ = lean_unbox_usize(v_i_3456_);
lean_dec(v_i_3456_);
v_stop_boxed_3460_ = lean_unbox_usize(v_stop_3457_);
lean_dec(v_stop_3457_);
v_res_3461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3451_, v_00_u03b2_3452_, v_00_u03c3_3453_, v_f_3454_, v_as_3455_, v_i_boxed_3459_, v_stop_boxed_3460_, v_b_3458_);
lean_dec_ref(v_as_3455_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3462_, lean_object* v_00_u03b1_3463_, lean_object* v_00_u03b2_3464_, lean_object* v_f_3465_, lean_object* v_keys_3466_, lean_object* v_vals_3467_, lean_object* v_heq_3468_, lean_object* v_i_3469_, lean_object* v_acc_3470_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3465_, v_keys_3466_, v_vals_3467_, v_i_3469_, v_acc_3470_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3472_, lean_object* v_00_u03b1_3473_, lean_object* v_00_u03b2_3474_, lean_object* v_f_3475_, lean_object* v_keys_3476_, lean_object* v_vals_3477_, lean_object* v_heq_3478_, lean_object* v_i_3479_, lean_object* v_acc_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3472_, v_00_u03b1_3473_, v_00_u03b2_3474_, v_f_3475_, v_keys_3476_, v_vals_3477_, v_heq_3478_, v_i_3479_, v_acc_3480_);
lean_dec_ref(v_vals_3477_);
lean_dec_ref(v_keys_3476_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* v_env_3482_){
_start:
{
lean_object* v___x_3483_; lean_object* v_ext_3484_; lean_object* v_toEnvExtension_3485_; lean_object* v_asyncMode_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; lean_object* v___x_3489_; lean_object* v_tokens_3490_; 
v___x_3483_ = l_Lean_Parser_parserExtension;
v_ext_3484_ = lean_ctor_get(v___x_3483_, 1);
v_toEnvExtension_3485_ = lean_ctor_get(v_ext_3484_, 0);
v_asyncMode_3486_ = lean_ctor_get(v_toEnvExtension_3485_, 2);
v___x_3487_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3488_ = 0;
v___x_3489_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3487_, v___x_3483_, v_env_3482_, v_asyncMode_3486_, v___x_3488_);
v_tokens_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc_ref(v_tokens_3490_);
lean_dec(v___x_3489_);
return v_tokens_3490_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__8));
v___x_3516_ = l_Lean_mkAtom(v___x_3515_);
return v___x_3516_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3517_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__10, &l_Lean_Parser_mkInputContext___auto__1___closed__10_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__10);
v___x_3518_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3519_ = lean_array_push(v___x_3518_, v___x_3517_);
return v___x_3519_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3531_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3532_ = lean_array_push(v___x_3531_, v___x_3530_);
return v___x_3532_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3533_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__15, &l_Lean_Parser_mkInputContext___auto__1___closed__15_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__15);
v___x_3534_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__13));
v___x_3535_ = lean_box(2);
v___x_3536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
lean_ctor_set(v___x_3536_, 1, v___x_3534_);
lean_ctor_set(v___x_3536_, 2, v___x_3533_);
return v___x_3536_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3537_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__16, &l_Lean_Parser_mkInputContext___auto__1___closed__16_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__16);
v___x_3538_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__11, &l_Lean_Parser_mkInputContext___auto__1___closed__11_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__11);
v___x_3539_ = lean_array_push(v___x_3538_, v___x_3537_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3540_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3541_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__17, &l_Lean_Parser_mkInputContext___auto__1___closed__17_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__17);
v___x_3542_ = lean_array_push(v___x_3541_, v___x_3540_);
return v___x_3542_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3544_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__18, &l_Lean_Parser_mkInputContext___auto__1___closed__18_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__18);
v___x_3545_ = lean_array_push(v___x_3544_, v___x_3543_);
return v___x_3545_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3547_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__19, &l_Lean_Parser_mkInputContext___auto__1___closed__19_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__19);
v___x_3548_ = lean_array_push(v___x_3547_, v___x_3546_);
return v___x_3548_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3550_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__20, &l_Lean_Parser_mkInputContext___auto__1___closed__20_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__20);
v___x_3551_ = lean_array_push(v___x_3550_, v___x_3549_);
return v___x_3551_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3552_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__21, &l_Lean_Parser_mkInputContext___auto__1___closed__21_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__21);
v___x_3553_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__9));
v___x_3554_ = lean_box(2);
v___x_3555_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v___x_3553_);
lean_ctor_set(v___x_3555_, 2, v___x_3552_);
return v___x_3555_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__22, &l_Lean_Parser_mkInputContext___auto__1___closed__22_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__22);
v___x_3557_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3558_ = lean_array_push(v___x_3557_, v___x_3556_);
return v___x_3558_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3559_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__23, &l_Lean_Parser_mkInputContext___auto__1___closed__23_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__23);
v___x_3560_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3561_ = lean_box(2);
v___x_3562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
lean_ctor_set(v___x_3562_, 1, v___x_3560_);
lean_ctor_set(v___x_3562_, 2, v___x_3559_);
return v___x_3562_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__24, &l_Lean_Parser_mkInputContext___auto__1___closed__24_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__24);
v___x_3564_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3565_ = lean_array_push(v___x_3564_, v___x_3563_);
return v___x_3565_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3566_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__25, &l_Lean_Parser_mkInputContext___auto__1___closed__25_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__25);
v___x_3567_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3568_ = lean_box(2);
v___x_3569_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
lean_ctor_set(v___x_3569_, 1, v___x_3567_);
lean_ctor_set(v___x_3569_, 2, v___x_3566_);
return v___x_3569_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__26, &l_Lean_Parser_mkInputContext___auto__1___closed__26_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__26);
v___x_3571_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3572_ = lean_array_push(v___x_3571_, v___x_3570_);
return v___x_3572_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3573_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__27, &l_Lean_Parser_mkInputContext___auto__1___closed__27_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__27);
v___x_3574_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3575_ = lean_box(2);
v___x_3576_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
lean_ctor_set(v___x_3576_, 1, v___x_3574_);
lean_ctor_set(v___x_3576_, 2, v___x_3573_);
return v___x_3576_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1(void){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__28, &l_Lean_Parser_mkInputContext___auto__1___closed__28_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__28);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object* v_input_3578_, lean_object* v_fileName_3579_, uint8_t v_normalizeLineEndings_3580_, lean_object* v_endPos_3581_){
_start:
{
lean_object* v_fst_3583_; lean_object* v_snd_3584_; lean_object* v_text_3590_; 
v_text_3590_ = l_Lean_FileMap_ofString(v_input_3578_);
if (v_normalizeLineEndings_3580_ == 0)
{
v_fst_3583_ = v_text_3590_;
v_snd_3584_ = v_endPos_3581_;
goto v___jp_3582_;
}
else
{
lean_object* v_source_3591_; lean_object* v_endPos_x27_3592_; lean_object* v___x_3593_; lean_object* v_text_3594_; lean_object* v___x_3595_; 
v_source_3591_ = lean_ctor_get(v_text_3590_, 0);
lean_inc_ref(v_source_3591_);
v_endPos_x27_3592_ = l_Lean_FileMap_toPosition(v_text_3590_, v_endPos_3581_);
lean_dec(v_endPos_3581_);
v___x_3593_ = l_String_crlfToLf(v_source_3591_);
lean_dec_ref(v_source_3591_);
v_text_3594_ = l_Lean_FileMap_ofString(v___x_3593_);
v___x_3595_ = l_Lean_FileMap_ofPosition(v_text_3594_, v_endPos_x27_3592_);
v_fst_3583_ = v_text_3594_;
v_snd_3584_ = v___x_3595_;
goto v___jp_3582_;
}
v___jp_3582_:
{
lean_object* v_source_3585_; lean_object* v___x_3586_; uint8_t v___x_3587_; 
v_source_3585_ = lean_ctor_get(v_fst_3583_, 0);
lean_inc_ref(v_source_3585_);
v___x_3586_ = lean_string_utf8_byte_size(v_source_3585_);
v___x_3587_ = lean_nat_dec_le(v_snd_3584_, v___x_3586_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; 
lean_dec(v_snd_3584_);
v___x_3588_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3588_, 0, v_source_3585_);
lean_ctor_set(v___x_3588_, 1, v_fileName_3579_);
lean_ctor_set(v___x_3588_, 2, v_fst_3583_);
lean_ctor_set(v___x_3588_, 3, v___x_3586_);
return v___x_3588_;
}
else
{
lean_object* v___x_3589_; 
v___x_3589_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3589_, 0, v_source_3585_);
lean_ctor_set(v___x_3589_, 1, v_fileName_3579_);
lean_ctor_set(v___x_3589_, 2, v_fst_3583_);
lean_ctor_set(v___x_3589_, 3, v_snd_3584_);
return v___x_3589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object* v_input_3596_, lean_object* v_fileName_3597_, lean_object* v_normalizeLineEndings_3598_, lean_object* v_endPos_3599_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3600_; lean_object* v_res_3601_; 
v_normalizeLineEndings_boxed_3600_ = lean_unbox(v_normalizeLineEndings_3598_);
v_res_3601_ = l_Lean_Parser_mkInputContext___redArg(v_input_3596_, v_fileName_3597_, v_normalizeLineEndings_boxed_3600_, v_endPos_3599_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object* v_input_3602_, lean_object* v_fileName_3603_, uint8_t v_normalizeLineEndings_3604_, lean_object* v_endPos_3605_, lean_object* v_endPos__valid_3606_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Lean_Parser_mkInputContext___redArg(v_input_3602_, v_fileName_3603_, v_normalizeLineEndings_3604_, v_endPos_3605_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object* v_input_3608_, lean_object* v_fileName_3609_, lean_object* v_normalizeLineEndings_3610_, lean_object* v_endPos_3611_, lean_object* v_endPos__valid_3612_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3613_; lean_object* v_res_3614_; 
v_normalizeLineEndings_boxed_3613_ = lean_unbox(v_normalizeLineEndings_3610_);
v_res_3614_ = l_Lean_Parser_mkInputContext(v_input_3608_, v_fileName_3609_, v_normalizeLineEndings_boxed_3613_, v_endPos_3611_, v_endPos__valid_3612_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* v_input_3617_){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3618_ = l_Lean_Parser_SyntaxStack_empty;
v___x_3619_ = lean_unsigned_to_nat(0u);
v___x_3620_ = l_Lean_Parser_initCacheForInput(v_input_3617_);
v___x_3621_ = lean_box(0);
v___x_3622_ = ((lean_object*)(l_Lean_Parser_mkParserState___closed__0));
v___x_3623_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3618_);
lean_ctor_set(v___x_3623_, 1, v___x_3619_);
lean_ctor_set(v___x_3623_, 2, v___x_3619_);
lean_ctor_set(v___x_3623_, 3, v___x_3620_);
lean_ctor_set(v___x_3623_, 4, v___x_3621_);
lean_ctor_set(v___x_3623_, 5, v___x_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* v_input_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Lean_Parser_mkParserState(v_input_3624_);
lean_dec_ref(v_input_3624_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* v_env_3628_, lean_object* v_catName_3629_, lean_object* v_input_3630_, lean_object* v_fileName_3631_){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v_p_3634_; uint8_t v___x_3635_; lean_object* v___x_3636_; lean_object* v_ictx_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v_s_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3632_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__0));
v___x_3633_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 1);
lean_closure_set(v___x_3633_, 0, v_catName_3629_);
v_p_3634_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_3634_, 0, v___x_3632_);
lean_closure_set(v_p_3634_, 1, v___x_3633_);
v___x_3635_ = 1;
v___x_3636_ = lean_string_utf8_byte_size(v_input_3630_);
lean_inc_ref(v_input_3630_);
v_ictx_3637_ = l_Lean_Parser_mkInputContext___redArg(v_input_3630_, v_fileName_3631_, v___x_3635_, v___x_3636_);
v___x_3638_ = l_Lean_Options_empty;
v___x_3639_ = lean_box(0);
v___x_3640_ = lean_box(0);
lean_inc_ref(v_env_3628_);
v___x_3641_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3641_, 0, v_env_3628_);
lean_ctor_set(v___x_3641_, 1, v___x_3638_);
lean_ctor_set(v___x_3641_, 2, v___x_3639_);
lean_ctor_set(v___x_3641_, 3, v___x_3640_);
v___x_3642_ = l_Lean_Parser_getTokenTable(v_env_3628_);
v___x_3643_ = l_Lean_Parser_mkParserState(v_input_3630_);
lean_dec_ref(v_input_3630_);
lean_inc_ref(v_ictx_3637_);
v_s_3644_ = l_Lean_Parser_ParserFn_run(v_p_3634_, v_ictx_3637_, v___x_3641_, v___x_3642_, v___x_3643_);
lean_inc_ref(v_s_3644_);
v___x_3645_ = l_Lean_Parser_ParserState_allErrors(v_s_3644_);
v___x_3646_ = lean_array_get_size(v___x_3645_);
lean_dec_ref(v___x_3645_);
v___x_3647_ = lean_unsigned_to_nat(0u);
v___x_3648_ = lean_nat_dec_eq(v___x_3646_, v___x_3647_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3637_, v_s_3644_);
v___x_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
return v___x_3650_;
}
else
{
lean_object* v_stxStack_3651_; lean_object* v_pos_3652_; uint8_t v___x_3653_; 
v_stxStack_3651_ = lean_ctor_get(v_s_3644_, 0);
v_pos_3652_ = lean_ctor_get(v_s_3644_, 2);
v___x_3653_ = l_Lean_Parser_InputContext_atEnd(v_ictx_3637_, v_pos_3652_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3654_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__1));
v___x_3655_ = l_Lean_Parser_ParserState_mkError(v_s_3644_, v___x_3654_);
v___x_3656_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3637_, v___x_3655_);
v___x_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
return v___x_3657_;
}
else
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
lean_inc_ref(v_stxStack_3651_);
lean_dec_ref(v_s_3644_);
lean_dec_ref(v_ictx_3637_);
v___x_3658_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3651_);
lean_dec_ref(v_stxStack_3651_);
v___x_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
return v___x_3659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* v_addFnName_3660_, lean_object* v_catName_3661_, lean_object* v_declName_3662_, lean_object* v_prio_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v_val_3679_; lean_object* v___x_3680_; 
v___x_3667_ = lean_box(0);
v___x_3668_ = l_Lean_mkConst(v_addFnName_3660_, v___x_3667_);
v___x_3669_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_catName_3661_);
lean_inc_n(v_declName_3662_, 2);
v___x_3670_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3662_);
v___x_3671_ = l_Lean_mkConst(v_declName_3662_, v___x_3667_);
v___x_3672_ = l_Lean_mkRawNatLit(v_prio_3663_);
v___x_3673_ = lean_unsigned_to_nat(4u);
v___x_3674_ = lean_mk_empty_array_with_capacity(v___x_3673_);
v___x_3675_ = lean_array_push(v___x_3674_, v___x_3669_);
v___x_3676_ = lean_array_push(v___x_3675_, v___x_3670_);
v___x_3677_ = lean_array_push(v___x_3676_, v___x_3671_);
v___x_3678_ = lean_array_push(v___x_3677_, v___x_3672_);
v_val_3679_ = l_Lean_mkAppN(v___x_3668_, v___x_3678_);
lean_dec_ref(v___x_3678_);
v___x_3680_ = l_Lean_declareBuiltin(v_declName_3662_, v_val_3679_, v_a_3664_, v_a_3665_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object* v_addFnName_3681_, lean_object* v_catName_3682_, lean_object* v_declName_3683_, lean_object* v_prio_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3681_, v_catName_3682_, v_declName_3683_, v_prio_3684_, v_a_3685_, v_a_3686_);
lean_dec(v_a_3686_);
lean_dec_ref(v_a_3685_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* v_catName_3694_, lean_object* v_declName_3695_, lean_object* v_prio_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = ((lean_object*)(l_Lean_Parser_declareLeadingBuiltinParser___closed__1));
v___x_3701_ = l_Lean_Parser_declareBuiltinParser(v___x_3700_, v_catName_3694_, v_declName_3695_, v_prio_3696_, v_a_3697_, v_a_3698_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object* v_catName_3702_, lean_object* v_declName_3703_, lean_object* v_prio_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3702_, v_declName_3703_, v_prio_3704_, v_a_3705_, v_a_3706_);
lean_dec(v_a_3706_);
lean_dec_ref(v_a_3705_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* v_catName_3714_, lean_object* v_declName_3715_, lean_object* v_prio_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = ((lean_object*)(l_Lean_Parser_declareTrailingBuiltinParser___closed__1));
v___x_3721_ = l_Lean_Parser_declareBuiltinParser(v___x_3720_, v_catName_3714_, v_declName_3715_, v_prio_3716_, v_a_3717_, v_a_3718_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object* v_catName_3722_, lean_object* v_declName_3723_, lean_object* v_prio_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3722_, v_declName_3723_, v_prio_3724_, v_a_3725_, v_a_3726_);
lean_dec(v_a_3726_);
lean_dec_ref(v_a_3725_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* v_args_3735_){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; uint8_t v___x_3738_; 
v___x_3736_ = l_Lean_Syntax_getNumArgs(v_args_3735_);
v___x_3737_ = lean_unsigned_to_nat(0u);
v___x_3738_ = lean_nat_dec_eq(v___x_3736_, v___x_3737_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3739_; uint8_t v___x_3740_; 
v___x_3739_ = lean_unsigned_to_nat(1u);
v___x_3740_ = lean_nat_dec_eq(v___x_3736_, v___x_3739_);
lean_dec(v___x_3736_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
v___x_3741_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__1));
return v___x_3741_;
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = l_Lean_Syntax_getArg(v_args_3735_, v___x_3737_);
v___x_3743_ = l_Lean_Syntax_isNatLit_x3f(v___x_3742_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3744_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__2));
v___x_3745_ = l_Lean_Syntax_formatStx(v___x_3742_, v___x_3743_, v___x_3738_);
v___x_3746_ = l_Std_Format_defWidth;
v___x_3747_ = l_Std_Format_pretty(v___x_3745_, v___x_3746_, v___x_3737_, v___x_3737_);
v___x_3748_ = lean_string_append(v___x_3744_, v___x_3747_);
lean_dec_ref(v___x_3747_);
v___x_3749_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3750_ = lean_string_append(v___x_3748_, v___x_3749_);
v___x_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
return v___x_3751_;
}
else
{
lean_object* v_val_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec(v___x_3742_);
v_val_3752_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3743_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_val_3752_);
lean_dec(v___x_3743_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_val_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
}
else
{
lean_object* v___x_3760_; 
lean_dec(v___x_3736_);
v___x_3760_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__3));
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* v_args_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_Lean_Parser_getParserPriority(v_args_3761_);
lean_dec(v_args_3761_);
return v_res_3762_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0));
v___x_3765_ = l_Lean_stringToMessageData(v___x_3764_);
return v___x_3765_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3767_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2));
v___x_3768_ = l_Lean_stringToMessageData(v___x_3767_);
return v___x_3768_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3769_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3770_ = l_Lean_stringToMessageData(v___x_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object* v_name_3774_, uint8_t v_kind_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___y_3785_; 
v___x_3779_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1);
v___x_3780_ = l_Lean_MessageData_ofName(v_name_3774_);
v___x_3781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3779_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
v___x_3782_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3);
v___x_3783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3781_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
switch(v_kind_3775_)
{
case 0:
{
lean_object* v___x_3792_; 
v___x_3792_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5));
v___y_3785_ = v___x_3792_;
goto v___jp_3784_;
}
case 1:
{
lean_object* v___x_3793_; 
v___x_3793_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6));
v___y_3785_ = v___x_3793_;
goto v___jp_3784_;
}
default: 
{
lean_object* v___x_3794_; 
v___x_3794_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7));
v___y_3785_ = v___x_3794_;
goto v___jp_3784_;
}
}
v___jp_3784_:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
lean_inc_ref(v___y_3785_);
v___x_3786_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3786_, 0, v___y_3785_);
v___x_3787_ = l_Lean_MessageData_ofFormat(v___x_3786_);
v___x_3788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3783_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
v___x_3789_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3788_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3790_, v___y_3776_, v___y_3777_);
return v___x_3791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object* v_name_3795_, lean_object* v_kind_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
uint8_t v_kind_boxed_3800_; lean_object* v_res_3801_; 
v_kind_boxed_3800_ = lean_unbox(v_kind_3796_);
v_res_3801_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3795_, v_kind_boxed_3800_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3802_, lean_object* v_msg_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_toCold_3807_; lean_object* v_currRecDepth_3808_; lean_object* v_ref_3809_; uint16_t v_optionFlags_3810_; uint8_t v_suppressElabErrors_3811_; uint8_t v_checkDeprecated_3812_; uint8_t v_isRecordingDeps_3813_; lean_object* v_ref_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_toCold_3807_ = lean_ctor_get(v___y_3804_, 0);
v_currRecDepth_3808_ = lean_ctor_get(v___y_3804_, 1);
v_ref_3809_ = lean_ctor_get(v___y_3804_, 2);
v_optionFlags_3810_ = lean_ctor_get_uint16(v___y_3804_, sizeof(void*)*3);
v_suppressElabErrors_3811_ = lean_ctor_get_uint8(v___y_3804_, sizeof(void*)*3 + 2);
v_checkDeprecated_3812_ = lean_ctor_get_uint8(v___y_3804_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3813_ = lean_ctor_get_uint8(v___y_3804_, sizeof(void*)*3 + 4);
v_ref_3814_ = l_Lean_replaceRef(v_ref_3802_, v_ref_3809_);
lean_inc(v_currRecDepth_3808_);
lean_inc_ref(v_toCold_3807_);
v___x_3815_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3815_, 0, v_toCold_3807_);
lean_ctor_set(v___x_3815_, 1, v_currRecDepth_3808_);
lean_ctor_set(v___x_3815_, 2, v_ref_3814_);
lean_ctor_set_uint16(v___x_3815_, sizeof(void*)*3, v_optionFlags_3810_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*3 + 2, v_suppressElabErrors_3811_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*3 + 3, v_checkDeprecated_3812_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*3 + 4, v_isRecordingDeps_3813_);
v___x_3816_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_3803_, v___x_3815_, v___y_3805_);
lean_dec_ref_known(v___x_3815_, 3);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3817_, lean_object* v_msg_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3817_, v_msg_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v_ref_3817_);
return v_res_3822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3824_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_3825_ = l_Lean_stringToMessageData(v___x_3824_);
return v___x_3825_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3827_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_3828_ = l_Lean_stringToMessageData(v___x_3827_);
return v___x_3828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_3831_ = l_Lean_stringToMessageData(v___x_3830_);
return v___x_3831_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_3834_ = l_Lean_stringToMessageData(v___x_3833_);
return v___x_3834_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_3837_ = l_Lean_stringToMessageData(v___x_3836_);
return v___x_3837_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3839_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_3840_ = l_Lean_stringToMessageData(v___x_3839_);
return v___x_3840_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_3843_ = l_Lean_stringToMessageData(v___x_3842_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_3844_, lean_object* v_declHint_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v_env_3850_; uint8_t v___x_3851_; 
v___x_3848_ = lean_box(0);
v___x_3849_ = lean_st_ref_get(v___y_3846_);
v_env_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc_ref(v_env_3850_);
lean_dec(v___x_3849_);
v___x_3851_ = l_Lean_Name_isAnonymous(v_declHint_3845_);
if (v___x_3851_ == 0)
{
uint8_t v_isExporting_3852_; 
v_isExporting_3852_ = lean_ctor_get_uint8(v_env_3850_, sizeof(void*)*13);
if (v_isExporting_3852_ == 0)
{
lean_object* v___x_3853_; 
lean_dec_ref(v_env_3850_);
lean_dec(v_declHint_3845_);
v___x_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3853_, 0, v_msg_3844_);
return v___x_3853_;
}
else
{
lean_object* v___x_3854_; uint8_t v___x_3855_; 
lean_inc_ref(v_env_3850_);
v___x_3854_ = l_Lean_Environment_setExporting(v_env_3850_, v___x_3851_);
lean_inc(v_declHint_3845_);
lean_inc_ref(v___x_3854_);
v___x_3855_ = l_Lean_Environment_contains(v___x_3854_, v_declHint_3845_, v_isExporting_3852_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3856_; 
lean_dec_ref(v___x_3854_);
lean_dec_ref(v_env_3850_);
lean_dec(v_declHint_3845_);
v___x_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3856_, 0, v_msg_3844_);
return v___x_3856_;
}
else
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v_c_3862_; lean_object* v___x_3863_; 
v___x_3857_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_3858_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_3859_ = l_Lean_Options_empty;
lean_inc_ref(v___x_3854_);
v___x_3860_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3854_);
lean_ctor_set(v___x_3860_, 1, v___x_3857_);
lean_ctor_set(v___x_3860_, 2, v___x_3858_);
lean_ctor_set(v___x_3860_, 3, v___x_3859_);
lean_inc(v_declHint_3845_);
v___x_3861_ = l_Lean_MessageData_ofConstName(v_declHint_3845_, v___x_3851_);
v_c_3862_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3862_, 0, v___x_3860_);
lean_ctor_set(v_c_3862_, 1, v___x_3861_);
v___x_3863_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3854_, v_declHint_3845_);
lean_dec_ref(v___x_3854_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
lean_dec_ref(v_env_3850_);
lean_dec(v_declHint_3845_);
v___x_3864_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
lean_ctor_set(v___x_3865_, 1, v_c_3862_);
v___x_3866_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_3867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3865_);
lean_ctor_set(v___x_3867_, 1, v___x_3866_);
v___x_3868_ = l_Lean_MessageData_note(v___x_3867_);
v___x_3869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3869_, 0, v_msg_3844_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
return v___x_3870_;
}
else
{
lean_object* v_val_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3905_; 
v_val_3871_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3873_ = v___x_3863_;
v_isShared_3874_ = v_isSharedCheck_3905_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_val_3871_);
lean_dec(v___x_3863_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3905_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3875_; lean_object* v_moduleNames_3876_; lean_object* v_mod_3877_; uint8_t v___x_3878_; 
v___x_3875_ = l_Lean_Environment_header(v_env_3850_);
lean_dec_ref(v_env_3850_);
v_moduleNames_3876_ = lean_ctor_get(v___x_3875_, 4);
lean_inc_ref(v_moduleNames_3876_);
lean_dec_ref(v___x_3875_);
v_mod_3877_ = lean_array_get(v___x_3848_, v_moduleNames_3876_, v_val_3871_);
lean_dec(v_val_3871_);
lean_dec_ref(v_moduleNames_3876_);
v___x_3878_ = l_Lean_isPrivateName(v_declHint_3845_);
lean_dec(v_declHint_3845_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3890_; 
v___x_3879_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_3880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
lean_ctor_set(v___x_3880_, 1, v_c_3862_);
v___x_3881_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_3882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3880_);
lean_ctor_set(v___x_3882_, 1, v___x_3881_);
v___x_3883_ = l_Lean_MessageData_ofName(v_mod_3877_);
v___x_3884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3882_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v___x_3885_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_3886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3884_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
v___x_3887_ = l_Lean_MessageData_note(v___x_3886_);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v_msg_3844_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
if (v_isShared_3874_ == 0)
{
lean_ctor_set_tag(v___x_3873_, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3888_);
v___x_3890_ = v___x_3873_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3888_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
else
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3892_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
lean_ctor_set(v___x_3893_, 1, v_c_3862_);
v___x_3894_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_3895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3893_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
v___x_3896_ = l_Lean_MessageData_ofName(v_mod_3877_);
v___x_3897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3895_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___x_3898_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3897_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = l_Lean_MessageData_note(v___x_3899_);
v___x_3901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3901_, 0, v_msg_3844_);
lean_ctor_set(v___x_3901_, 1, v___x_3900_);
if (v_isShared_3874_ == 0)
{
lean_ctor_set_tag(v___x_3873_, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3901_);
v___x_3903_ = v___x_3873_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3901_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3906_; 
lean_dec_ref(v_env_3850_);
lean_dec(v_declHint_3845_);
v___x_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3906_, 0, v_msg_3844_);
return v___x_3906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_3907_, lean_object* v_declHint_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3907_, v_declHint_3908_, v___y_3909_);
lean_dec(v___y_3909_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_3912_, lean_object* v_declHint_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v___x_3917_; lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3927_; 
v___x_3917_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3912_, v_declHint_3913_, v___y_3915_);
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3920_ = v___x_3917_;
v_isShared_3921_ = v_isSharedCheck_3927_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3927_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3925_; 
v___x_3922_ = l_Lean_unknownIdentifierMessageTag;
v___x_3923_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
lean_ctor_set(v___x_3923_, 1, v_a_3918_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 0, v___x_3923_);
v___x_3925_ = v___x_3920_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_3928_, lean_object* v_declHint_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3928_, v_declHint_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3934_, lean_object* v_msg_3935_, lean_object* v_declHint_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v___x_3940_; lean_object* v_a_3941_; lean_object* v___x_3942_; 
v___x_3940_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3935_, v_declHint_3936_, v___y_3937_, v___y_3938_);
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3941_);
lean_dec_ref(v___x_3940_);
v___x_3942_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3934_, v_a_3941_, v___y_3937_, v___y_3938_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3943_, lean_object* v_msg_3944_, lean_object* v_declHint_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_res_3949_; 
v_res_3949_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3943_, v_msg_3944_, v_declHint_3945_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v_ref_3943_);
return v_res_3949_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3950_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_3951_ = l_Lean_stringToMessageData(v___x_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3952_, lean_object* v_constName_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v___x_3957_; uint8_t v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3957_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3958_ = 0;
lean_inc(v_constName_3953_);
v___x_3959_ = l_Lean_MessageData_ofConstName(v_constName_3953_, v___x_3958_);
v___x_3960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3957_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
v___x_3961_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3960_);
lean_ctor_set(v___x_3962_, 1, v___x_3961_);
v___x_3963_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3952_, v___x_3962_, v_constName_3953_, v___y_3954_, v___y_3955_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3964_, lean_object* v_constName_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3964_, v_constName_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v_ref_3964_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object* v_constName_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v_ref_3974_; lean_object* v___x_3975_; 
v_ref_3974_ = lean_ctor_get(v___y_3971_, 2);
v___x_3975_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3974_, v_constName_3970_, v___y_3971_, v___y_3972_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3976_, v___y_3977_, v___y_3978_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object* v_constName_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v___x_3985_; lean_object* v_env_3986_; uint8_t v___x_3987_; lean_object* v___x_3988_; 
v___x_3985_ = lean_st_ref_get(v___y_3983_);
v_env_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc_ref(v_env_3986_);
lean_dec(v___x_3985_);
v___x_3987_ = 0;
lean_inc(v_constName_3981_);
v___x_3988_ = l_Lean_Environment_find_x3f(v_env_3986_, v_constName_3981_, v___x_3987_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3981_, v___y_3982_, v___y_3983_);
return v___x_3989_;
}
else
{
lean_object* v_val_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v_constName_3981_);
v_val_3990_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3988_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_val_3990_);
lean_dec(v___x_3988_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
lean_ctor_set_tag(v___x_3992_, 0);
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_val_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object* v_constName_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3998_, v___y_3999_, v___y_4000_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
return v_res_4002_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1(void){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0));
v___x_4005_ = l_Lean_stringToMessageData(v___x_4004_);
return v___x_4005_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3(void){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2));
v___x_4008_ = l_Lean_stringToMessageData(v___x_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* v_attrName_4009_, lean_object* v_catName_4010_, lean_object* v_declName_4011_, lean_object* v_stx_4012_, uint8_t v_kind_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___x_4037_; 
v___x_4037_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4012_, v_a_4014_, v_a_4015_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___y_4040_; lean_object* v___y_4041_; uint8_t v___x_4069_; uint8_t v___x_4070_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4037_, 1);
v___x_4069_ = 0;
v___x_4070_ = l_Lean_instBEqAttributeKind_beq(v_kind_4013_, v___x_4069_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4071_; 
lean_dec(v_a_4038_);
lean_dec(v_declName_4011_);
lean_dec(v_catName_4010_);
v___x_4071_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_attrName_4009_, v_kind_4013_, v_a_4014_, v_a_4015_);
return v___x_4071_;
}
else
{
lean_dec(v_attrName_4009_);
v___y_4040_ = v_a_4014_;
v___y_4041_ = v_a_4015_;
goto v___jp_4039_;
}
v___jp_4039_:
{
lean_object* v___x_4042_; 
lean_inc(v_declName_4011_);
v___x_4042_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_declName_4011_, v___y_4040_, v___y_4041_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4044_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_a_4043_);
lean_dec_ref_known(v___x_4042_, 1);
v___x_4044_ = l_Lean_ConstantInfo_type(v_a_4043_);
if (lean_obj_tag(v___x_4044_) == 4)
{
lean_object* v_declName_4045_; 
v_declName_4045_ = lean_ctor_get(v___x_4044_, 0);
lean_inc(v_declName_4045_);
lean_dec_ref_known(v___x_4044_, 2);
if (lean_obj_tag(v_declName_4045_) == 1)
{
lean_object* v_pre_4046_; 
v_pre_4046_ = lean_ctor_get(v_declName_4045_, 0);
lean_inc(v_pre_4046_);
if (lean_obj_tag(v_pre_4046_) == 1)
{
lean_object* v_pre_4047_; 
v_pre_4047_ = lean_ctor_get(v_pre_4046_, 0);
lean_inc(v_pre_4047_);
if (lean_obj_tag(v_pre_4047_) == 1)
{
lean_object* v_pre_4048_; 
v_pre_4048_ = lean_ctor_get(v_pre_4047_, 0);
if (lean_obj_tag(v_pre_4048_) == 0)
{
lean_object* v_str_4049_; lean_object* v_str_4050_; lean_object* v_str_4051_; lean_object* v___x_4052_; uint8_t v___x_4053_; 
v_str_4049_ = lean_ctor_get(v_declName_4045_, 1);
lean_inc_ref(v_str_4049_);
lean_dec_ref_known(v_declName_4045_, 2);
v_str_4050_ = lean_ctor_get(v_pre_4046_, 1);
lean_inc_ref(v_str_4050_);
lean_dec_ref_known(v_pre_4046_, 2);
v_str_4051_ = lean_ctor_get(v_pre_4047_, 1);
lean_inc_ref(v_str_4051_);
lean_dec_ref_known(v_pre_4047_, 2);
v___x_4052_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_4053_ = lean_string_dec_eq(v_str_4051_, v___x_4052_);
lean_dec_ref(v_str_4051_);
if (v___x_4053_ == 0)
{
lean_dec_ref(v_str_4050_);
lean_dec_ref(v_str_4049_);
lean_dec(v_a_4038_);
lean_dec(v_catName_4010_);
v___y_4024_ = v_a_4043_;
v___y_4025_ = v___y_4040_;
v___y_4026_ = v___y_4041_;
goto v___jp_4023_;
}
else
{
lean_object* v___x_4054_; uint8_t v___x_4055_; 
v___x_4054_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_4055_ = lean_string_dec_eq(v_str_4050_, v___x_4054_);
lean_dec_ref(v_str_4050_);
if (v___x_4055_ == 0)
{
lean_dec_ref(v_str_4049_);
lean_dec(v_a_4038_);
lean_dec(v_catName_4010_);
v___y_4024_ = v_a_4043_;
v___y_4025_ = v___y_4040_;
v___y_4026_ = v___y_4041_;
goto v___jp_4023_;
}
else
{
lean_object* v___x_4056_; uint8_t v___x_4057_; 
v___x_4056_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_4057_ = lean_string_dec_eq(v_str_4049_, v___x_4056_);
if (v___x_4057_ == 0)
{
uint8_t v___x_4058_; 
v___x_4058_ = lean_string_dec_eq(v_str_4049_, v___x_4054_);
lean_dec_ref(v_str_4049_);
if (v___x_4058_ == 0)
{
lean_dec(v_a_4038_);
lean_dec(v_catName_4010_);
v___y_4024_ = v_a_4043_;
v___y_4025_ = v___y_4040_;
v___y_4026_ = v___y_4041_;
goto v___jp_4023_;
}
else
{
lean_object* v___x_4059_; 
lean_dec(v_a_4043_);
lean_inc(v_declName_4011_);
lean_inc(v_catName_4010_);
v___x_4059_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_4010_, v_declName_4011_, v_a_4038_, v___y_4040_, v___y_4041_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_dec_ref_known(v___x_4059_, 1);
v___y_4018_ = v___y_4040_;
v___y_4019_ = v___y_4041_;
goto v___jp_4017_;
}
else
{
lean_dec(v_declName_4011_);
lean_dec(v_catName_4010_);
return v___x_4059_;
}
}
}
else
{
lean_object* v___x_4060_; 
lean_dec_ref(v_str_4049_);
lean_dec(v_a_4043_);
lean_inc(v_declName_4011_);
lean_inc(v_catName_4010_);
v___x_4060_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_4010_, v_declName_4011_, v_a_4038_, v___y_4040_, v___y_4041_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_dec_ref_known(v___x_4060_, 1);
v___y_4018_ = v___y_4040_;
v___y_4019_ = v___y_4041_;
goto v___jp_4017_;
}
else
{
lean_dec(v_declName_4011_);
lean_dec(v_catName_4010_);
return v___x_4060_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_4047_, 2);
lean_dec_ref_known(v_pre_4046_, 2);
lean_dec_ref_known(v_declName_4045_, 2);
lean_dec(v_a_4038_);
lean_dec(v_catName_4010_);
v___y_4024_ = v_a_4043_;
v___y_4025_ = v___y_4040_;
v___y_4026_ = v___y_4041_;
goto v___jp_4023_;
}
}
else
{
lean_dec_ref_known(v_pre_4046_, 2);
lean_dec(v_pre_4047_);
lean_dec_ref_known(v_declName_4045_, 2);
lean_dec(v_a_4038_);
lean_dec(v_catName_4010_);
v___y_4024_ = v_a_4043_;
v___y_4025_ = v___y_4040_;
v___y_4026_ = v___y_4041_;
goto v___jp_4023_;
}
}
else
{
lean_dec(v_pre_4046_);
lean_dec_ref_known(v_declName_4045_, 2);
lean_dec(v_a_4038_);
lean_dec(v_catName_4010_);
v___y_4024_ = v_a_4043_;
v___y_4025_ = v___y_4040_;
v___y_4026_ = v___y_4041_;
goto v___jp_4023_;
}
}
else
{
lean_dec(v_declName_4045_);
lean_dec(v_a_4038_);
lean_dec(v_catName_4010_);
v___y_4024_ = v_a_4043_;
v___y_4025_ = v___y_4040_;
v___y_4026_ = v___y_4041_;
goto v___jp_4023_;
}
}
else
{
lean_dec_ref(v___x_4044_);
lean_dec(v_a_4038_);
lean_dec(v_catName_4010_);
v___y_4024_ = v_a_4043_;
v___y_4025_ = v___y_4040_;
v___y_4026_ = v___y_4041_;
goto v___jp_4023_;
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec(v_a_4038_);
lean_dec(v_declName_4011_);
lean_dec(v_catName_4010_);
v_a_4061_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4042_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4042_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
else
{
lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4079_; 
lean_dec(v_declName_4011_);
lean_dec(v_catName_4010_);
lean_dec(v_attrName_4009_);
v_a_4072_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4074_ = v___x_4037_;
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___x_4037_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4075_ == 0)
{
v___x_4077_ = v___x_4074_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4072_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
v___jp_4017_:
{
lean_object* v___x_4020_; 
lean_inc(v_declName_4011_);
v___x_4020_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_4011_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4020_) == 0)
{
uint8_t v___x_4021_; lean_object* v___x_4022_; 
lean_dec_ref_known(v___x_4020_, 1);
v___x_4021_ = 1;
v___x_4022_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4010_, v_declName_4011_, v___x_4021_, v___y_4018_, v___y_4019_);
return v___x_4022_;
}
else
{
lean_dec(v_declName_4011_);
lean_dec(v_catName_4010_);
return v___x_4020_;
}
}
v___jp_4023_:
{
lean_object* v___x_4027_; uint8_t v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4027_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
v___x_4028_ = 0;
v___x_4029_ = l_Lean_MessageData_ofConstName(v_declName_4011_, v___x_4028_);
v___x_4030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4027_);
lean_ctor_set(v___x_4030_, 1, v___x_4029_);
v___x_4031_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
v___x_4032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4030_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = l_Lean_ConstantInfo_type(v___y_4024_);
lean_dec_ref(v___y_4024_);
v___x_4034_ = l_Lean_indentExpr(v___x_4033_);
v___x_4035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4032_);
lean_ctor_set(v___x_4035_, 1, v___x_4034_);
v___x_4036_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4035_, v___y_4025_, v___y_4026_);
return v___x_4036_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* v_attrName_4080_, lean_object* v_catName_4081_, lean_object* v_declName_4082_, lean_object* v_stx_4083_, lean_object* v_kind_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_){
_start:
{
uint8_t v_kind_boxed_4088_; lean_object* v_res_4089_; 
v_kind_boxed_4088_ = lean_unbox(v_kind_4084_);
v_res_4089_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_4080_, v_catName_4081_, v_declName_4082_, v_stx_4083_, v_kind_boxed_4088_, v_a_4085_, v_a_4086_);
lean_dec(v_a_4086_);
lean_dec_ref(v_a_4085_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object* v_00_u03b1_4090_, lean_object* v_name_4091_, uint8_t v_kind_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v___x_4096_; 
v___x_4096_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_4091_, v_kind_4092_, v___y_4093_, v___y_4094_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b1_4097_, lean_object* v_name_4098_, lean_object* v_kind_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
uint8_t v_kind_boxed_4103_; lean_object* v_res_4104_; 
v_kind_boxed_4103_ = lean_unbox(v_kind_4099_);
v_res_4104_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(v_00_u03b1_4097_, v_name_4098_, v_kind_boxed_4103_, v___y_4100_, v___y_4101_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object* v_00_u03b1_4105_, lean_object* v_constName_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_4106_, v___y_4107_, v___y_4108_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object* v_00_u03b1_4111_, lean_object* v_constName_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(v_00_u03b1_4111_, v_constName_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4117_, lean_object* v_ref_4118_, lean_object* v_constName_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_4118_, v_constName_4119_, v___y_4120_, v___y_4121_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4124_, lean_object* v_ref_4125_, lean_object* v_constName_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(v_00_u03b1_4124_, v_ref_4125_, v_constName_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v_ref_4125_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4131_, lean_object* v_ref_4132_, lean_object* v_msg_4133_, lean_object* v_declHint_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_4132_, v_msg_4133_, v_declHint_4134_, v___y_4135_, v___y_4136_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4139_, lean_object* v_ref_4140_, lean_object* v_msg_4141_, lean_object* v_declHint_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4139_, v_ref_4140_, v_msg_4141_, v_declHint_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v_ref_4140_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_4147_, lean_object* v_declHint_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v___x_4152_; 
v___x_4152_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_4147_, v_declHint_4148_, v___y_4150_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_4153_, lean_object* v_declHint_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_4153_, v_declHint_4154_, v___y_4155_, v___y_4156_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_4159_, lean_object* v_ref_4160_, lean_object* v_msg_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v___x_4165_; 
v___x_4165_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4160_, v_msg_4161_, v___y_4162_, v___y_4163_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_4166_, lean_object* v_ref_4167_, lean_object* v_msg_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_4166_, v_ref_4167_, v_msg_4168_, v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v_ref_4167_);
return v_res_4172_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2(void){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0));
v___x_4180_ = l_Lean_mkAtom(v___x_4179_);
return v___x_4180_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4181_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2);
v___x_4182_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4183_ = lean_array_push(v___x_4182_, v___x_4181_);
return v___x_4183_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8(void){
_start:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4192_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7));
v___x_4193_ = l_Lean_mkAtom(v___x_4192_);
return v___x_4193_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9(void){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4194_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8);
v___x_4195_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4196_ = lean_array_push(v___x_4195_, v___x_4194_);
return v___x_4196_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4197_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9);
v___x_4198_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6));
v___x_4199_ = lean_box(2);
v___x_4200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4199_);
lean_ctor_set(v___x_4200_, 1, v___x_4198_);
lean_ctor_set(v___x_4200_, 2, v___x_4197_);
return v___x_4200_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4201_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10);
v___x_4202_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3);
v___x_4203_ = lean_array_push(v___x_4202_, v___x_4201_);
return v___x_4203_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4204_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11);
v___x_4205_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1));
v___x_4206_ = lean_box(2);
v___x_4207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
lean_ctor_set(v___x_4207_, 1, v___x_4205_);
lean_ctor_set(v___x_4207_, 2, v___x_4204_);
return v___x_4207_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4208_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12);
v___x_4209_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4210_ = lean_array_push(v___x_4209_, v___x_4208_);
return v___x_4210_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14(void){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4211_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13);
v___x_4212_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_4213_ = lean_box(2);
v___x_4214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
lean_ctor_set(v___x_4214_, 1, v___x_4212_);
lean_ctor_set(v___x_4214_, 2, v___x_4211_);
return v___x_4214_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4215_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14);
v___x_4216_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4217_ = lean_array_push(v___x_4216_, v___x_4215_);
return v___x_4217_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4218_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15);
v___x_4219_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_4220_ = lean_box(2);
v___x_4221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
lean_ctor_set(v___x_4221_, 1, v___x_4219_);
lean_ctor_set(v___x_4221_, 2, v___x_4218_);
return v___x_4221_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4222_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16);
v___x_4223_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4224_ = lean_array_push(v___x_4223_, v___x_4222_);
return v___x_4224_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4225_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17);
v___x_4226_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_4227_ = lean_box(2);
v___x_4228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
lean_ctor_set(v___x_4228_, 1, v___x_4226_);
lean_ctor_set(v___x_4228_, 2, v___x_4225_);
return v___x_4228_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4229_; 
v___x_4229_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object* v_attrName_4230_, lean_object* v_decl_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4235_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_4236_ = l_Lean_MessageData_ofName(v_attrName_4230_);
v___x_4237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4237_, 0, v___x_4235_);
lean_ctor_set(v___x_4237_, 1, v___x_4236_);
v___x_4238_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_4239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4237_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4239_, v___y_4232_, v___y_4233_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object* v_attrName_4241_, lean_object* v_decl_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_4241_, v_decl_4242_, v___y_4243_, v___y_4244_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec(v_decl_4242_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object* v_attrName_4247_, lean_object* v_catName_4248_, lean_object* v_declName_4249_, lean_object* v_stx_4250_, uint8_t v_kind_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v___x_4255_; 
v___x_4255_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_4247_, v_catName_4248_, v_declName_4249_, v_stx_4250_, v_kind_4251_, v___y_4252_, v___y_4253_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object* v_attrName_4256_, lean_object* v_catName_4257_, lean_object* v_declName_4258_, lean_object* v_stx_4259_, lean_object* v_kind_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
uint8_t v_kind_boxed_4264_; lean_object* v_res_4265_; 
v_kind_boxed_4264_ = lean_unbox(v_kind_4260_);
v_res_4265_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_4256_, v_catName_4257_, v_declName_4258_, v_stx_4259_, v_kind_boxed_4264_, v___y_4261_, v___y_4262_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
return v_res_4265_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1(void){
_start:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4267_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__0));
v___x_4268_ = lean_mk_io_user_error(v___x_4267_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* v_attrName_4271_, lean_object* v_declName_4272_, uint8_t v_behavior_4273_, lean_object* v_ref_4274_){
_start:
{
if (lean_obj_tag(v_declName_4272_) == 1)
{
lean_object* v_pre_4279_; 
v_pre_4279_ = lean_ctor_get(v_declName_4272_, 0);
if (lean_obj_tag(v_pre_4279_) == 1)
{
lean_object* v_pre_4280_; 
v_pre_4280_ = lean_ctor_get(v_pre_4279_, 0);
if (lean_obj_tag(v_pre_4280_) == 1)
{
lean_object* v_pre_4281_; 
v_pre_4281_ = lean_ctor_get(v_pre_4280_, 0);
if (lean_obj_tag(v_pre_4281_) == 1)
{
lean_object* v_pre_4282_; 
v_pre_4282_ = lean_ctor_get(v_pre_4281_, 0);
if (lean_obj_tag(v_pre_4282_) == 0)
{
lean_object* v_str_4283_; lean_object* v_str_4284_; lean_object* v_str_4285_; lean_object* v_str_4286_; lean_object* v___x_4287_; uint8_t v___x_4288_; 
v_str_4283_ = lean_ctor_get(v_declName_4272_, 1);
v_str_4284_ = lean_ctor_get(v_pre_4279_, 1);
v_str_4285_ = lean_ctor_get(v_pre_4280_, 1);
v_str_4286_ = lean_ctor_get(v_pre_4281_, 1);
v___x_4287_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_4288_ = lean_string_dec_eq(v_str_4286_, v___x_4287_);
if (v___x_4288_ == 0)
{
lean_dec_ref_known(v_declName_4272_, 2);
lean_dec(v_ref_4274_);
lean_dec(v_attrName_4271_);
goto v___jp_4276_;
}
else
{
lean_object* v___x_4289_; uint8_t v___x_4290_; 
v___x_4289_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_4290_ = lean_string_dec_eq(v_str_4285_, v___x_4289_);
if (v___x_4290_ == 0)
{
lean_dec_ref_known(v_declName_4272_, 2);
lean_dec(v_ref_4274_);
lean_dec(v_attrName_4271_);
goto v___jp_4276_;
}
else
{
lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4291_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__2));
v___x_4292_ = lean_string_dec_eq(v_str_4284_, v___x_4291_);
if (v___x_4292_ == 0)
{
lean_dec_ref_known(v_declName_4272_, 2);
lean_dec(v_ref_4274_);
lean_dec(v_attrName_4271_);
goto v___jp_4276_;
}
else
{
lean_object* v___f_4293_; lean_object* v___x_4294_; lean_object* v_catName_4295_; lean_object* v___f_4296_; lean_object* v___x_4297_; 
lean_inc_n(v_attrName_4271_, 2);
v___f_4293_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4293_, 0, v_attrName_4271_);
v___x_4294_ = lean_box(0);
lean_inc_ref(v_str_4283_);
v_catName_4295_ = l_Lean_Name_str___override(v___x_4294_, v_str_4283_);
lean_inc(v_catName_4295_);
v___f_4296_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed), 8, 2);
lean_closure_set(v___f_4296_, 0, v_attrName_4271_);
lean_closure_set(v___f_4296_, 1, v_catName_4295_);
v___x_4297_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_4295_, v_declName_4272_, v_behavior_4273_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v___x_4298_; uint8_t v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
lean_dec_ref_known(v___x_4297_, 1);
v___x_4298_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__3));
v___x_4299_ = 1;
v___x_4300_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4300_, 0, v_ref_4274_);
lean_ctor_set(v___x_4300_, 1, v_attrName_4271_);
lean_ctor_set(v___x_4300_, 2, v___x_4298_);
lean_ctor_set_uint8(v___x_4300_, sizeof(void*)*3, v___x_4299_);
v___x_4301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4300_);
lean_ctor_set(v___x_4301_, 1, v___f_4296_);
lean_ctor_set(v___x_4301_, 2, v___f_4293_);
v___x_4302_ = l_Lean_registerBuiltinAttribute(v___x_4301_);
return v___x_4302_;
}
else
{
lean_dec_ref(v___f_4296_);
lean_dec_ref(v___f_4293_);
lean_dec(v_ref_4274_);
lean_dec(v_attrName_4271_);
return v___x_4297_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_declName_4272_, 2);
lean_dec(v_ref_4274_);
lean_dec(v_attrName_4271_);
goto v___jp_4276_;
}
}
else
{
lean_dec_ref_known(v_declName_4272_, 2);
lean_dec(v_ref_4274_);
lean_dec(v_attrName_4271_);
goto v___jp_4276_;
}
}
else
{
lean_dec_ref_known(v_declName_4272_, 2);
lean_dec(v_ref_4274_);
lean_dec(v_attrName_4271_);
goto v___jp_4276_;
}
}
else
{
lean_dec_ref_known(v_declName_4272_, 2);
lean_dec(v_ref_4274_);
lean_dec(v_attrName_4271_);
goto v___jp_4276_;
}
}
else
{
lean_dec(v_ref_4274_);
lean_dec(v_declName_4272_);
lean_dec(v_attrName_4271_);
goto v___jp_4276_;
}
v___jp_4276_:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4277_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___closed__1, &l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
v___x_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4277_);
return v___x_4278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* v_attrName_4303_, lean_object* v_declName_4304_, lean_object* v_behavior_4305_, lean_object* v_ref_4306_, lean_object* v_a_4307_){
_start:
{
uint8_t v_behavior_boxed_4308_; lean_object* v_res_4309_; 
v_behavior_boxed_4308_ = lean_unbox(v_behavior_4305_);
v_res_4309_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_4303_, v_declName_4304_, v_behavior_boxed_4308_, v_ref_4306_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object* v_kind_4310_, lean_object* v_x_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v___x_4315_; lean_object* v_env_4316_; lean_object* v_nextMacroScope_4317_; lean_object* v_ngen_4318_; lean_object* v_auxDeclNGen_4319_; lean_object* v_traceState_4320_; lean_object* v_recordedDeps_4321_; lean_object* v_messages_4322_; lean_object* v_infoState_4323_; lean_object* v_snapshotTasks_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4336_; 
v___x_4315_ = lean_st_ref_take(v___y_4313_);
v_env_4316_ = lean_ctor_get(v___x_4315_, 0);
v_nextMacroScope_4317_ = lean_ctor_get(v___x_4315_, 1);
v_ngen_4318_ = lean_ctor_get(v___x_4315_, 2);
v_auxDeclNGen_4319_ = lean_ctor_get(v___x_4315_, 3);
v_traceState_4320_ = lean_ctor_get(v___x_4315_, 4);
v_recordedDeps_4321_ = lean_ctor_get(v___x_4315_, 6);
v_messages_4322_ = lean_ctor_get(v___x_4315_, 7);
v_infoState_4323_ = lean_ctor_get(v___x_4315_, 8);
v_snapshotTasks_4324_ = lean_ctor_get(v___x_4315_, 9);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4336_ == 0)
{
lean_object* v_unused_4337_; 
v_unused_4337_ = lean_ctor_get(v___x_4315_, 5);
lean_dec(v_unused_4337_);
v___x_4326_ = v___x_4315_;
v_isShared_4327_ = v_isSharedCheck_4336_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_snapshotTasks_4324_);
lean_inc(v_infoState_4323_);
lean_inc(v_messages_4322_);
lean_inc(v_recordedDeps_4321_);
lean_inc(v_traceState_4320_);
lean_inc(v_auxDeclNGen_4319_);
lean_inc(v_ngen_4318_);
lean_inc(v_nextMacroScope_4317_);
lean_inc(v_env_4316_);
lean_dec(v___x_4315_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4336_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4332_; 
v___x_4328_ = lean_box(0);
v___x_4329_ = l_Lean_Parser_addSyntaxNodeKind(v_env_4316_, v_kind_4310_);
v___x_4330_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 5, v___x_4330_);
lean_ctor_set(v___x_4326_, 0, v___x_4329_);
v___x_4332_ = v___x_4326_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4329_);
lean_ctor_set(v_reuseFailAlloc_4335_, 1, v_nextMacroScope_4317_);
lean_ctor_set(v_reuseFailAlloc_4335_, 2, v_ngen_4318_);
lean_ctor_set(v_reuseFailAlloc_4335_, 3, v_auxDeclNGen_4319_);
lean_ctor_set(v_reuseFailAlloc_4335_, 4, v_traceState_4320_);
lean_ctor_set(v_reuseFailAlloc_4335_, 5, v___x_4330_);
lean_ctor_set(v_reuseFailAlloc_4335_, 6, v_recordedDeps_4321_);
lean_ctor_set(v_reuseFailAlloc_4335_, 7, v_messages_4322_);
lean_ctor_set(v_reuseFailAlloc_4335_, 8, v_infoState_4323_);
lean_ctor_set(v_reuseFailAlloc_4335_, 9, v_snapshotTasks_4324_);
v___x_4332_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = lean_st_ref_put(v___y_4313_, v___x_4332_);
v___x_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4328_);
return v___x_4334_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object* v_kind_4338_, lean_object* v_x_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_4338_, v_x_4339_, v___y_4340_, v___y_4341_);
lean_dec(v___y_4341_);
lean_dec_ref(v___y_4340_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_4344_, lean_object* v_keys_4345_, lean_object* v_vals_4346_, lean_object* v_i_4347_, lean_object* v_acc_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
lean_object* v___x_4352_; uint8_t v___x_4353_; 
v___x_4352_ = lean_array_get_size(v_keys_4345_);
v___x_4353_ = lean_nat_dec_lt(v_i_4347_, v___x_4352_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; 
lean_dec(v_i_4347_);
lean_dec_ref(v_f_4344_);
v___x_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4354_, 0, v_acc_4348_);
return v___x_4354_;
}
else
{
lean_object* v_k_4355_; lean_object* v_v_4356_; lean_object* v___x_4357_; 
v_k_4355_ = lean_array_fget_borrowed(v_keys_4345_, v_i_4347_);
v_v_4356_ = lean_array_fget_borrowed(v_vals_4346_, v_i_4347_);
lean_inc_ref(v_f_4344_);
lean_inc(v___y_4350_);
lean_inc_ref(v___y_4349_);
lean_inc(v_v_4356_);
lean_inc(v_k_4355_);
v___x_4357_ = lean_apply_6(v_f_4344_, v_acc_4348_, v_k_4355_, v_v_4356_, v___y_4349_, v___y_4350_, lean_box(0));
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4357_, 1);
v___x_4359_ = lean_unsigned_to_nat(1u);
v___x_4360_ = lean_nat_add(v_i_4347_, v___x_4359_);
lean_dec(v_i_4347_);
v_i_4347_ = v___x_4360_;
v_acc_4348_ = v_a_4358_;
goto _start;
}
else
{
lean_dec(v_i_4347_);
lean_dec_ref(v_f_4344_);
return v___x_4357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_4362_, lean_object* v_keys_4363_, lean_object* v_vals_4364_, lean_object* v_i_4365_, lean_object* v_acc_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4362_, v_keys_4363_, v_vals_4364_, v_i_4365_, v_acc_4366_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec_ref(v_vals_4364_);
lean_dec_ref(v_keys_4363_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_4371_, lean_object* v_as_4372_, size_t v_i_4373_, size_t v_stop_4374_, lean_object* v_b_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v_a_4380_; lean_object* v___y_4385_; uint8_t v___x_4387_; 
v___x_4387_ = lean_usize_dec_eq(v_i_4373_, v_stop_4374_);
if (v___x_4387_ == 0)
{
lean_object* v___x_4388_; 
v___x_4388_ = lean_array_uget_borrowed(v_as_4372_, v_i_4373_);
switch(lean_obj_tag(v___x_4388_))
{
case 0:
{
lean_object* v_key_4389_; lean_object* v_val_4390_; lean_object* v___x_4391_; 
v_key_4389_ = lean_ctor_get(v___x_4388_, 0);
v_val_4390_ = lean_ctor_get(v___x_4388_, 1);
lean_inc_ref(v_f_4371_);
lean_inc(v___y_4377_);
lean_inc_ref(v___y_4376_);
lean_inc(v_val_4390_);
lean_inc(v_key_4389_);
v___x_4391_ = lean_apply_6(v_f_4371_, v_b_4375_, v_key_4389_, v_val_4390_, v___y_4376_, v___y_4377_, lean_box(0));
v___y_4385_ = v___x_4391_;
goto v___jp_4384_;
}
case 1:
{
lean_object* v_node_4392_; lean_object* v___x_4393_; 
v_node_4392_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_node_4392_);
lean_inc_ref(v_f_4371_);
v___x_4393_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4371_, v_node_4392_, v_b_4375_, v___y_4376_, v___y_4377_);
v___y_4385_ = v___x_4393_;
goto v___jp_4384_;
}
default: 
{
v_a_4380_ = v_b_4375_;
goto v___jp_4379_;
}
}
}
else
{
lean_object* v___x_4394_; 
lean_dec_ref(v_f_4371_);
v___x_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4394_, 0, v_b_4375_);
return v___x_4394_;
}
v___jp_4379_:
{
size_t v___x_4381_; size_t v___x_4382_; 
v___x_4381_ = ((size_t)1ULL);
v___x_4382_ = lean_usize_add(v_i_4373_, v___x_4381_);
v_i_4373_ = v___x_4382_;
v_b_4375_ = v_a_4380_;
goto _start;
}
v___jp_4384_:
{
if (lean_obj_tag(v___y_4385_) == 0)
{
lean_object* v_a_4386_; 
v_a_4386_ = lean_ctor_get(v___y_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v___y_4385_, 1);
v_a_4380_ = v_a_4386_;
goto v___jp_4379_;
}
else
{
lean_dec_ref(v_f_4371_);
return v___y_4385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object* v_f_4395_, lean_object* v_x_4396_, lean_object* v_x_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_){
_start:
{
if (lean_obj_tag(v_x_4396_) == 0)
{
lean_object* v_es_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4414_; 
v_es_4401_ = lean_ctor_get(v_x_4396_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v_x_4396_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4403_ = v_x_4396_;
v_isShared_4404_ = v_isSharedCheck_4414_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_es_4401_);
lean_dec(v_x_4396_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4414_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; uint8_t v___x_4407_; 
v___x_4405_ = lean_unsigned_to_nat(0u);
v___x_4406_ = lean_array_get_size(v_es_4401_);
v___x_4407_ = lean_nat_dec_lt(v___x_4405_, v___x_4406_);
if (v___x_4407_ == 0)
{
lean_object* v___x_4409_; 
lean_dec_ref(v_es_4401_);
lean_dec_ref(v_f_4395_);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v_x_4397_);
v___x_4409_ = v___x_4403_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_x_4397_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
else
{
size_t v___x_4411_; size_t v___x_4412_; lean_object* v___x_4413_; 
lean_del_object(v___x_4403_);
v___x_4411_ = ((size_t)0ULL);
v___x_4412_ = lean_usize_of_nat(v___x_4406_);
v___x_4413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4395_, v_es_4401_, v___x_4411_, v___x_4412_, v_x_4397_, v___y_4398_, v___y_4399_);
lean_dec_ref(v_es_4401_);
return v___x_4413_;
}
}
}
else
{
lean_object* v_ks_4415_; lean_object* v_vs_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
v_ks_4415_ = lean_ctor_get(v_x_4396_, 0);
lean_inc_ref(v_ks_4415_);
v_vs_4416_ = lean_ctor_get(v_x_4396_, 1);
lean_inc_ref(v_vs_4416_);
lean_dec_ref_known(v_x_4396_, 2);
v___x_4417_ = lean_unsigned_to_nat(0u);
v___x_4418_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4395_, v_ks_4415_, v_vs_4416_, v___x_4417_, v_x_4397_, v___y_4398_, v___y_4399_);
lean_dec_ref(v_vs_4416_);
lean_dec_ref(v_ks_4415_);
return v___x_4418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_4419_, lean_object* v_x_4420_, lean_object* v_x_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4419_, v_x_4420_, v_x_4421_, v___y_4422_, v___y_4423_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_4426_, lean_object* v_as_4427_, lean_object* v_i_4428_, lean_object* v_stop_4429_, lean_object* v_b_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
size_t v_i_boxed_4434_; size_t v_stop_boxed_4435_; lean_object* v_res_4436_; 
v_i_boxed_4434_ = lean_unbox_usize(v_i_4428_);
lean_dec(v_i_4428_);
v_stop_boxed_4435_ = lean_unbox_usize(v_stop_4429_);
lean_dec(v_stop_4429_);
v_res_4436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4426_, v_as_4427_, v_i_boxed_4434_, v_stop_boxed_4435_, v_b_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec_ref(v_as_4427_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object* v_f_4437_, lean_object* v_x_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v___x_4444_; 
lean_inc(v___y_4442_);
lean_inc_ref(v___y_4441_);
v___x_4444_ = lean_apply_5(v_f_4437_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, lean_box(0));
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object* v_f_4445_, lean_object* v_x_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4445_, v_x_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object* v_map_4453_, lean_object* v_f_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v___f_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___f_4458_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4458_, 0, v_f_4454_);
v___x_4459_ = lean_box(0);
v___x_4460_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v___f_4458_, v_map_4453_, v___x_4459_, v___y_4455_, v___y_4456_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object* v_map_4461_, lean_object* v_f_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4461_, v_f_4462_, v___y_4463_, v___y_4464_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
return v_res_4466_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4468_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0));
v___x_4469_ = l_Lean_stringToMessageData(v___x_4468_);
return v___x_4469_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_4471_ = l_Lean_stringToMessageData(v___x_4470_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t v_attrKind_4472_, lean_object* v_declName_4473_, lean_object* v_as_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
if (lean_obj_tag(v_as_4474_) == 0)
{
lean_object* v___x_4478_; lean_object* v___x_4479_; 
lean_dec(v_declName_4473_);
v___x_4478_ = lean_box(0);
v___x_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
return v___x_4479_;
}
else
{
lean_object* v_head_4480_; lean_object* v_tail_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4508_; 
v_head_4480_ = lean_ctor_get(v_as_4474_, 0);
v_tail_4481_ = lean_ctor_get(v_as_4474_, 1);
v_isSharedCheck_4508_ = !lean_is_exclusive(v_as_4474_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4483_ = v_as_4474_;
v_isShared_4484_ = v_isSharedCheck_4508_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_tail_4481_);
lean_inc(v_head_4480_);
lean_dec(v_as_4474_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4508_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
uint8_t v___x_4485_; lean_object* v___x_4486_; 
v___x_4485_ = 0;
v___x_4486_ = l_Lean_Parser_addToken(v_head_4480_, v_attrKind_4472_, v___y_4475_, v___y_4476_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_dec_ref_known(v___x_4486_, 1);
lean_del_object(v___x_4483_);
v_as_4474_ = v_tail_4481_;
goto _start;
}
else
{
lean_object* v_a_4488_; uint8_t v___x_4489_; 
lean_dec(v_tail_4481_);
v_a_4488_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4488_);
v___x_4489_ = l_Lean_Exception_isInterrupt(v_a_4488_);
if (v___x_4489_ == 0)
{
uint8_t v___x_4490_; 
lean_inc(v_a_4488_);
v___x_4490_ = l_Lean_Exception_isRuntime(v_a_4488_);
if (v___x_4490_ == 0)
{
if (lean_obj_tag(v_a_4488_) == 0)
{
lean_object* v_msg_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4506_; 
lean_dec_ref_known(v___x_4486_, 1);
v_msg_4491_ = lean_ctor_get(v_a_4488_, 1);
v_isSharedCheck_4506_ = !lean_is_exclusive(v_a_4488_);
if (v_isSharedCheck_4506_ == 0)
{
lean_object* v_unused_4507_; 
v_unused_4507_ = lean_ctor_get(v_a_4488_, 0);
lean_dec(v_unused_4507_);
v___x_4493_ = v_a_4488_;
v_isShared_4494_ = v_isSharedCheck_4506_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_msg_4491_);
lean_dec(v_a_4488_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4506_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4498_; 
v___x_4495_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1);
v___x_4496_ = l_Lean_MessageData_ofConstName(v_declName_4473_, v___x_4485_);
if (v_isShared_4494_ == 0)
{
lean_ctor_set_tag(v___x_4493_, 7);
lean_ctor_set(v___x_4493_, 1, v___x_4496_);
lean_ctor_set(v___x_4493_, 0, v___x_4495_);
v___x_4498_ = v___x_4493_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4495_);
lean_ctor_set(v_reuseFailAlloc_4505_, 1, v___x_4496_);
v___x_4498_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
lean_object* v___x_4499_; lean_object* v___x_4501_; 
v___x_4499_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2);
if (v_isShared_4484_ == 0)
{
lean_ctor_set_tag(v___x_4483_, 7);
lean_ctor_set(v___x_4483_, 1, v___x_4499_);
lean_ctor_set(v___x_4483_, 0, v___x_4498_);
v___x_4501_ = v___x_4483_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4498_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v___x_4499_);
v___x_4501_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4501_);
lean_ctor_set(v___x_4502_, 1, v_msg_4491_);
v___x_4503_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4502_, v___y_4475_, v___y_4476_);
return v___x_4503_;
}
}
}
}
else
{
lean_dec(v_a_4488_);
lean_del_object(v___x_4483_);
lean_dec(v_declName_4473_);
return v___x_4486_;
}
}
else
{
lean_dec(v_a_4488_);
lean_del_object(v___x_4483_);
lean_dec(v_declName_4473_);
return v___x_4486_;
}
}
else
{
lean_dec(v_a_4488_);
lean_del_object(v___x_4483_);
lean_dec(v_declName_4473_);
return v___x_4486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object* v_attrKind_4509_, lean_object* v_declName_4510_, lean_object* v_as_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
uint8_t v_attrKind_boxed_4515_; lean_object* v_res_4516_; 
v_attrKind_boxed_4515_ = lean_unbox(v_attrKind_4509_);
v_res_4516_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_boxed_4515_, v_declName_4510_, v_as_4511_, v___y_4512_, v___y_4513_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object* v_catName_4518_, lean_object* v_declName_4519_, lean_object* v_stx_4520_, uint8_t v_attrKind_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v___f_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___f_4525_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0));
v___x_4526_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4527_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4520_, v_a_4522_, v_a_4523_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4529_; lean_object* v_env_4530_; lean_object* v___x_4531_; lean_object* v_ext_4532_; lean_object* v_toEnvExtension_4533_; lean_object* v_asyncMode_4534_; uint8_t v___x_4535_; lean_object* v___x_4536_; lean_object* v_categories_4537_; lean_object* v___x_4538_; lean_object* v_env_4539_; lean_object* v_ref_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
lean_inc(v_a_4528_);
lean_dec_ref_known(v___x_4527_, 1);
v___x_4529_ = lean_st_ref_get(v_a_4523_);
v_env_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc_ref(v_env_4530_);
lean_dec(v___x_4529_);
v___x_4531_ = l_Lean_Parser_parserExtension;
v_ext_4532_ = lean_ctor_get(v___x_4531_, 1);
v_toEnvExtension_4533_ = lean_ctor_get(v_ext_4532_, 0);
v_asyncMode_4534_ = lean_ctor_get(v_toEnvExtension_4533_, 2);
v___x_4535_ = 0;
v___x_4536_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4526_, v___x_4531_, v_env_4530_, v_asyncMode_4534_, v___x_4535_);
v_categories_4537_ = lean_ctor_get(v___x_4536_, 2);
lean_inc_ref_n(v_categories_4537_, 2);
lean_dec(v___x_4536_);
v___x_4538_ = lean_st_ref_get(v_a_4523_);
v_env_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc_ref(v_env_4539_);
lean_dec(v___x_4538_);
v_ref_4540_ = lean_ctor_get(v_a_4522_, 2);
v___x_4541_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4522_);
v___x_4542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4542_, 0, v_env_4539_);
lean_ctor_set(v___x_4542_, 1, v___x_4541_);
lean_inc(v_declName_4519_);
v___x_4543_ = l_Lean_Parser_mkParserOfConstant(v_categories_4537_, v_declName_4519_, v___x_4542_);
lean_dec_ref_known(v___x_4542_, 2);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_object* v_a_4544_; lean_object* v_snd_4545_; lean_object* v_info_4546_; lean_object* v_fst_4547_; lean_object* v_collectTokens_4548_; lean_object* v_collectKinds_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
lean_inc(v_a_4544_);
lean_dec_ref_known(v___x_4543_, 1);
v_snd_4545_ = lean_ctor_get(v_a_4544_, 1);
lean_inc(v_snd_4545_);
v_info_4546_ = lean_ctor_get(v_snd_4545_, 0);
v_fst_4547_ = lean_ctor_get(v_a_4544_, 0);
lean_inc(v_fst_4547_);
lean_dec(v_a_4544_);
v_collectTokens_4548_ = lean_ctor_get(v_info_4546_, 0);
v_collectKinds_4549_ = lean_ctor_get(v_info_4546_, 1);
v___x_4550_ = lean_box(0);
lean_inc_ref(v_collectTokens_4548_);
v___x_4551_ = lean_apply_1(v_collectTokens_4548_, v___x_4550_);
lean_inc(v_declName_4519_);
v___x_4552_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4521_, v_declName_4519_, v___x_4551_, v_a_4522_, v_a_4523_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
lean_dec_ref_known(v___x_4552_, 1);
v___x_4553_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
lean_inc_ref(v_collectKinds_4549_);
v___x_4554_ = lean_apply_1(v_collectKinds_4549_, v___x_4553_);
v___x_4555_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v___x_4554_, v___f_4525_, v_a_4522_, v_a_4523_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v___x_4556_; uint8_t v___x_4557_; uint8_t v___x_4558_; lean_object* v___x_4559_; 
lean_dec_ref_known(v___x_4555_, 1);
lean_inc(v_a_4528_);
lean_inc(v_snd_4545_);
lean_inc_n(v_declName_4519_, 2);
lean_inc_n(v_catName_4518_, 2);
v___x_4556_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_4556_, 0, v_catName_4518_);
lean_ctor_set(v___x_4556_, 1, v_declName_4519_);
lean_ctor_set(v___x_4556_, 2, v_snd_4545_);
lean_ctor_set(v___x_4556_, 3, v_a_4528_);
v___x_4557_ = lean_unbox(v_fst_4547_);
lean_ctor_set_uint8(v___x_4556_, sizeof(void*)*4, v___x_4557_);
v___x_4558_ = lean_unbox(v_fst_4547_);
lean_dec(v_fst_4547_);
v___x_4559_ = l_Lean_Parser_addParser(v_categories_4537_, v_catName_4518_, v_declName_4519_, v___x_4558_, v_snd_4545_, v_a_4528_);
if (lean_obj_tag(v___x_4559_) == 0)
{
lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4569_; 
lean_dec_ref_known(v___x_4556_, 4);
lean_dec(v_declName_4519_);
lean_dec(v_catName_4518_);
v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4562_ = v___x_4559_;
v_isShared_4563_ = v_isSharedCheck_4569_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v___x_4559_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4569_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4565_; 
if (v_isShared_4563_ == 0)
{
lean_ctor_set_tag(v___x_4562_, 3);
v___x_4565_ = v___x_4562_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4560_);
v___x_4565_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4566_ = l_Lean_MessageData_ofFormat(v___x_4565_);
v___x_4567_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4566_, v_a_4522_, v_a_4523_);
return v___x_4567_;
}
}
}
else
{
lean_object* v___x_4570_; lean_object* v___x_4571_; 
lean_dec_ref_known(v___x_4559_, 1);
v___x_4570_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_4531_, v___x_4556_, v_attrKind_4521_, v_a_4522_, v_a_4523_);
lean_dec_ref(v___x_4570_);
v___x_4571_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4518_, v_declName_4519_, v___x_4535_, v_a_4522_, v_a_4523_);
return v___x_4571_;
}
}
else
{
lean_dec(v_fst_4547_);
lean_dec(v_snd_4545_);
lean_dec_ref(v_categories_4537_);
lean_dec(v_a_4528_);
lean_dec(v_declName_4519_);
lean_dec(v_catName_4518_);
return v___x_4555_;
}
}
else
{
lean_dec(v_fst_4547_);
lean_dec(v_snd_4545_);
lean_dec_ref(v_categories_4537_);
lean_dec(v_a_4528_);
lean_dec(v_declName_4519_);
lean_dec(v_catName_4518_);
return v___x_4552_;
}
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4583_; 
lean_dec_ref(v_categories_4537_);
lean_dec(v_a_4528_);
lean_dec(v_declName_4519_);
lean_dec(v_catName_4518_);
v_a_4572_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4574_ = v___x_4543_;
v_isShared_4575_ = v_isSharedCheck_4583_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4543_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4583_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4581_; 
v___x_4576_ = lean_io_error_to_string(v_a_4572_);
v___x_4577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4576_);
v___x_4578_ = l_Lean_MessageData_ofFormat(v___x_4577_);
lean_inc(v_ref_4540_);
v___x_4579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4579_, 0, v_ref_4540_);
lean_ctor_set(v___x_4579_, 1, v___x_4578_);
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 0, v___x_4579_);
v___x_4581_ = v___x_4574_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4579_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_dec(v_declName_4519_);
lean_dec(v_catName_4518_);
v_a_4584_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4527_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4527_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object* v_catName_4592_, lean_object* v_declName_4593_, lean_object* v_stx_4594_, lean_object* v_attrKind_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_){
_start:
{
uint8_t v_attrKind_boxed_4599_; lean_object* v_res_4600_; 
v_attrKind_boxed_4599_ = lean_unbox(v_attrKind_4595_);
v_res_4600_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4592_, v_declName_4593_, v_stx_4594_, v_attrKind_boxed_4599_, v_a_4596_, v_a_4597_);
lean_dec(v_a_4597_);
lean_dec_ref(v_a_4596_);
return v_res_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* v___attrName_4601_, lean_object* v_catName_4602_, lean_object* v_declName_4603_, lean_object* v_stx_4604_, uint8_t v_attrKind_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_){
_start:
{
lean_object* v___x_4609_; 
v___x_4609_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4602_, v_declName_4603_, v_stx_4604_, v_attrKind_4605_, v_a_4606_, v_a_4607_);
return v___x_4609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* v___attrName_4610_, lean_object* v_catName_4611_, lean_object* v_declName_4612_, lean_object* v_stx_4613_, lean_object* v_attrKind_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
uint8_t v_attrKind_boxed_4618_; lean_object* v_res_4619_; 
v_attrKind_boxed_4618_ = lean_unbox(v_attrKind_4614_);
v_res_4619_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4610_, v_catName_4611_, v_declName_4612_, v_stx_4613_, v_attrKind_boxed_4618_, v_a_4615_, v_a_4616_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec(v___attrName_4610_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object* v_00_u03b2_4620_, lean_object* v_map_4621_, lean_object* v_f_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v___x_4626_; 
v___x_4626_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4621_, v_f_4622_, v___y_4623_, v___y_4624_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b2_4627_, lean_object* v_map_4628_, lean_object* v_f_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(v_00_u03b2_4627_, v_map_4628_, v_f_4629_, v___y_4630_, v___y_4631_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object* v_map_4634_, lean_object* v_f_4635_, lean_object* v_init_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
lean_object* v___x_4640_; 
v___x_4640_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4635_, v_map_4634_, v_init_4636_, v___y_4637_, v___y_4638_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object* v_map_4641_, lean_object* v_f_4642_, lean_object* v_init_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4641_, v_f_4642_, v_init_4643_, v___y_4644_, v___y_4645_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object* v_00_u03c3_4648_, lean_object* v_00_u03b2_4649_, lean_object* v_map_4650_, lean_object* v_f_4651_, lean_object* v_init_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v___x_4656_; 
v___x_4656_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4651_, v_map_4650_, v_init_4652_, v___y_4653_, v___y_4654_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object* v_00_u03c3_4657_, lean_object* v_00_u03b2_4658_, lean_object* v_map_4659_, lean_object* v_f_4660_, lean_object* v_init_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(v_00_u03c3_4657_, v_00_u03b2_4658_, v_map_4659_, v_f_4660_, v_init_4661_, v___y_4662_, v___y_4663_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_4666_, lean_object* v_00_u03b1_4667_, lean_object* v_00_u03b2_4668_, lean_object* v_f_4669_, lean_object* v_x_4670_, lean_object* v_x_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_){
_start:
{
lean_object* v___x_4675_; 
v___x_4675_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4669_, v_x_4670_, v_x_4671_, v___y_4672_, v___y_4673_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03c3_4676_, lean_object* v_00_u03b1_4677_, lean_object* v_00_u03b2_4678_, lean_object* v_f_4679_, lean_object* v_x_4680_, lean_object* v_x_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(v_00_u03c3_4676_, v_00_u03b1_4677_, v_00_u03b2_4678_, v_f_4679_, v_x_4680_, v_x_4681_, v___y_4682_, v___y_4683_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4686_, lean_object* v_00_u03b2_4687_, lean_object* v_00_u03c3_4688_, lean_object* v_f_4689_, lean_object* v_as_4690_, size_t v_i_4691_, size_t v_stop_4692_, lean_object* v_b_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
lean_object* v___x_4697_; 
v___x_4697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4689_, v_as_4690_, v_i_4691_, v_stop_4692_, v_b_4693_, v___y_4694_, v___y_4695_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4698_, lean_object* v_00_u03b2_4699_, lean_object* v_00_u03c3_4700_, lean_object* v_f_4701_, lean_object* v_as_4702_, lean_object* v_i_4703_, lean_object* v_stop_4704_, lean_object* v_b_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
size_t v_i_boxed_4709_; size_t v_stop_boxed_4710_; lean_object* v_res_4711_; 
v_i_boxed_4709_ = lean_unbox_usize(v_i_4703_);
lean_dec(v_i_4703_);
v_stop_boxed_4710_ = lean_unbox_usize(v_stop_4704_);
lean_dec(v_stop_4704_);
v_res_4711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4698_, v_00_u03b2_4699_, v_00_u03c3_4700_, v_f_4701_, v_as_4702_, v_i_boxed_4709_, v_stop_boxed_4710_, v_b_4705_, v___y_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec_ref(v_as_4702_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_4712_, lean_object* v_00_u03b1_4713_, lean_object* v_00_u03b2_4714_, lean_object* v_f_4715_, lean_object* v_keys_4716_, lean_object* v_vals_4717_, lean_object* v_heq_4718_, lean_object* v_i_4719_, lean_object* v_acc_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v___x_4724_; 
v___x_4724_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4715_, v_keys_4716_, v_vals_4717_, v_i_4719_, v_acc_4720_, v___y_4721_, v___y_4722_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_4725_, lean_object* v_00_u03b1_4726_, lean_object* v_00_u03b2_4727_, lean_object* v_f_4728_, lean_object* v_keys_4729_, lean_object* v_vals_4730_, lean_object* v_heq_4731_, lean_object* v_i_4732_, lean_object* v_acc_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4725_, v_00_u03b1_4726_, v_00_u03b2_4727_, v_f_4728_, v_keys_4729_, v_vals_4730_, v_heq_4731_, v_i_4732_, v_acc_4733_, v___y_4734_, v___y_4735_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec_ref(v_vals_4730_);
lean_dec_ref(v_keys_4729_);
return v_res_4737_;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___auto__1(void){
_start:
{
lean_object* v___x_4738_; 
v___x_4738_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object* v_catName_4739_, lean_object* v_declName_4740_, lean_object* v_stx_4741_, uint8_t v_attrKind_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v___x_4746_; 
v___x_4746_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4739_, v_declName_4740_, v_stx_4741_, v_attrKind_4742_, v___y_4743_, v___y_4744_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object* v_catName_4747_, lean_object* v_declName_4748_, lean_object* v_stx_4749_, lean_object* v_attrKind_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_){
_start:
{
uint8_t v_attrKind_boxed_4754_; lean_object* v_res_4755_; 
v_attrKind_boxed_4754_ = lean_unbox(v_attrKind_4750_);
v_res_4755_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4747_, v_declName_4748_, v_stx_4749_, v_attrKind_boxed_4754_, v___y_4751_, v___y_4752_);
lean_dec(v___y_4752_);
lean_dec_ref(v___y_4751_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* v_attrName_4757_, lean_object* v_catName_4758_, lean_object* v_ref_4759_){
_start:
{
lean_object* v___f_4760_; lean_object* v___f_4761_; lean_object* v___x_4762_; uint8_t v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___f_4760_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4760_, 0, v_catName_4758_);
lean_inc(v_attrName_4757_);
v___f_4761_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4761_, 0, v_attrName_4757_);
v___x_4762_ = ((lean_object*)(l_Lean_Parser_mkParserAttributeImpl___closed__0));
v___x_4763_ = 1;
v___x_4764_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4764_, 0, v_ref_4759_);
lean_ctor_set(v___x_4764_, 1, v_attrName_4757_);
lean_ctor_set(v___x_4764_, 2, v___x_4762_);
lean_ctor_set_uint8(v___x_4764_, sizeof(void*)*3, v___x_4763_);
v___x_4765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4764_);
lean_ctor_set(v___x_4765_, 1, v___f_4760_);
lean_ctor_set(v___x_4765_, 2, v___f_4761_);
return v___x_4765_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4766_; 
v___x_4766_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* v_attrName_4767_, lean_object* v_catName_4768_, lean_object* v_ref_4769_){
_start:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4771_ = l_Lean_Parser_mkParserAttributeImpl(v_attrName_4767_, v_catName_4768_, v_ref_4769_);
v___x_4772_ = l_Lean_registerBuiltinAttribute(v___x_4771_);
return v___x_4772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object* v_attrName_4773_, lean_object* v_catName_4774_, lean_object* v_ref_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4773_, v_catName_4774_, v_ref_4775_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object* v_ref_4781_, lean_object* v_args_4782_){
_start:
{
if (lean_obj_tag(v_args_4782_) == 1)
{
lean_object* v_head_4785_; 
v_head_4785_ = lean_ctor_get(v_args_4782_, 0);
lean_inc(v_head_4785_);
if (lean_obj_tag(v_head_4785_) == 2)
{
lean_object* v_tail_4786_; 
v_tail_4786_ = lean_ctor_get(v_args_4782_, 1);
lean_inc(v_tail_4786_);
lean_dec_ref_known(v_args_4782_, 2);
if (lean_obj_tag(v_tail_4786_) == 1)
{
lean_object* v_head_4787_; 
v_head_4787_ = lean_ctor_get(v_tail_4786_, 0);
lean_inc(v_head_4787_);
if (lean_obj_tag(v_head_4787_) == 2)
{
lean_object* v_tail_4788_; 
v_tail_4788_ = lean_ctor_get(v_tail_4786_, 1);
lean_inc(v_tail_4788_);
lean_dec_ref_known(v_tail_4786_, 2);
if (lean_obj_tag(v_tail_4788_) == 0)
{
lean_object* v_v_4789_; lean_object* v_v_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4798_; 
v_v_4789_ = lean_ctor_get(v_head_4785_, 0);
lean_inc(v_v_4789_);
lean_dec_ref_known(v_head_4785_, 1);
v_v_4790_ = lean_ctor_get(v_head_4787_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v_head_4787_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4792_ = v_head_4787_;
v_isShared_4793_ = v_isSharedCheck_4798_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_v_4790_);
lean_dec(v_head_4787_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4798_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4794_; lean_object* v___x_4796_; 
v___x_4794_ = l_Lean_Parser_mkParserAttributeImpl(v_v_4789_, v_v_4790_, v_ref_4781_);
if (v_isShared_4793_ == 0)
{
lean_ctor_set_tag(v___x_4792_, 1);
lean_ctor_set(v___x_4792_, 0, v___x_4794_);
v___x_4796_ = v___x_4792_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4794_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
else
{
lean_dec(v_tail_4788_);
lean_dec_ref_known(v_head_4787_, 1);
lean_dec_ref_known(v_head_4785_, 1);
lean_dec(v_ref_4781_);
goto v___jp_4783_;
}
}
else
{
lean_dec_ref_known(v_tail_4786_, 2);
lean_dec(v_head_4787_);
lean_dec_ref_known(v_head_4785_, 1);
lean_dec(v_ref_4781_);
goto v___jp_4783_;
}
}
else
{
lean_dec(v_tail_4786_);
lean_dec_ref_known(v_head_4785_, 1);
lean_dec(v_ref_4781_);
goto v___jp_4783_;
}
}
else
{
lean_dec_ref_known(v_args_4782_, 2);
lean_dec(v_head_4785_);
lean_dec(v_ref_4781_);
goto v___jp_4783_;
}
}
else
{
lean_dec(v_args_4782_);
lean_dec(v_ref_4781_);
goto v___jp_4783_;
}
v___jp_4783_:
{
lean_object* v___x_4784_; 
v___x_4784_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
return v___x_4784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___f_4804_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4805_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4806_ = l_Lean_registerAttributeImplBuilder(v___x_4805_, v___f_4804_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object* v_a_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
return v_res_4808_;
}
}
static lean_object* _init_l_Lean_Parser_registerParserCategory___auto__1(void){
_start:
{
lean_object* v___x_4809_; 
v___x_4809_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object* v_env_4810_, lean_object* v_attrName_4811_, lean_object* v_catName_4812_, uint8_t v_behavior_4813_, lean_object* v_ref_4814_){
_start:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; 
lean_inc(v_ref_4814_);
lean_inc(v_catName_4812_);
v___x_4816_ = l_Lean_Parser_addParserCategory(v_env_4810_, v_catName_4812_, v_ref_4814_, v_behavior_4813_);
v___x_4817_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_4816_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4831_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4831_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4831_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4822_; lean_object* v___x_4824_; 
v___x_4822_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
if (v_isShared_4821_ == 0)
{
lean_ctor_set_tag(v___x_4820_, 2);
lean_ctor_set(v___x_4820_, 0, v_attrName_4811_);
v___x_4824_ = v___x_4820_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_attrName_4811_);
v___x_4824_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4825_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4825_, 0, v_catName_4812_);
v___x_4826_ = lean_box(0);
v___x_4827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4825_);
lean_ctor_set(v___x_4827_, 1, v___x_4826_);
v___x_4828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4824_);
lean_ctor_set(v___x_4828_, 1, v___x_4827_);
v___x_4829_ = l_Lean_registerAttributeOfBuilder(v_a_4818_, v___x_4822_, v_ref_4814_, v___x_4828_);
return v___x_4829_;
}
}
}
else
{
lean_dec(v_ref_4814_);
lean_dec(v_catName_4812_);
lean_dec(v_attrName_4811_);
return v___x_4817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* v_env_4832_, lean_object* v_attrName_4833_, lean_object* v_catName_4834_, lean_object* v_behavior_4835_, lean_object* v_ref_4836_, lean_object* v_a_4837_){
_start:
{
uint8_t v_behavior_boxed_4838_; lean_object* v_res_4839_; 
v_behavior_boxed_4838_ = lean_unbox(v_behavior_4835_);
v_res_4839_ = l_Lean_Parser_registerParserCategory(v_env_4832_, v_attrName_4833_, v_catName_4834_, v_behavior_boxed_4838_, v_ref_4836_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; uint8_t v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4862_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4863_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4864_ = 0;
v___x_4865_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4866_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4862_, v___x_4863_, v___x_4864_, v___x_4865_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object* v_a_4867_){
_start:
{
lean_object* v_res_4868_; 
v_res_4868_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
return v_res_4868_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4874_ = lean_unsigned_to_nat(3431364690u);
v___x_4875_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4876_ = l_Lean_Name_num___override(v___x_4875_, v___x_4874_);
return v___x_4876_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4877_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4878_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4879_ = l_Lean_Name_str___override(v___x_4878_, v___x_4877_);
return v___x_4879_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4880_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4881_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4882_ = l_Lean_Name_str___override(v___x_4881_, v___x_4880_);
return v___x_4882_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4883_ = lean_unsigned_to_nat(2u);
v___x_4884_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4885_ = l_Lean_Name_num___override(v___x_4884_, v___x_4883_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4887_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4888_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4889_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4890_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4887_, v___x_4888_, v___x_4889_);
return v___x_4890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object* v_a_4891_){
_start:
{
lean_object* v_res_4892_; 
v_res_4892_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
return v_res_4892_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4902_ = lean_unsigned_to_nat(2342493449u);
v___x_4903_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4904_ = l_Lean_Name_num___override(v___x_4903_, v___x_4902_);
return v___x_4904_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; 
v___x_4905_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4906_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4907_ = l_Lean_Name_str___override(v___x_4906_, v___x_4905_);
return v___x_4907_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4908_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4909_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4910_ = l_Lean_Name_str___override(v___x_4909_, v___x_4908_);
return v___x_4910_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4911_ = lean_unsigned_to_nat(2u);
v___x_4912_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4913_ = l_Lean_Name_num___override(v___x_4912_, v___x_4911_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; uint8_t v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4915_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4916_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4917_ = 0;
v___x_4918_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4919_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4915_, v___x_4916_, v___x_4917_, v___x_4918_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object* v_a_4920_){
_start:
{
lean_object* v_res_4921_; 
v_res_4921_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
return v_res_4921_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4927_ = lean_unsigned_to_nat(3226070615u);
v___x_4928_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4929_ = l_Lean_Name_num___override(v___x_4928_, v___x_4927_);
return v___x_4929_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4930_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4931_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4932_ = l_Lean_Name_str___override(v___x_4931_, v___x_4930_);
return v___x_4932_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; 
v___x_4933_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4934_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4935_ = l_Lean_Name_str___override(v___x_4934_, v___x_4933_);
return v___x_4935_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4936_ = lean_unsigned_to_nat(2u);
v___x_4937_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4938_ = l_Lean_Name_num___override(v___x_4937_, v___x_4936_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4940_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4941_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4942_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4943_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4940_, v___x_4941_, v___x_4942_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object* v_a_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* v_rbp_4946_){
_start:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4947_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4948_ = l_Lean_Parser_categoryParser(v___x_4947_, v_rbp_4946_);
return v___x_4948_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t v_addOpenSimple_4949_, lean_object* v_x_4950_, lean_object* v_x_4951_){
_start:
{
if (lean_obj_tag(v_x_4951_) == 0)
{
return v_x_4950_;
}
else
{
lean_object* v_head_4952_; lean_object* v_tail_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4976_; 
v_head_4952_ = lean_ctor_get(v_x_4951_, 0);
v_tail_4953_ = lean_ctor_get(v_x_4951_, 1);
v_isSharedCheck_4976_ = !lean_is_exclusive(v_x_4951_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4955_ = v_x_4951_;
v_isShared_4956_ = v_isSharedCheck_4976_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_tail_4953_);
lean_inc(v_head_4952_);
lean_dec(v_x_4951_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4976_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v_fst_4957_; lean_object* v_snd_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4975_; 
v_fst_4957_ = lean_ctor_get(v_x_4950_, 0);
v_snd_4958_ = lean_ctor_get(v_x_4950_, 1);
v_isSharedCheck_4975_ = !lean_is_exclusive(v_x_4950_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4960_ = v_x_4950_;
v_isShared_4961_ = v_isSharedCheck_4975_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_snd_4958_);
lean_inc(v_fst_4957_);
lean_dec(v_x_4950_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4975_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___y_4963_; 
if (v_addOpenSimple_4949_ == 0)
{
lean_del_object(v___x_4955_);
v___y_4963_ = v_snd_4958_;
goto v___jp_4962_;
}
else
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4973_; 
v___x_4970_ = lean_box(0);
lean_inc(v_head_4952_);
v___x_4971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4971_, 0, v_head_4952_);
lean_ctor_set(v___x_4971_, 1, v___x_4970_);
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 1, v_snd_4958_);
lean_ctor_set(v___x_4955_, 0, v___x_4971_);
v___x_4973_ = v___x_4955_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v___x_4971_);
lean_ctor_set(v_reuseFailAlloc_4974_, 1, v_snd_4958_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
v___y_4963_ = v___x_4973_;
goto v___jp_4962_;
}
}
v___jp_4962_:
{
lean_object* v___x_4964_; lean_object* v_env_4965_; lean_object* v___x_4967_; 
v___x_4964_ = l_Lean_Parser_parserExtension;
v_env_4965_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v___x_4964_, v_fst_4957_, v_head_4952_);
if (v_isShared_4961_ == 0)
{
lean_ctor_set(v___x_4960_, 1, v___y_4963_);
lean_ctor_set(v___x_4960_, 0, v_env_4965_);
v___x_4967_ = v___x_4960_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4969_; 
v_reuseFailAlloc_4969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4969_, 0, v_env_4965_);
lean_ctor_set(v_reuseFailAlloc_4969_, 1, v___y_4963_);
v___x_4967_ = v_reuseFailAlloc_4969_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
v_x_4950_ = v___x_4967_;
v_x_4951_ = v_tail_4953_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object* v_addOpenSimple_4977_, lean_object* v_x_4978_, lean_object* v_x_4979_){
_start:
{
uint8_t v_addOpenSimple_boxed_4980_; lean_object* v_res_4981_; 
v_addOpenSimple_boxed_4980_ = lean_unbox(v_addOpenSimple_4977_);
v_res_4981_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_boxed_4980_, v_x_4978_, v_x_4979_);
return v_res_4981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t v_addOpenSimple_4982_, lean_object* v_as_4983_, size_t v_i_4984_, size_t v_stop_4985_, lean_object* v_b_4986_){
_start:
{
uint8_t v___x_4987_; 
v___x_4987_ = lean_usize_dec_eq(v_i_4984_, v_stop_4985_);
if (v___x_4987_ == 0)
{
lean_object* v_toParserModuleContext_4988_; lean_object* v_toInputContext_4989_; lean_object* v_toCacheableParserContext_4990_; lean_object* v_tokens_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_5018_; 
v_toParserModuleContext_4988_ = lean_ctor_get(v_b_4986_, 1);
v_toInputContext_4989_ = lean_ctor_get(v_b_4986_, 0);
v_toCacheableParserContext_4990_ = lean_ctor_get(v_b_4986_, 2);
v_tokens_4991_ = lean_ctor_get(v_b_4986_, 3);
v_isSharedCheck_5018_ = !lean_is_exclusive(v_b_4986_);
if (v_isSharedCheck_5018_ == 0)
{
v___x_4993_ = v_b_4986_;
v_isShared_4994_ = v_isSharedCheck_5018_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_tokens_4991_);
lean_inc(v_toCacheableParserContext_4990_);
lean_inc(v_toParserModuleContext_4988_);
lean_inc(v_toInputContext_4989_);
lean_dec(v_b_4986_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_5018_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v_env_4995_; lean_object* v_options_4996_; lean_object* v_currNamespace_4997_; lean_object* v_openDecls_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5017_; 
v_env_4995_ = lean_ctor_get(v_toParserModuleContext_4988_, 0);
v_options_4996_ = lean_ctor_get(v_toParserModuleContext_4988_, 1);
v_currNamespace_4997_ = lean_ctor_get(v_toParserModuleContext_4988_, 2);
v_openDecls_4998_ = lean_ctor_get(v_toParserModuleContext_4988_, 3);
v_isSharedCheck_5017_ = !lean_is_exclusive(v_toParserModuleContext_4988_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5000_ = v_toParserModuleContext_4988_;
v_isShared_5001_ = v_isSharedCheck_5017_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_openDecls_4998_);
lean_inc(v_currNamespace_4997_);
lean_inc(v_options_4996_);
lean_inc(v_env_4995_);
lean_dec(v_toParserModuleContext_4988_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5017_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5002_; lean_object* v_nss_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v_fst_5006_; lean_object* v_snd_5007_; lean_object* v___x_5009_; 
v___x_5002_ = lean_array_uget_borrowed(v_as_4983_, v_i_4984_);
lean_inc(v___x_5002_);
lean_inc(v_openDecls_4998_);
lean_inc(v_currNamespace_4997_);
lean_inc_ref(v_env_4995_);
v_nss_5003_ = l_Lean_ResolveName_resolveNamespace(v_env_4995_, v_currNamespace_4997_, v_openDecls_4998_, v___x_5002_);
v___x_5004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5004_, 0, v_env_4995_);
lean_ctor_set(v___x_5004_, 1, v_openDecls_4998_);
v___x_5005_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4982_, v___x_5004_, v_nss_5003_);
v_fst_5006_ = lean_ctor_get(v___x_5005_, 0);
lean_inc(v_fst_5006_);
v_snd_5007_ = lean_ctor_get(v___x_5005_, 1);
lean_inc(v_snd_5007_);
lean_dec_ref(v___x_5005_);
if (v_isShared_5001_ == 0)
{
lean_ctor_set(v___x_5000_, 3, v_snd_5007_);
lean_ctor_set(v___x_5000_, 0, v_fst_5006_);
v___x_5009_ = v___x_5000_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_fst_5006_);
lean_ctor_set(v_reuseFailAlloc_5016_, 1, v_options_4996_);
lean_ctor_set(v_reuseFailAlloc_5016_, 2, v_currNamespace_4997_);
lean_ctor_set(v_reuseFailAlloc_5016_, 3, v_snd_5007_);
v___x_5009_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5011_; 
if (v_isShared_4994_ == 0)
{
lean_ctor_set(v___x_4993_, 1, v___x_5009_);
v___x_5011_ = v___x_4993_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_toInputContext_4989_);
lean_ctor_set(v_reuseFailAlloc_5015_, 1, v___x_5009_);
lean_ctor_set(v_reuseFailAlloc_5015_, 2, v_toCacheableParserContext_4990_);
lean_ctor_set(v_reuseFailAlloc_5015_, 3, v_tokens_4991_);
v___x_5011_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
size_t v___x_5012_; size_t v___x_5013_; 
v___x_5012_ = ((size_t)1ULL);
v___x_5013_ = lean_usize_add(v_i_4984_, v___x_5012_);
v_i_4984_ = v___x_5013_;
v_b_4986_ = v___x_5011_;
goto _start;
}
}
}
}
}
else
{
return v_b_4986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object* v_addOpenSimple_5019_, lean_object* v_as_5020_, lean_object* v_i_5021_, lean_object* v_stop_5022_, lean_object* v_b_5023_){
_start:
{
uint8_t v_addOpenSimple_boxed_5024_; size_t v_i_boxed_5025_; size_t v_stop_boxed_5026_; lean_object* v_res_5027_; 
v_addOpenSimple_boxed_5024_ = lean_unbox(v_addOpenSimple_5019_);
v_i_boxed_5025_ = lean_unbox_usize(v_i_5021_);
lean_dec(v_i_5021_);
v_stop_boxed_5026_ = lean_unbox_usize(v_stop_5022_);
lean_dec(v_stop_5022_);
v_res_5027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_boxed_5024_, v_as_5020_, v_i_boxed_5025_, v_stop_boxed_5026_, v_b_5023_);
lean_dec_ref(v_as_5020_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object* v___x_5028_, lean_object* v_ids_5029_, uint8_t v_addOpenSimple_5030_, lean_object* v_c_5031_){
_start:
{
lean_object* v___y_5033_; lean_object* v___x_5053_; lean_object* v___x_5054_; uint8_t v___x_5055_; 
v___x_5053_ = lean_unsigned_to_nat(0u);
v___x_5054_ = lean_array_get_size(v_ids_5029_);
v___x_5055_ = lean_nat_dec_lt(v___x_5053_, v___x_5054_);
if (v___x_5055_ == 0)
{
v___y_5033_ = v_c_5031_;
goto v___jp_5032_;
}
else
{
size_t v___x_5056_; size_t v___x_5057_; lean_object* v___x_5058_; 
v___x_5056_ = ((size_t)0ULL);
v___x_5057_ = lean_usize_of_nat(v___x_5054_);
v___x_5058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_5030_, v_ids_5029_, v___x_5056_, v___x_5057_, v_c_5031_);
v___y_5033_ = v___x_5058_;
goto v___jp_5032_;
}
v___jp_5032_:
{
lean_object* v_toParserModuleContext_5034_; lean_object* v_toInputContext_5035_; lean_object* v_toCacheableParserContext_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5051_; 
v_toParserModuleContext_5034_ = lean_ctor_get(v___y_5033_, 1);
v_toInputContext_5035_ = lean_ctor_get(v___y_5033_, 0);
v_toCacheableParserContext_5036_ = lean_ctor_get(v___y_5033_, 2);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___y_5033_);
if (v_isSharedCheck_5051_ == 0)
{
lean_object* v_unused_5052_; 
v_unused_5052_ = lean_ctor_get(v___y_5033_, 3);
lean_dec(v_unused_5052_);
v___x_5038_ = v___y_5033_;
v_isShared_5039_ = v_isSharedCheck_5051_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_toCacheableParserContext_5036_);
lean_inc(v_toParserModuleContext_5034_);
lean_inc(v_toInputContext_5035_);
lean_dec(v___y_5033_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5051_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v_env_5040_; lean_object* v___x_5041_; lean_object* v_ext_5042_; lean_object* v_toEnvExtension_5043_; lean_object* v_asyncMode_5044_; uint8_t v___x_5045_; lean_object* v___x_5046_; lean_object* v_tokens_5047_; lean_object* v___x_5049_; 
v_env_5040_ = lean_ctor_get(v_toParserModuleContext_5034_, 0);
v___x_5041_ = l_Lean_Parser_parserExtension;
v_ext_5042_ = lean_ctor_get(v___x_5041_, 1);
v_toEnvExtension_5043_ = lean_ctor_get(v_ext_5042_, 0);
v_asyncMode_5044_ = lean_ctor_get(v_toEnvExtension_5043_, 2);
v___x_5045_ = 0;
lean_inc_ref(v_env_5040_);
v___x_5046_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5028_, v___x_5041_, v_env_5040_, v_asyncMode_5044_, v___x_5045_);
v_tokens_5047_ = lean_ctor_get(v___x_5046_, 0);
lean_inc_ref(v_tokens_5047_);
lean_dec(v___x_5046_);
if (v_isShared_5039_ == 0)
{
lean_ctor_set(v___x_5038_, 3, v_tokens_5047_);
v___x_5049_ = v___x_5038_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_toInputContext_5035_);
lean_ctor_set(v_reuseFailAlloc_5050_, 1, v_toParserModuleContext_5034_);
lean_ctor_set(v_reuseFailAlloc_5050_, 2, v_toCacheableParserContext_5036_);
lean_ctor_set(v_reuseFailAlloc_5050_, 3, v_tokens_5047_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object* v___x_5059_, lean_object* v_ids_5060_, lean_object* v_addOpenSimple_5061_, lean_object* v_c_5062_){
_start:
{
uint8_t v_addOpenSimple_boxed_5063_; lean_object* v_res_5064_; 
v_addOpenSimple_boxed_5063_ = lean_unbox(v_addOpenSimple_5061_);
v_res_5064_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_5059_, v_ids_5060_, v_addOpenSimple_boxed_5063_, v_c_5062_);
lean_dec_ref(v_ids_5060_);
lean_dec_ref(v___x_5059_);
return v_res_5064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* v_ids_5065_, uint8_t v_addOpenSimple_5066_, lean_object* v_p_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_){
_start:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___f_5072_; lean_object* v___x_5073_; 
v___x_5070_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_5071_ = lean_box(v_addOpenSimple_5066_);
v___f_5072_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed), 4, 3);
lean_closure_set(v___f_5072_, 0, v___x_5070_);
lean_closure_set(v___f_5072_, 1, v_ids_5065_);
lean_closure_set(v___f_5072_, 2, v___x_5071_);
v___x_5073_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5072_, v_p_5067_, v_a_5068_, v_a_5069_);
return v___x_5073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* v_ids_5074_, lean_object* v_addOpenSimple_5075_, lean_object* v_p_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_){
_start:
{
uint8_t v_addOpenSimple_boxed_5079_; lean_object* v_res_5080_; 
v_addOpenSimple_boxed_5079_ = lean_unbox(v_addOpenSimple_5075_);
v_res_5080_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_5074_, v_addOpenSimple_boxed_5079_, v_p_5076_, v_a_5077_, v_a_5078_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t v_sz_5081_, size_t v_i_5082_, lean_object* v_bs_5083_){
_start:
{
uint8_t v___x_5084_; 
v___x_5084_ = lean_usize_dec_lt(v_i_5082_, v_sz_5081_);
if (v___x_5084_ == 0)
{
return v_bs_5083_;
}
else
{
lean_object* v_v_5085_; lean_object* v___x_5086_; lean_object* v_bs_x27_5087_; lean_object* v___x_5088_; size_t v___x_5089_; size_t v___x_5090_; lean_object* v___x_5091_; 
v_v_5085_ = lean_array_uget(v_bs_5083_, v_i_5082_);
v___x_5086_ = lean_unsigned_to_nat(0u);
v_bs_x27_5087_ = lean_array_uset(v_bs_5083_, v_i_5082_, v___x_5086_);
v___x_5088_ = l_Lean_Syntax_getId(v_v_5085_);
lean_dec(v_v_5085_);
v___x_5089_ = ((size_t)1ULL);
v___x_5090_ = lean_usize_add(v_i_5082_, v___x_5089_);
v___x_5091_ = lean_array_uset(v_bs_x27_5087_, v_i_5082_, v___x_5088_);
v_i_5082_ = v___x_5090_;
v_bs_5083_ = v___x_5091_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object* v_sz_5093_, lean_object* v_i_5094_, lean_object* v_bs_5095_){
_start:
{
size_t v_sz_boxed_5096_; size_t v_i_boxed_5097_; lean_object* v_res_5098_; 
v_sz_boxed_5096_ = lean_unbox_usize(v_sz_5093_);
lean_dec(v_sz_5093_);
v_i_boxed_5097_ = lean_unbox_usize(v_i_5094_);
lean_dec(v_i_5094_);
v_res_5098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_boxed_5096_, v_i_boxed_5097_, v_bs_5095_);
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* v_openDeclStx_5112_, lean_object* v_p_5113_, lean_object* v_c_5114_, lean_object* v_s_5115_){
_start:
{
lean_object* v___x_5116_; lean_object* v___x_5117_; uint8_t v___x_5118_; 
lean_inc(v_openDeclStx_5112_);
v___x_5116_ = l_Lean_Syntax_getKind(v_openDeclStx_5112_);
v___x_5117_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__2));
v___x_5118_ = lean_name_eq(v___x_5116_, v___x_5117_);
if (v___x_5118_ == 0)
{
lean_object* v___x_5119_; uint8_t v___x_5120_; 
v___x_5119_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__4));
v___x_5120_ = lean_name_eq(v___x_5116_, v___x_5119_);
lean_dec(v___x_5116_);
if (v___x_5120_ == 0)
{
lean_object* v___x_5121_; 
lean_dec(v_openDeclStx_5112_);
v___x_5121_ = lean_apply_2(v_p_5113_, v_c_5114_, v_s_5115_);
return v___x_5121_;
}
else
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; size_t v_sz_5125_; size_t v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v___x_5122_ = lean_unsigned_to_nat(1u);
v___x_5123_ = l_Lean_Syntax_getArg(v_openDeclStx_5112_, v___x_5122_);
lean_dec(v_openDeclStx_5112_);
v___x_5124_ = l_Lean_Syntax_getArgs(v___x_5123_);
lean_dec(v___x_5123_);
v_sz_5125_ = lean_array_size(v___x_5124_);
v___x_5126_ = ((size_t)0ULL);
v___x_5127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_5125_, v___x_5126_, v___x_5124_);
v___x_5128_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_5127_, v___x_5118_, v_p_5113_, v_c_5114_, v_s_5115_);
return v___x_5128_;
}
}
else
{
lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; size_t v_sz_5132_; size_t v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; 
lean_dec(v___x_5116_);
v___x_5129_ = lean_unsigned_to_nat(0u);
v___x_5130_ = l_Lean_Syntax_getArg(v_openDeclStx_5112_, v___x_5129_);
lean_dec(v_openDeclStx_5112_);
v___x_5131_ = l_Lean_Syntax_getArgs(v___x_5130_);
lean_dec(v___x_5130_);
v_sz_5132_ = lean_array_size(v___x_5131_);
v___x_5133_ = ((size_t)0ULL);
v___x_5134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_5132_, v___x_5133_, v___x_5131_);
v___x_5135_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_5134_, v___x_5118_, v_p_5113_, v_c_5114_, v_s_5115_);
return v___x_5135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* v_p_5142_, lean_object* v_c_5143_, lean_object* v_s_5144_){
_start:
{
lean_object* v_stxStack_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; uint8_t v___x_5148_; 
v_stxStack_5145_ = lean_ctor_get(v_s_5144_, 0);
v___x_5146_ = lean_unsigned_to_nat(0u);
v___x_5147_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5145_);
v___x_5148_ = lean_nat_dec_lt(v___x_5146_, v___x_5147_);
lean_dec(v___x_5147_);
if (v___x_5148_ == 0)
{
lean_object* v___x_5149_; 
v___x_5149_ = lean_apply_2(v_p_5142_, v_c_5143_, v_s_5144_);
return v___x_5149_;
}
else
{
lean_object* v_stx_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; uint8_t v___x_5153_; 
v_stx_5150_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5145_);
lean_inc(v_stx_5150_);
v___x_5151_ = l_Lean_Syntax_getKind(v_stx_5150_);
v___x_5152_ = ((lean_object*)(l_Lean_Parser_withOpenFn___closed__1));
v___x_5153_ = lean_name_eq(v___x_5151_, v___x_5152_);
lean_dec(v___x_5151_);
if (v___x_5153_ == 0)
{
lean_object* v___x_5154_; 
lean_dec(v_stx_5150_);
v___x_5154_ = lean_apply_2(v_p_5142_, v_c_5143_, v_s_5144_);
return v___x_5154_;
}
else
{
lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; 
v___x_5155_ = lean_unsigned_to_nat(1u);
v___x_5156_ = l_Lean_Syntax_getArg(v_stx_5150_, v___x_5155_);
lean_dec(v_stx_5150_);
v___x_5157_ = l_Lean_Parser_withOpenDeclFnCore(v___x_5156_, v_p_5142_, v_c_5143_, v_s_5144_);
return v___x_5157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* v_p_5158_){
_start:
{
lean_object* v_info_5159_; lean_object* v_fn_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5168_; 
v_info_5159_ = lean_ctor_get(v_p_5158_, 0);
v_fn_5160_ = lean_ctor_get(v_p_5158_, 1);
v_isSharedCheck_5168_ = !lean_is_exclusive(v_p_5158_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5162_ = v_p_5158_;
v_isShared_5163_ = v_isSharedCheck_5168_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_fn_5160_);
lean_inc(v_info_5159_);
lean_dec(v_p_5158_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5168_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v___x_5164_; lean_object* v___x_5166_; 
v___x_5164_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(v___x_5164_, 0, v_fn_5160_);
if (v_isShared_5163_ == 0)
{
lean_ctor_set(v___x_5162_, 1, v___x_5164_);
v___x_5166_ = v___x_5162_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_info_5159_);
lean_ctor_set(v_reuseFailAlloc_5167_, 1, v___x_5164_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* v_p_5169_, lean_object* v_c_5170_, lean_object* v_s_5171_){
_start:
{
lean_object* v_stxStack_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; uint8_t v___x_5175_; 
v_stxStack_5172_ = lean_ctor_get(v_s_5171_, 0);
v___x_5173_ = lean_unsigned_to_nat(0u);
v___x_5174_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5172_);
v___x_5175_ = lean_nat_dec_lt(v___x_5173_, v___x_5174_);
lean_dec(v___x_5174_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; 
v___x_5176_ = lean_apply_2(v_p_5169_, v_c_5170_, v_s_5171_);
return v___x_5176_;
}
else
{
lean_object* v_stx_5177_; lean_object* v___x_5178_; 
v_stx_5177_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5172_);
v___x_5178_ = l_Lean_Parser_withOpenDeclFnCore(v_stx_5177_, v_p_5169_, v_c_5170_, v_s_5171_);
return v___x_5178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* v_p_5179_){
_start:
{
lean_object* v_info_5180_; lean_object* v_fn_5181_; lean_object* v___x_5183_; uint8_t v_isShared_5184_; uint8_t v_isSharedCheck_5189_; 
v_info_5180_ = lean_ctor_get(v_p_5179_, 0);
v_fn_5181_ = lean_ctor_get(v_p_5179_, 1);
v_isSharedCheck_5189_ = !lean_is_exclusive(v_p_5179_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5183_ = v_p_5179_;
v_isShared_5184_ = v_isSharedCheck_5189_;
goto v_resetjp_5182_;
}
else
{
lean_inc(v_fn_5181_);
lean_inc(v_info_5180_);
lean_dec(v_p_5179_);
v___x_5183_ = lean_box(0);
v_isShared_5184_ = v_isSharedCheck_5189_;
goto v_resetjp_5182_;
}
v_resetjp_5182_:
{
lean_object* v___x_5185_; lean_object* v___x_5187_; 
v___x_5185_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(v___x_5185_, 0, v_fn_5181_);
if (v_isShared_5184_ == 0)
{
lean_ctor_set(v___x_5183_, 1, v___x_5185_);
v___x_5187_ = v___x_5183_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_info_5180_);
lean_ctor_set(v_reuseFailAlloc_5188_, 1, v___x_5185_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object* v_val_5196_){
_start:
{
lean_object* v___x_5204_; 
v___x_5204_ = l_Lean_Syntax_isStrLit_x3f(v_val_5196_);
if (lean_obj_tag(v___x_5204_) == 1)
{
lean_object* v_val_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5213_; 
v_val_5205_ = lean_ctor_get(v___x_5204_, 0);
v_isSharedCheck_5213_ = !lean_is_exclusive(v___x_5204_);
if (v_isSharedCheck_5213_ == 0)
{
v___x_5207_ = v___x_5204_;
v_isShared_5208_ = v_isSharedCheck_5213_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_val_5205_);
lean_dec(v___x_5204_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5213_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5209_; lean_object* v___x_5211_; 
v___x_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5209_, 0, v_val_5205_);
if (v_isShared_5208_ == 0)
{
lean_ctor_set(v___x_5207_, 0, v___x_5209_);
v___x_5211_ = v___x_5207_;
goto v_reusejp_5210_;
}
else
{
lean_object* v_reuseFailAlloc_5212_; 
v_reuseFailAlloc_5212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5212_, 0, v___x_5209_);
v___x_5211_ = v_reuseFailAlloc_5212_;
goto v_reusejp_5210_;
}
v_reusejp_5210_:
{
return v___x_5211_;
}
}
}
else
{
lean_object* v___x_5214_; 
lean_dec(v___x_5204_);
v___x_5214_ = l_Lean_Syntax_isNatLit_x3f(v_val_5196_);
if (lean_obj_tag(v___x_5214_) == 1)
{
lean_object* v_val_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5223_; 
v_val_5215_ = lean_ctor_get(v___x_5214_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5214_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5217_ = v___x_5214_;
v_isShared_5218_ = v_isSharedCheck_5223_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_val_5215_);
lean_dec(v___x_5214_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5223_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v___x_5219_; lean_object* v___x_5221_; 
v___x_5219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5219_, 0, v_val_5215_);
if (v_isShared_5218_ == 0)
{
lean_ctor_set(v___x_5217_, 0, v___x_5219_);
v___x_5221_ = v___x_5217_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v___x_5219_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
else
{
lean_dec(v___x_5214_);
if (lean_obj_tag(v_val_5196_) == 2)
{
lean_object* v_val_5224_; lean_object* v___x_5225_; uint8_t v___x_5226_; 
v_val_5224_ = lean_ctor_get(v_val_5196_, 1);
v___x_5225_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3));
v___x_5226_ = lean_string_dec_eq(v_val_5224_, v___x_5225_);
if (v___x_5226_ == 0)
{
goto v___jp_5197_;
}
else
{
lean_object* v___x_5227_; lean_object* v___x_5228_; 
v___x_5227_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5227_, 0, v___x_5226_);
v___x_5228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5228_, 0, v___x_5227_);
return v___x_5228_;
}
}
else
{
goto v___jp_5197_;
}
}
}
v___jp_5197_:
{
if (lean_obj_tag(v_val_5196_) == 2)
{
lean_object* v_val_5198_; lean_object* v___x_5199_; uint8_t v___x_5200_; 
v_val_5198_ = lean_ctor_get(v_val_5196_, 1);
v___x_5199_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0));
v___x_5200_ = lean_string_dec_eq(v_val_5198_, v___x_5199_);
if (v___x_5200_ == 0)
{
lean_object* v___x_5201_; 
v___x_5201_ = lean_box(0);
return v___x_5201_;
}
else
{
lean_object* v___x_5202_; 
v___x_5202_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2));
return v___x_5202_;
}
}
else
{
lean_object* v___x_5203_; 
v___x_5203_ = lean_box(0);
return v___x_5203_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object* v_val_5229_){
_start:
{
lean_object* v_res_5230_; 
v_res_5230_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_val_5229_);
lean_dec(v_val_5229_);
return v_res_5230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object* v_nameStx_5231_, lean_object* v_v_5232_, lean_object* v_c_5233_){
_start:
{
lean_object* v_toParserModuleContext_5234_; lean_object* v_toInputContext_5235_; lean_object* v_toCacheableParserContext_5236_; lean_object* v_tokens_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5274_; 
v_toParserModuleContext_5234_ = lean_ctor_get(v_c_5233_, 1);
v_toInputContext_5235_ = lean_ctor_get(v_c_5233_, 0);
v_toCacheableParserContext_5236_ = lean_ctor_get(v_c_5233_, 2);
v_tokens_5237_ = lean_ctor_get(v_c_5233_, 3);
v_isSharedCheck_5274_ = !lean_is_exclusive(v_c_5233_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5239_ = v_c_5233_;
v_isShared_5240_ = v_isSharedCheck_5274_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_tokens_5237_);
lean_inc(v_toCacheableParserContext_5236_);
lean_inc(v_toParserModuleContext_5234_);
lean_inc(v_toInputContext_5235_);
lean_dec(v_c_5233_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5274_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v_env_5241_; lean_object* v_options_5242_; lean_object* v_currNamespace_5243_; lean_object* v_openDecls_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5273_; 
v_env_5241_ = lean_ctor_get(v_toParserModuleContext_5234_, 0);
v_options_5242_ = lean_ctor_get(v_toParserModuleContext_5234_, 1);
v_currNamespace_5243_ = lean_ctor_get(v_toParserModuleContext_5234_, 2);
v_openDecls_5244_ = lean_ctor_get(v_toParserModuleContext_5234_, 3);
v_isSharedCheck_5273_ = !lean_is_exclusive(v_toParserModuleContext_5234_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5246_ = v_toParserModuleContext_5234_;
v_isShared_5247_ = v_isSharedCheck_5273_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_openDecls_5244_);
lean_inc(v_currNamespace_5243_);
lean_inc(v_options_5242_);
lean_inc(v_env_5241_);
lean_dec(v_toParserModuleContext_5234_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5273_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
lean_object* v___y_5249_; lean_object* v_map_5256_; uint8_t v_hasTrace_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5272_; 
v_map_5256_ = lean_ctor_get(v_options_5242_, 0);
v_hasTrace_5257_ = lean_ctor_get_uint8(v_options_5242_, sizeof(void*)*1);
v_isSharedCheck_5272_ = !lean_is_exclusive(v_options_5242_);
if (v_isSharedCheck_5272_ == 0)
{
v___x_5259_ = v_options_5242_;
v_isShared_5260_ = v_isSharedCheck_5272_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_map_5256_);
lean_dec(v_options_5242_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5272_;
goto v_resetjp_5258_;
}
v___jp_5248_:
{
lean_object* v___x_5251_; 
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 1, v___y_5249_);
v___x_5251_ = v___x_5246_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_env_5241_);
lean_ctor_set(v_reuseFailAlloc_5255_, 1, v___y_5249_);
lean_ctor_set(v_reuseFailAlloc_5255_, 2, v_currNamespace_5243_);
lean_ctor_set(v_reuseFailAlloc_5255_, 3, v_openDecls_5244_);
v___x_5251_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
lean_object* v___x_5253_; 
if (v_isShared_5240_ == 0)
{
lean_ctor_set(v___x_5239_, 1, v___x_5251_);
v___x_5253_ = v___x_5239_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_toInputContext_5235_);
lean_ctor_set(v_reuseFailAlloc_5254_, 1, v___x_5251_);
lean_ctor_set(v_reuseFailAlloc_5254_, 2, v_toCacheableParserContext_5236_);
lean_ctor_set(v_reuseFailAlloc_5254_, 3, v_tokens_5237_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
v_resetjp_5258_:
{
lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; 
v___x_5261_ = l_Lean_Syntax_getId(v_nameStx_5231_);
v___x_5262_ = l_Lean_Name_eraseMacroScopes(v___x_5261_);
lean_dec(v___x_5261_);
lean_inc(v___x_5262_);
v___x_5263_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_5262_, v_v_5232_, v_map_5256_);
if (v_hasTrace_5257_ == 0)
{
lean_object* v___x_5264_; uint8_t v___x_5265_; lean_object* v___x_5267_; 
v___x_5264_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_5265_ = l_Lean_Name_isPrefixOf(v___x_5264_, v___x_5262_);
lean_dec(v___x_5262_);
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 0, v___x_5263_);
v___x_5267_ = v___x_5259_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v___x_5263_);
v___x_5267_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
lean_ctor_set_uint8(v___x_5267_, sizeof(void*)*1, v___x_5265_);
v___y_5249_ = v___x_5267_;
goto v___jp_5248_;
}
}
else
{
lean_object* v___x_5270_; 
lean_dec(v___x_5262_);
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 0, v___x_5263_);
v___x_5270_ = v___x_5259_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v___x_5263_);
lean_ctor_set_uint8(v_reuseFailAlloc_5271_, sizeof(void*)*1, v_hasTrace_5257_);
v___x_5270_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
v___y_5249_ = v___x_5270_;
goto v___jp_5248_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object* v_nameStx_5275_, lean_object* v_v_5276_, lean_object* v_c_5277_){
_start:
{
lean_object* v_res_5278_; 
v_res_5278_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(v_nameStx_5275_, v_v_5276_, v_c_5277_);
lean_dec(v_nameStx_5275_);
return v_res_5278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object* v_nameStx_5279_, lean_object* v_valStx_5280_, lean_object* v_p_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_){
_start:
{
lean_object* v___x_5284_; 
v___x_5284_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_valStx_5280_);
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v___x_5285_; 
lean_dec(v_nameStx_5279_);
v___x_5285_ = lean_apply_2(v_p_5281_, v_a_5282_, v_a_5283_);
return v___x_5285_;
}
else
{
lean_object* v_val_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; 
v_val_5286_ = lean_ctor_get(v___x_5284_, 0);
lean_inc(v_val_5286_);
lean_dec_ref_known(v___x_5284_, 1);
v___x_5287_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed), 3, 2);
lean_closure_set(v___x_5287_, 0, v_nameStx_5279_);
lean_closure_set(v___x_5287_, 1, v_val_5286_);
v___x_5288_ = l_Lean_Parser_adaptUncacheableContextFn(v___x_5287_, v_p_5281_, v_a_5282_, v_a_5283_);
return v___x_5288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object* v_nameStx_5289_, lean_object* v_valStx_5290_, lean_object* v_p_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v_nameStx_5289_, v_valStx_5290_, v_p_5291_, v_a_5292_, v_a_5293_);
lean_dec(v_valStx_5290_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object* v_p_5301_, lean_object* v_c_5302_, lean_object* v_s_5303_){
_start:
{
lean_object* v_stxStack_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; uint8_t v___x_5307_; 
v_stxStack_5304_ = lean_ctor_get(v_s_5303_, 0);
v___x_5305_ = lean_unsigned_to_nat(0u);
v___x_5306_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5304_);
v___x_5307_ = lean_nat_dec_lt(v___x_5305_, v___x_5306_);
lean_dec(v___x_5306_);
if (v___x_5307_ == 0)
{
lean_object* v___x_5308_; 
v___x_5308_ = lean_apply_2(v_p_5301_, v_c_5302_, v_s_5303_);
return v___x_5308_;
}
else
{
lean_object* v_stx_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; uint8_t v___x_5312_; 
v_stx_5309_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5304_);
lean_inc(v_stx_5309_);
v___x_5310_ = l_Lean_Syntax_getKind(v_stx_5309_);
v___x_5311_ = ((lean_object*)(l_Lean_Parser_withSetOptionFn___closed__1));
v___x_5312_ = lean_name_eq(v___x_5310_, v___x_5311_);
lean_dec(v___x_5310_);
if (v___x_5312_ == 0)
{
lean_object* v___x_5313_; 
lean_dec(v_stx_5309_);
v___x_5313_ = lean_apply_2(v_p_5301_, v_c_5302_, v_s_5303_);
return v___x_5313_;
}
else
{
lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5314_ = lean_unsigned_to_nat(1u);
v___x_5315_ = l_Lean_Syntax_getArg(v_stx_5309_, v___x_5314_);
v___x_5316_ = lean_unsigned_to_nat(3u);
v___x_5317_ = l_Lean_Syntax_getArg(v_stx_5309_, v___x_5316_);
lean_dec(v_stx_5309_);
v___x_5318_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5315_, v___x_5317_, v_p_5301_, v_c_5302_, v_s_5303_);
lean_dec(v___x_5317_);
return v___x_5318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object* v_p_5319_){
_start:
{
lean_object* v_info_5320_; lean_object* v_fn_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5329_; 
v_info_5320_ = lean_ctor_get(v_p_5319_, 0);
v_fn_5321_ = lean_ctor_get(v_p_5319_, 1);
v_isSharedCheck_5329_ = !lean_is_exclusive(v_p_5319_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5323_ = v_p_5319_;
v_isShared_5324_ = v_isSharedCheck_5329_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_fn_5321_);
lean_inc(v_info_5320_);
lean_dec(v_p_5319_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5329_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5325_; lean_object* v___x_5327_; 
v___x_5325_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionFn), 3, 1);
lean_closure_set(v___x_5325_, 0, v_fn_5321_);
if (v_isShared_5324_ == 0)
{
lean_ctor_set(v___x_5323_, 1, v___x_5325_);
v___x_5327_ = v___x_5323_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_info_5320_);
lean_ctor_set(v_reuseFailAlloc_5328_, 1, v___x_5325_);
v___x_5327_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
return v___x_5327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object* v_p_5330_, lean_object* v_c_5331_, lean_object* v_s_5332_){
_start:
{
lean_object* v_stxStack_5333_; lean_object* v_sz_5334_; lean_object* v___x_5335_; uint8_t v___x_5336_; 
v_stxStack_5333_ = lean_ctor_get(v_s_5332_, 0);
v_sz_5334_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5333_);
v___x_5335_ = lean_unsigned_to_nat(3u);
v___x_5336_ = lean_nat_dec_le(v___x_5335_, v_sz_5334_);
if (v___x_5336_ == 0)
{
lean_object* v___x_5337_; 
lean_dec(v_sz_5334_);
v___x_5337_ = lean_apply_2(v_p_5330_, v_c_5331_, v_s_5332_);
return v___x_5337_;
}
else
{
lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; 
v___x_5338_ = lean_nat_sub(v_sz_5334_, v___x_5335_);
lean_dec(v_sz_5334_);
v___x_5339_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5333_, v___x_5338_);
lean_dec(v___x_5338_);
v___x_5340_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5333_);
v___x_5341_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5339_, v___x_5340_, v_p_5330_, v_c_5331_, v_s_5332_);
lean_dec(v___x_5340_);
return v___x_5341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object* v_p_5342_){
_start:
{
lean_object* v_info_5343_; lean_object* v_fn_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5352_; 
v_info_5343_ = lean_ctor_get(v_p_5342_, 0);
v_fn_5344_ = lean_ctor_get(v_p_5342_, 1);
v_isSharedCheck_5352_ = !lean_is_exclusive(v_p_5342_);
if (v_isSharedCheck_5352_ == 0)
{
v___x_5346_ = v_p_5342_;
v_isShared_5347_ = v_isSharedCheck_5352_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_fn_5344_);
lean_inc(v_info_5343_);
lean_dec(v_p_5342_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5352_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v___x_5348_; lean_object* v___x_5350_; 
v___x_5348_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionValueFn), 3, 1);
lean_closure_set(v___x_5348_, 0, v_fn_5344_);
if (v_isShared_5347_ == 0)
{
lean_ctor_set(v___x_5346_, 1, v___x_5348_);
v___x_5350_ = v___x_5346_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_info_5343_);
lean_ctor_set(v_reuseFailAlloc_5351_, 1, v___x_5348_);
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object* v___x_5353_){
_start:
{
lean_object* v___x_5355_; lean_object* v___x_5356_; 
v___x_5355_ = lean_st_ref_get(v___x_5353_);
v___x_5356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5356_, 0, v___x_5355_);
return v___x_5356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v___x_5357_, lean_object* v___y_5358_){
_start:
{
lean_object* v_res_5359_; 
v_res_5359_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_5357_);
lean_dec(v___x_5357_);
return v_res_5359_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5360_; lean_object* v___f_5361_; 
v___x_5360_ = l_Lean_Parser_parserAliasesRef;
v___f_5361_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5361_, 0, v___x_5360_);
return v___f_5361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; uint8_t v___x_5372_; lean_object* v___x_5373_; 
v___f_5368_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_);
v___x_5369_ = lean_box(0);
v___x_5370_ = lean_box(2);
v___x_5371_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_));
v___x_5372_ = 0;
v___x_5373_ = l_Lean_registerEnvExtension___redArg(v___f_5368_, v___x_5369_, v___x_5370_, v___x_5371_, v___x_5372_, v___x_5372_);
return v___x_5373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v_a_5374_){
_start:
{
lean_object* v_res_5375_; 
v_res_5375_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
return v_res_5375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___impl(lean_object* v_x_5376_){
_start:
{
lean_object* v___x_5377_; 
v___x_5377_ = lean_obj_tag_nat(v_x_5376_);
return v___x_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___impl___boxed(lean_object* v_x_5378_){
_start:
{
lean_object* v_res_5379_; 
v_res_5379_ = l_Lean_Parser_ParserResolution_ctorIdx___impl(v_x_5378_);
lean_dec_ref(v_x_5378_);
return v_res_5379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object* v_t_5380_, lean_object* v_k_5381_){
_start:
{
switch(lean_obj_tag(v_t_5380_))
{
case 0:
{
lean_object* v_cat_5382_; lean_object* v___x_5383_; 
v_cat_5382_ = lean_ctor_get(v_t_5380_, 0);
lean_inc(v_cat_5382_);
lean_dec_ref_known(v_t_5380_, 1);
v___x_5383_ = lean_apply_1(v_k_5381_, v_cat_5382_);
return v___x_5383_;
}
case 1:
{
lean_object* v_decl_5384_; uint8_t v_isDescr_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; 
v_decl_5384_ = lean_ctor_get(v_t_5380_, 0);
lean_inc(v_decl_5384_);
v_isDescr_5385_ = lean_ctor_get_uint8(v_t_5380_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5380_, 1);
v___x_5386_ = lean_box(v_isDescr_5385_);
v___x_5387_ = lean_apply_2(v_k_5381_, v_decl_5384_, v___x_5386_);
return v___x_5387_;
}
default: 
{
lean_object* v_p_5388_; lean_object* v___x_5389_; 
v_p_5388_ = lean_ctor_get(v_t_5380_, 0);
lean_inc_ref(v_p_5388_);
lean_dec_ref_known(v_t_5380_, 1);
v___x_5389_ = lean_apply_1(v_k_5381_, v_p_5388_);
return v___x_5389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object* v_motive_5390_, lean_object* v_ctorIdx_5391_, lean_object* v_t_5392_, lean_object* v_h_5393_, lean_object* v_k_5394_){
_start:
{
lean_object* v___x_5395_; 
v___x_5395_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5392_, v_k_5394_);
return v___x_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object* v_motive_5396_, lean_object* v_ctorIdx_5397_, lean_object* v_t_5398_, lean_object* v_h_5399_, lean_object* v_k_5400_){
_start:
{
lean_object* v_res_5401_; 
v_res_5401_ = l_Lean_Parser_ParserResolution_ctorElim(v_motive_5396_, v_ctorIdx_5397_, v_t_5398_, v_h_5399_, v_k_5400_);
lean_dec(v_ctorIdx_5397_);
return v_res_5401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object* v_t_5402_, lean_object* v_category_5403_){
_start:
{
lean_object* v___x_5404_; 
v___x_5404_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5402_, v_category_5403_);
return v___x_5404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object* v_motive_5405_, lean_object* v_t_5406_, lean_object* v_h_5407_, lean_object* v_category_5408_){
_start:
{
lean_object* v___x_5409_; 
v___x_5409_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5406_, v_category_5408_);
return v___x_5409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object* v_t_5410_, lean_object* v_parser_5411_){
_start:
{
lean_object* v___x_5412_; 
v___x_5412_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5410_, v_parser_5411_);
return v___x_5412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object* v_motive_5413_, lean_object* v_t_5414_, lean_object* v_h_5415_, lean_object* v_parser_5416_){
_start:
{
lean_object* v___x_5417_; 
v___x_5417_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5414_, v_parser_5416_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object* v_t_5418_, lean_object* v_alias_5419_){
_start:
{
lean_object* v___x_5420_; 
v___x_5420_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5418_, v_alias_5419_);
return v___x_5420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object* v_motive_5421_, lean_object* v_t_5422_, lean_object* v_h_5423_, lean_object* v_alias_5424_){
_start:
{
lean_object* v___x_5425_; 
v___x_5425_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5422_, v_alias_5424_);
return v___x_5425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object* v_env_5429_, lean_object* v_name_5430_){
_start:
{
uint8_t v___x_5431_; lean_object* v___x_5432_; 
v___x_5431_ = 0;
v___x_5432_ = l_Lean_Environment_find_x3f(v_env_5429_, v_name_5430_, v___x_5431_);
if (lean_obj_tag(v___x_5432_) == 0)
{
lean_object* v___x_5433_; 
v___x_5433_ = lean_box(0);
return v___x_5433_;
}
else
{
lean_object* v_val_5434_; lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5481_; 
v_val_5434_ = lean_ctor_get(v___x_5432_, 0);
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5432_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5436_ = v___x_5432_;
v_isShared_5437_ = v_isSharedCheck_5481_;
goto v_resetjp_5435_;
}
else
{
lean_inc(v_val_5434_);
lean_dec(v___x_5432_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5481_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v___x_5438_; 
v___x_5438_ = l_Lean_ConstantInfo_type(v_val_5434_);
lean_dec(v_val_5434_);
if (lean_obj_tag(v___x_5438_) == 4)
{
lean_object* v_declName_5439_; 
v_declName_5439_ = lean_ctor_get(v___x_5438_, 0);
lean_inc(v_declName_5439_);
lean_dec_ref_known(v___x_5438_, 2);
if (lean_obj_tag(v_declName_5439_) == 1)
{
lean_object* v_pre_5440_; 
v_pre_5440_ = lean_ctor_get(v_declName_5439_, 0);
lean_inc(v_pre_5440_);
if (lean_obj_tag(v_pre_5440_) == 1)
{
lean_object* v_pre_5441_; 
v_pre_5441_ = lean_ctor_get(v_pre_5440_, 0);
switch(lean_obj_tag(v_pre_5441_))
{
case 1:
{
lean_object* v_pre_5442_; 
lean_inc_ref(v_pre_5441_);
lean_del_object(v___x_5436_);
v_pre_5442_ = lean_ctor_get(v_pre_5441_, 0);
if (lean_obj_tag(v_pre_5442_) == 0)
{
lean_object* v_str_5443_; lean_object* v_str_5444_; lean_object* v_str_5445_; lean_object* v___x_5446_; uint8_t v___x_5447_; 
v_str_5443_ = lean_ctor_get(v_declName_5439_, 1);
lean_inc_ref(v_str_5443_);
lean_dec_ref_known(v_declName_5439_, 2);
v_str_5444_ = lean_ctor_get(v_pre_5440_, 1);
lean_inc_ref(v_str_5444_);
lean_dec_ref_known(v_pre_5440_, 2);
v_str_5445_ = lean_ctor_get(v_pre_5441_, 1);
lean_inc_ref(v_str_5445_);
lean_dec_ref_known(v_pre_5441_, 2);
v___x_5446_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5447_ = lean_string_dec_eq(v_str_5445_, v___x_5446_);
lean_dec_ref(v_str_5445_);
if (v___x_5447_ == 0)
{
lean_object* v___x_5448_; 
lean_dec_ref(v_str_5444_);
lean_dec_ref(v_str_5443_);
v___x_5448_ = lean_box(0);
return v___x_5448_;
}
else
{
lean_object* v___x_5449_; uint8_t v___x_5450_; 
v___x_5449_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_5450_ = lean_string_dec_eq(v_str_5444_, v___x_5449_);
lean_dec_ref(v_str_5444_);
if (v___x_5450_ == 0)
{
lean_object* v___x_5451_; 
lean_dec_ref(v_str_5443_);
v___x_5451_ = lean_box(0);
return v___x_5451_;
}
else
{
uint8_t v___x_5452_; 
v___x_5452_ = lean_string_dec_eq(v_str_5443_, v___x_5449_);
if (v___x_5452_ == 0)
{
lean_object* v___x_5453_; uint8_t v___x_5454_; 
v___x_5453_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_5454_ = lean_string_dec_eq(v_str_5443_, v___x_5453_);
lean_dec_ref(v_str_5443_);
if (v___x_5454_ == 0)
{
lean_object* v___x_5455_; 
v___x_5455_ = lean_box(0);
return v___x_5455_;
}
else
{
lean_object* v___x_5456_; 
v___x_5456_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5456_;
}
}
else
{
lean_object* v___x_5457_; 
lean_dec_ref(v_str_5443_);
v___x_5457_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5457_;
}
}
}
}
else
{
lean_object* v___x_5458_; 
lean_dec_ref_known(v_pre_5441_, 2);
lean_dec_ref_known(v_pre_5440_, 2);
lean_dec_ref_known(v_declName_5439_, 2);
v___x_5458_ = lean_box(0);
return v___x_5458_;
}
}
case 0:
{
lean_object* v_str_5459_; lean_object* v_str_5460_; lean_object* v___x_5461_; uint8_t v___x_5462_; 
v_str_5459_ = lean_ctor_get(v_declName_5439_, 1);
lean_inc_ref(v_str_5459_);
lean_dec_ref_known(v_declName_5439_, 2);
v_str_5460_ = lean_ctor_get(v_pre_5440_, 1);
lean_inc_ref(v_str_5460_);
lean_dec_ref_known(v_pre_5440_, 2);
v___x_5461_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5462_ = lean_string_dec_eq(v_str_5460_, v___x_5461_);
lean_dec_ref(v_str_5460_);
if (v___x_5462_ == 0)
{
lean_object* v___x_5463_; 
lean_dec_ref(v_str_5459_);
lean_del_object(v___x_5436_);
v___x_5463_ = lean_box(0);
return v___x_5463_;
}
else
{
lean_object* v___x_5464_; uint8_t v___x_5465_; 
v___x_5464_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_5465_ = lean_string_dec_eq(v_str_5459_, v___x_5464_);
if (v___x_5465_ == 0)
{
lean_object* v___x_5466_; uint8_t v___x_5467_; 
v___x_5466_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_5467_ = lean_string_dec_eq(v_str_5459_, v___x_5466_);
lean_dec_ref(v_str_5459_);
if (v___x_5467_ == 0)
{
lean_object* v___x_5468_; 
lean_del_object(v___x_5436_);
v___x_5468_ = lean_box(0);
return v___x_5468_;
}
else
{
lean_object* v___x_5469_; lean_object* v___x_5471_; 
v___x_5469_ = lean_box(v___x_5462_);
if (v_isShared_5437_ == 0)
{
lean_ctor_set(v___x_5436_, 0, v___x_5469_);
v___x_5471_ = v___x_5436_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v___x_5469_);
v___x_5471_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
return v___x_5471_;
}
}
}
else
{
lean_object* v___x_5473_; lean_object* v___x_5475_; 
lean_dec_ref(v_str_5459_);
v___x_5473_ = lean_box(v___x_5462_);
if (v_isShared_5437_ == 0)
{
lean_ctor_set(v___x_5436_, 0, v___x_5473_);
v___x_5475_ = v___x_5436_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5476_; 
v_reuseFailAlloc_5476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5476_, 0, v___x_5473_);
v___x_5475_ = v_reuseFailAlloc_5476_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
return v___x_5475_;
}
}
}
}
default: 
{
lean_object* v___x_5477_; 
lean_dec_ref_known(v_pre_5440_, 2);
lean_dec_ref_known(v_declName_5439_, 2);
lean_del_object(v___x_5436_);
v___x_5477_ = lean_box(0);
return v___x_5477_;
}
}
}
else
{
lean_object* v___x_5478_; 
lean_dec(v_pre_5440_);
lean_dec_ref_known(v_declName_5439_, 2);
lean_del_object(v___x_5436_);
v___x_5478_ = lean_box(0);
return v___x_5478_;
}
}
else
{
lean_object* v___x_5479_; 
lean_dec(v_declName_5439_);
lean_del_object(v___x_5436_);
v___x_5479_ = lean_box(0);
return v___x_5479_;
}
}
else
{
lean_object* v___x_5480_; 
lean_dec_ref(v___x_5438_);
lean_del_object(v___x_5436_);
v___x_5480_ = lean_box(0);
return v___x_5480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object* v_env_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_){
_start:
{
if (lean_obj_tag(v_a_5483_) == 0)
{
lean_object* v___x_5485_; 
lean_dec_ref(v_env_5482_);
v___x_5485_ = lean_array_to_list(v_a_5484_);
return v___x_5485_;
}
else
{
lean_object* v_head_5486_; lean_object* v_snd_5487_; 
v_head_5486_ = lean_ctor_get(v_a_5483_, 0);
v_snd_5487_ = lean_ctor_get(v_head_5486_, 1);
if (lean_obj_tag(v_snd_5487_) == 0)
{
lean_object* v_tail_5488_; lean_object* v_fst_5489_; lean_object* v___x_5490_; 
lean_inc(v_head_5486_);
v_tail_5488_ = lean_ctor_get(v_a_5483_, 1);
lean_inc(v_tail_5488_);
lean_dec_ref_known(v_a_5483_, 2);
v_fst_5489_ = lean_ctor_get(v_head_5486_, 0);
lean_inc_n(v_fst_5489_, 2);
lean_dec(v_head_5486_);
lean_inc_ref(v_env_5482_);
v___x_5490_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5482_, v_fst_5489_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_dec(v_fst_5489_);
v_a_5483_ = v_tail_5488_;
goto _start;
}
else
{
lean_object* v_val_5492_; lean_object* v___x_5493_; uint8_t v___x_5494_; lean_object* v___x_5495_; 
v_val_5492_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_val_5492_);
lean_dec_ref_known(v___x_5490_, 1);
v___x_5493_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5493_, 0, v_fst_5489_);
v___x_5494_ = lean_unbox(v_val_5492_);
lean_dec(v_val_5492_);
lean_ctor_set_uint8(v___x_5493_, sizeof(void*)*1, v___x_5494_);
v___x_5495_ = lean_array_push(v_a_5484_, v___x_5493_);
v_a_5483_ = v_tail_5488_;
v_a_5484_ = v___x_5495_;
goto _start;
}
}
else
{
lean_object* v_tail_5497_; 
v_tail_5497_ = lean_ctor_get(v_a_5483_, 1);
lean_inc(v_tail_5497_);
lean_dec_ref_known(v_a_5483_, 2);
v_a_5483_ = v_tail_5497_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object* v_env_5502_, lean_object* v_as_x27_5503_, lean_object* v_b_5504_){
_start:
{
if (lean_obj_tag(v_as_x27_5503_) == 0)
{
lean_dec_ref(v_env_5502_);
lean_inc_ref(v_b_5504_);
return v_b_5504_;
}
else
{
lean_object* v_head_5505_; lean_object* v_tail_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; 
v_head_5505_ = lean_ctor_get(v_as_x27_5503_, 0);
v_tail_5506_ = lean_ctor_get(v_as_x27_5503_, 1);
v___x_5507_ = lean_box(0);
v___x_5508_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_5505_) == 1)
{
lean_object* v_fields_5509_; 
v_fields_5509_ = lean_ctor_get(v_head_5505_, 1);
if (lean_obj_tag(v_fields_5509_) == 0)
{
lean_object* v_n_5510_; lean_object* v___x_5511_; 
v_n_5510_ = lean_ctor_get(v_head_5505_, 0);
lean_inc(v_n_5510_);
lean_inc_ref(v_env_5502_);
v___x_5511_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5502_, v_n_5510_);
if (lean_obj_tag(v___x_5511_) == 1)
{
lean_object* v_val_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5524_; 
lean_dec_ref(v_env_5502_);
v_val_5512_ = lean_ctor_get(v___x_5511_, 0);
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5511_);
if (v_isSharedCheck_5524_ == 0)
{
v___x_5514_ = v___x_5511_;
v_isShared_5515_ = v_isSharedCheck_5524_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_val_5512_);
lean_dec(v___x_5511_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5524_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5516_; uint8_t v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5521_; 
lean_inc(v_n_5510_);
v___x_5516_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5516_, 0, v_n_5510_);
v___x_5517_ = lean_unbox(v_val_5512_);
lean_dec(v_val_5512_);
lean_ctor_set_uint8(v___x_5516_, sizeof(void*)*1, v___x_5517_);
v___x_5518_ = lean_box(0);
v___x_5519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5519_, 0, v___x_5516_);
lean_ctor_set(v___x_5519_, 1, v___x_5518_);
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 0, v___x_5519_);
v___x_5521_ = v___x_5514_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v___x_5519_);
v___x_5521_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
lean_object* v___x_5522_; 
v___x_5522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5522_, 0, v___x_5521_);
lean_ctor_set(v___x_5522_, 1, v___x_5507_);
return v___x_5522_;
}
}
}
else
{
lean_dec(v___x_5511_);
v_as_x27_5503_ = v_tail_5506_;
v_b_5504_ = v___x_5508_;
goto _start;
}
}
else
{
v_as_x27_5503_ = v_tail_5506_;
v_b_5504_ = v___x_5508_;
goto _start;
}
}
else
{
v_as_x27_5503_ = v_tail_5506_;
v_b_5504_ = v___x_5508_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object* v_env_5528_, lean_object* v_as_x27_5529_, lean_object* v_b_5530_){
_start:
{
lean_object* v_res_5531_; 
v_res_5531_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5528_, v_as_x27_5529_, v_b_5530_);
lean_dec_ref(v_b_5530_);
lean_dec(v_as_x27_5529_);
return v_res_5531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object* v_env_5534_, lean_object* v_opts_5535_, lean_object* v_currNamespace_5536_, lean_object* v_openDecls_5537_, lean_object* v_ident_5538_){
_start:
{
if (lean_obj_tag(v_ident_5538_) == 3)
{
lean_object* v_val_5539_; lean_object* v_preresolved_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v_fst_5543_; lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5578_; 
v_val_5539_ = lean_ctor_get(v_ident_5538_, 2);
lean_inc(v_val_5539_);
v_preresolved_5540_ = lean_ctor_get(v_ident_5538_, 3);
lean_inc(v_preresolved_5540_);
lean_dec_ref_known(v_ident_5538_, 4);
v___x_5541_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
lean_inc_ref(v_env_5534_);
v___x_5542_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5534_, v_preresolved_5540_, v___x_5541_);
lean_dec(v_preresolved_5540_);
v_fst_5543_ = lean_ctor_get(v___x_5542_, 0);
v_isSharedCheck_5578_ = !lean_is_exclusive(v___x_5542_);
if (v_isSharedCheck_5578_ == 0)
{
lean_object* v_unused_5579_; 
v_unused_5579_ = lean_ctor_get(v___x_5542_, 1);
lean_dec(v_unused_5579_);
v___x_5545_ = v___x_5542_;
v_isShared_5546_ = v_isSharedCheck_5578_;
goto v_resetjp_5544_;
}
else
{
lean_inc(v_fst_5543_);
lean_dec(v___x_5542_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5578_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
if (lean_obj_tag(v_fst_5543_) == 0)
{
lean_object* v___x_5547_; uint8_t v___x_5548_; 
v___x_5547_ = l_Lean_Name_eraseMacroScopes(v_val_5539_);
lean_inc_ref(v_env_5534_);
v___x_5548_ = l_Lean_Parser_isParserCategory(v_env_5534_, v___x_5547_);
if (v___x_5548_ == 0)
{
lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; uint8_t v___x_5552_; 
lean_inc_ref_n(v_env_5534_, 2);
v___x_5549_ = l_Lean_ResolveName_resolveGlobalName(v_env_5534_, v_opts_5535_, v_currNamespace_5536_, v_openDecls_5537_, v_val_5539_);
v___x_5550_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0));
v___x_5551_ = l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(v_env_5534_, v___x_5549_, v___x_5550_);
v___x_5552_ = l_List_isEmpty___redArg(v___x_5551_);
if (v___x_5552_ == 0)
{
lean_dec(v___x_5547_);
lean_del_object(v___x_5545_);
lean_dec_ref(v_env_5534_);
return v___x_5551_;
}
else
{
lean_object* v___x_5553_; lean_object* v_asyncMode_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; 
lean_dec(v___x_5551_);
v___x_5553_ = l_Lean_Parser_aliasExtension;
v_asyncMode_5554_ = lean_ctor_get(v___x_5553_, 2);
v___x_5555_ = lean_box(1);
v___x_5556_ = lean_box(0);
v___x_5557_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5555_, v___x_5553_, v_env_5534_, v_asyncMode_5554_, v___x_5556_, v___x_5548_);
v___x_5558_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5557_, v___x_5547_);
lean_dec(v___x_5547_);
lean_dec(v___x_5557_);
if (lean_obj_tag(v___x_5558_) == 1)
{
lean_object* v_val_5559_; lean_object* v___x_5561_; uint8_t v_isShared_5562_; uint8_t v_isSharedCheck_5570_; 
v_val_5559_ = lean_ctor_get(v___x_5558_, 0);
v_isSharedCheck_5570_ = !lean_is_exclusive(v___x_5558_);
if (v_isSharedCheck_5570_ == 0)
{
v___x_5561_ = v___x_5558_;
v_isShared_5562_ = v_isSharedCheck_5570_;
goto v_resetjp_5560_;
}
else
{
lean_inc(v_val_5559_);
lean_dec(v___x_5558_);
v___x_5561_ = lean_box(0);
v_isShared_5562_ = v_isSharedCheck_5570_;
goto v_resetjp_5560_;
}
v_resetjp_5560_:
{
lean_object* v___x_5564_; 
if (v_isShared_5562_ == 0)
{
lean_ctor_set_tag(v___x_5561_, 2);
v___x_5564_ = v___x_5561_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_val_5559_);
v___x_5564_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
lean_object* v___x_5565_; lean_object* v___x_5567_; 
v___x_5565_ = lean_box(0);
if (v_isShared_5546_ == 0)
{
lean_ctor_set_tag(v___x_5545_, 1);
lean_ctor_set(v___x_5545_, 1, v___x_5565_);
lean_ctor_set(v___x_5545_, 0, v___x_5564_);
v___x_5567_ = v___x_5545_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5564_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v___x_5565_);
v___x_5567_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
return v___x_5567_;
}
}
}
}
else
{
lean_object* v___x_5571_; 
lean_dec(v___x_5558_);
lean_del_object(v___x_5545_);
v___x_5571_ = lean_box(0);
return v___x_5571_;
}
}
}
else
{
lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5575_; 
lean_dec(v_val_5539_);
lean_dec(v_openDecls_5537_);
lean_dec(v_currNamespace_5536_);
lean_dec_ref(v_env_5534_);
v___x_5572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5572_, 0, v___x_5547_);
v___x_5573_ = lean_box(0);
if (v_isShared_5546_ == 0)
{
lean_ctor_set_tag(v___x_5545_, 1);
lean_ctor_set(v___x_5545_, 1, v___x_5573_);
lean_ctor_set(v___x_5545_, 0, v___x_5572_);
v___x_5575_ = v___x_5545_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v___x_5572_);
lean_ctor_set(v_reuseFailAlloc_5576_, 1, v___x_5573_);
v___x_5575_ = v_reuseFailAlloc_5576_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
return v___x_5575_;
}
}
}
else
{
lean_object* v_val_5577_; 
lean_del_object(v___x_5545_);
lean_dec(v_val_5539_);
lean_dec(v_openDecls_5537_);
lean_dec(v_currNamespace_5536_);
lean_dec_ref(v_env_5534_);
v_val_5577_ = lean_ctor_get(v_fst_5543_, 0);
lean_inc(v_val_5577_);
lean_dec_ref_known(v_fst_5543_, 1);
return v_val_5577_;
}
}
}
else
{
lean_object* v___x_5580_; 
lean_dec(v_ident_5538_);
lean_dec(v_openDecls_5537_);
lean_dec(v_currNamespace_5536_);
lean_dec_ref(v_env_5534_);
v___x_5580_ = lean_box(0);
return v___x_5580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object* v_env_5581_, lean_object* v_opts_5582_, lean_object* v_currNamespace_5583_, lean_object* v_openDecls_5584_, lean_object* v_ident_5585_){
_start:
{
lean_object* v_res_5586_; 
v_res_5586_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5581_, v_opts_5582_, v_currNamespace_5583_, v_openDecls_5584_, v_ident_5585_);
lean_dec_ref(v_opts_5582_);
return v_res_5586_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object* v_env_5587_, lean_object* v_as_5588_, lean_object* v_as_x27_5589_, lean_object* v_b_5590_, lean_object* v_a_5591_){
_start:
{
lean_object* v___x_5592_; 
v___x_5592_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5587_, v_as_x27_5589_, v_b_5590_);
return v___x_5592_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object* v_env_5593_, lean_object* v_as_5594_, lean_object* v_as_x27_5595_, lean_object* v_b_5596_, lean_object* v_a_5597_){
_start:
{
lean_object* v_res_5598_; 
v_res_5598_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(v_env_5593_, v_as_5594_, v_as_x27_5595_, v_b_5596_, v_a_5597_);
lean_dec_ref(v_b_5596_);
lean_dec(v_as_x27_5595_);
lean_dec(v_as_5594_);
return v_res_5598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object* v_ctx_5599_, lean_object* v_id_5600_, uint8_t v_unsetExporting_5601_){
_start:
{
lean_object* v___y_5603_; 
if (v_unsetExporting_5601_ == 0)
{
lean_object* v_toParserModuleContext_5609_; lean_object* v_env_5610_; 
v_toParserModuleContext_5609_ = lean_ctor_get(v_ctx_5599_, 1);
v_env_5610_ = lean_ctor_get(v_toParserModuleContext_5609_, 0);
lean_inc_ref(v_env_5610_);
v___y_5603_ = v_env_5610_;
goto v___jp_5602_;
}
else
{
lean_object* v_toParserModuleContext_5611_; lean_object* v_env_5612_; uint8_t v___x_5613_; lean_object* v___x_5614_; 
v_toParserModuleContext_5611_ = lean_ctor_get(v_ctx_5599_, 1);
v_env_5612_ = lean_ctor_get(v_toParserModuleContext_5611_, 0);
v___x_5613_ = 0;
lean_inc_ref(v_env_5612_);
v___x_5614_ = l_Lean_Environment_setExporting(v_env_5612_, v___x_5613_);
v___y_5603_ = v___x_5614_;
goto v___jp_5602_;
}
v___jp_5602_:
{
lean_object* v_toParserModuleContext_5604_; lean_object* v_options_5605_; lean_object* v_currNamespace_5606_; lean_object* v_openDecls_5607_; lean_object* v___x_5608_; 
v_toParserModuleContext_5604_ = lean_ctor_get(v_ctx_5599_, 1);
lean_inc_ref(v_toParserModuleContext_5604_);
lean_dec_ref(v_ctx_5599_);
v_options_5605_ = lean_ctor_get(v_toParserModuleContext_5604_, 1);
lean_inc_ref(v_options_5605_);
v_currNamespace_5606_ = lean_ctor_get(v_toParserModuleContext_5604_, 2);
lean_inc(v_currNamespace_5606_);
v_openDecls_5607_ = lean_ctor_get(v_toParserModuleContext_5604_, 3);
lean_inc(v_openDecls_5607_);
lean_dec_ref(v_toParserModuleContext_5604_);
v___x_5608_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v___y_5603_, v_options_5605_, v_currNamespace_5606_, v_openDecls_5607_, v_id_5600_);
lean_dec_ref(v_options_5605_);
return v___x_5608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object* v_ctx_5615_, lean_object* v_id_5616_, lean_object* v_unsetExporting_5617_){
_start:
{
uint8_t v_unsetExporting_boxed_5618_; lean_object* v_res_5619_; 
v_unsetExporting_boxed_5618_ = lean_unbox(v_unsetExporting_5617_);
v_res_5619_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5615_, v_id_5616_, v_unsetExporting_boxed_5618_);
return v_res_5619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object* v_id_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_){
_start:
{
lean_object* v___x_5624_; lean_object* v_toCold_5625_; lean_object* v_env_5626_; lean_object* v_currNamespace_5627_; lean_object* v_openDecls_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5624_ = lean_st_ref_get(v_a_5622_);
v_toCold_5625_ = lean_ctor_get(v_a_5621_, 0);
v_env_5626_ = lean_ctor_get(v___x_5624_, 0);
lean_inc_ref(v_env_5626_);
lean_dec(v___x_5624_);
v_currNamespace_5627_ = lean_ctor_get(v_toCold_5625_, 4);
v_openDecls_5628_ = lean_ctor_get(v_toCold_5625_, 5);
v___x_5629_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_5621_);
lean_inc(v_openDecls_5628_);
lean_inc(v_currNamespace_5627_);
v___x_5630_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5626_, v___x_5629_, v_currNamespace_5627_, v_openDecls_5628_, v_id_5620_);
lean_dec_ref(v___x_5629_);
v___x_5631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5631_, 0, v___x_5630_);
return v___x_5631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object* v_id_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_){
_start:
{
lean_object* v_res_5636_; 
v_res_5636_ = l_Lean_Parser_resolveParserName(v_id_5632_, v_a_5633_, v_a_5634_);
lean_dec(v_a_5634_);
lean_dec_ref(v_a_5633_);
return v_res_5636_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object* v_x_5637_, lean_object* v_x_5638_){
_start:
{
if (lean_obj_tag(v_x_5637_) == 0)
{
if (lean_obj_tag(v_x_5638_) == 0)
{
uint8_t v___x_5639_; 
v___x_5639_ = 1;
return v___x_5639_;
}
else
{
uint8_t v___x_5640_; 
v___x_5640_ = 0;
return v___x_5640_;
}
}
else
{
if (lean_obj_tag(v_x_5638_) == 0)
{
uint8_t v___x_5641_; 
v___x_5641_ = 0;
return v___x_5641_;
}
else
{
lean_object* v_val_5642_; lean_object* v_val_5643_; uint8_t v___x_5644_; 
v_val_5642_ = lean_ctor_get(v_x_5637_, 0);
v_val_5643_ = lean_ctor_get(v_x_5638_, 0);
v___x_5644_ = l_Lean_Parser_instBEqError_beq(v_val_5642_, v_val_5643_);
return v___x_5644_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object* v_x_5645_, lean_object* v_x_5646_){
_start:
{
uint8_t v_res_5647_; lean_object* v_r_5648_; 
v_res_5647_ = l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5645_, v_x_5646_);
lean_dec(v_x_5646_);
lean_dec(v_x_5645_);
v_r_5648_ = lean_box(v_res_5647_);
return v_r_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t v___x_5649_, lean_object* v_ctx_5650_){
_start:
{
lean_object* v_toParserModuleContext_5651_; lean_object* v_toInputContext_5652_; lean_object* v_toCacheableParserContext_5653_; lean_object* v_tokens_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5679_; 
v_toParserModuleContext_5651_ = lean_ctor_get(v_ctx_5650_, 1);
v_toInputContext_5652_ = lean_ctor_get(v_ctx_5650_, 0);
v_toCacheableParserContext_5653_ = lean_ctor_get(v_ctx_5650_, 2);
v_tokens_5654_ = lean_ctor_get(v_ctx_5650_, 3);
v_isSharedCheck_5679_ = !lean_is_exclusive(v_ctx_5650_);
if (v_isSharedCheck_5679_ == 0)
{
v___x_5656_ = v_ctx_5650_;
v_isShared_5657_ = v_isSharedCheck_5679_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_tokens_5654_);
lean_inc(v_toCacheableParserContext_5653_);
lean_inc(v_toParserModuleContext_5651_);
lean_inc(v_toInputContext_5652_);
lean_dec(v_ctx_5650_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5679_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v_env_5658_; lean_object* v_options_5659_; lean_object* v_currNamespace_5660_; lean_object* v_openDecls_5661_; lean_object* v___x_5663_; uint8_t v_isShared_5664_; uint8_t v_isSharedCheck_5678_; 
v_env_5658_ = lean_ctor_get(v_toParserModuleContext_5651_, 0);
v_options_5659_ = lean_ctor_get(v_toParserModuleContext_5651_, 1);
v_currNamespace_5660_ = lean_ctor_get(v_toParserModuleContext_5651_, 2);
v_openDecls_5661_ = lean_ctor_get(v_toParserModuleContext_5651_, 3);
v_isSharedCheck_5678_ = !lean_is_exclusive(v_toParserModuleContext_5651_);
if (v_isSharedCheck_5678_ == 0)
{
v___x_5663_ = v_toParserModuleContext_5651_;
v_isShared_5664_ = v_isSharedCheck_5678_;
goto v_resetjp_5662_;
}
else
{
lean_inc(v_openDecls_5661_);
lean_inc(v_currNamespace_5660_);
lean_inc(v_options_5659_);
lean_inc(v_env_5658_);
lean_dec(v_toParserModuleContext_5651_);
v___x_5663_ = lean_box(0);
v_isShared_5664_ = v_isSharedCheck_5678_;
goto v_resetjp_5662_;
}
v_resetjp_5662_:
{
lean_object* v___x_5665_; uint8_t v___y_5667_; lean_object* v___x_5675_; uint8_t v___x_5676_; 
v___x_5665_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_5675_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_5676_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_5659_, v___x_5675_);
if (v___x_5676_ == 0)
{
uint8_t v___x_5677_; 
v___x_5677_ = 1;
v___y_5667_ = v___x_5677_;
goto v___jp_5666_;
}
else
{
v___y_5667_ = v___x_5649_;
goto v___jp_5666_;
}
v___jp_5666_:
{
lean_object* v___x_5668_; lean_object* v___x_5670_; 
v___x_5668_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_5659_, v___x_5665_, v___y_5667_);
if (v_isShared_5664_ == 0)
{
lean_ctor_set(v___x_5663_, 1, v___x_5668_);
v___x_5670_ = v___x_5663_;
goto v_reusejp_5669_;
}
else
{
lean_object* v_reuseFailAlloc_5674_; 
v_reuseFailAlloc_5674_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_env_5658_);
lean_ctor_set(v_reuseFailAlloc_5674_, 1, v___x_5668_);
lean_ctor_set(v_reuseFailAlloc_5674_, 2, v_currNamespace_5660_);
lean_ctor_set(v_reuseFailAlloc_5674_, 3, v_openDecls_5661_);
v___x_5670_ = v_reuseFailAlloc_5674_;
goto v_reusejp_5669_;
}
v_reusejp_5669_:
{
lean_object* v___x_5672_; 
if (v_isShared_5657_ == 0)
{
lean_ctor_set(v___x_5656_, 1, v___x_5670_);
v___x_5672_ = v___x_5656_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5673_; 
v_reuseFailAlloc_5673_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5673_, 0, v_toInputContext_5652_);
lean_ctor_set(v_reuseFailAlloc_5673_, 1, v___x_5670_);
lean_ctor_set(v_reuseFailAlloc_5673_, 2, v_toCacheableParserContext_5653_);
lean_ctor_set(v_reuseFailAlloc_5673_, 3, v_tokens_5654_);
v___x_5672_ = v_reuseFailAlloc_5673_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
return v___x_5672_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object* v___x_5680_, lean_object* v_ctx_5681_){
_start:
{
uint8_t v___x_1068__boxed_5682_; lean_object* v_res_5683_; 
v___x_1068__boxed_5682_ = lean_unbox(v___x_5680_);
v_res_5683_ = l_Lean_Parser_parserOfStackFn___lam__0(v___x_1068__boxed_5682_, v_ctx_5681_);
return v_res_5683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* v_offset_5691_, lean_object* v_ctx_5692_, lean_object* v_s_5693_){
_start:
{
lean_object* v_stxStack_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; uint8_t v___x_5698_; 
v_stxStack_5694_ = lean_ctor_get(v_s_5693_, 0);
v___x_5695_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5694_);
v___x_5696_ = lean_unsigned_to_nat(1u);
v___x_5697_ = lean_nat_add(v_offset_5691_, v___x_5696_);
v___x_5698_ = lean_nat_dec_lt(v___x_5695_, v___x_5697_);
lean_dec(v___x_5697_);
if (v___x_5698_ == 0)
{
lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; 
v___x_5699_ = lean_nat_sub(v___x_5695_, v_offset_5691_);
lean_dec(v___x_5695_);
v___x_5700_ = lean_nat_sub(v___x_5699_, v___x_5696_);
lean_dec(v___x_5699_);
v___x_5701_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5694_, v___x_5700_);
lean_dec(v___x_5700_);
if (lean_obj_tag(v___x_5701_) == 3)
{
uint8_t v___x_5713_; lean_object* v___x_5714_; 
v___x_5713_ = 1;
lean_inc_ref(v___x_5701_);
lean_inc_ref(v_ctx_5692_);
v___x_5714_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5692_, v___x_5701_, v___x_5713_);
if (lean_obj_tag(v___x_5714_) == 0)
{
lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; 
lean_dec_ref(v_ctx_5692_);
v___x_5715_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__1));
v___x_5716_ = lean_box(0);
v___x_5717_ = l_Lean_Syntax_formatStx(v___x_5701_, v___x_5716_, v___x_5698_);
v___x_5718_ = l_Std_Format_defWidth;
v___x_5719_ = lean_unsigned_to_nat(0u);
v___x_5720_ = l_Std_Format_pretty(v___x_5717_, v___x_5718_, v___x_5719_, v___x_5719_);
v___x_5721_ = lean_string_append(v___x_5715_, v___x_5720_);
lean_dec_ref(v___x_5720_);
v___x_5722_ = lean_box(0);
v___x_5723_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5693_, v___x_5721_, v___x_5722_, v___x_5713_);
return v___x_5723_;
}
else
{
lean_object* v_head_5724_; lean_object* v_tail_5725_; lean_object* v_iniSz_5726_; lean_object* v_s_5728_; 
v_head_5724_ = lean_ctor_get(v___x_5714_, 0);
lean_inc(v_head_5724_);
v_tail_5725_ = lean_ctor_get(v___x_5714_, 1);
lean_inc(v_tail_5725_);
lean_dec_ref_known(v___x_5714_, 2);
v_iniSz_5726_ = l_Lean_Parser_ParserState_stackSize(v_s_5693_);
switch(lean_obj_tag(v_head_5724_))
{
case 0:
{
if (lean_obj_tag(v_tail_5725_) == 0)
{
lean_object* v_cat_5738_; lean_object* v___x_5739_; 
lean_dec_ref_known(v___x_5701_, 4);
v_cat_5738_ = lean_ctor_get(v_head_5724_, 0);
lean_inc(v_cat_5738_);
lean_dec_ref_known(v_head_5724_, 1);
v___x_5739_ = l_Lean_Parser_categoryParserFn(v_cat_5738_, v_ctx_5692_, v_s_5693_);
v_s_5728_ = v___x_5739_;
goto v___jp_5727_;
}
else
{
lean_dec_ref_known(v_tail_5725_, 2);
lean_dec_ref_known(v_head_5724_, 1);
lean_dec(v_iniSz_5726_);
lean_dec_ref(v_ctx_5692_);
goto v___jp_5702_;
}
}
case 1:
{
if (lean_obj_tag(v_tail_5725_) == 0)
{
lean_object* v_decl_5740_; lean_object* v___x_5741_; lean_object* v___f_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
lean_dec_ref_known(v___x_5701_, 4);
v_decl_5740_ = lean_ctor_get(v_head_5724_, 0);
lean_inc(v_decl_5740_);
lean_dec_ref_known(v_head_5724_, 1);
v___x_5741_ = lean_box(v___x_5698_);
v___f_5742_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5742_, 0, v___x_5741_);
v___x_5743_ = lean_box(0);
v___x_5744_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConst), 4, 2);
lean_closure_set(v___x_5744_, 0, v_decl_5740_);
lean_closure_set(v___x_5744_, 1, v___x_5743_);
v___x_5745_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5742_, v___x_5744_, v_ctx_5692_, v_s_5693_);
v_s_5728_ = v___x_5745_;
goto v___jp_5727_;
}
else
{
lean_dec_ref_known(v_tail_5725_, 2);
lean_dec_ref_known(v_head_5724_, 1);
lean_dec(v_iniSz_5726_);
lean_dec_ref(v_ctx_5692_);
goto v___jp_5702_;
}
}
default: 
{
if (lean_obj_tag(v_tail_5725_) == 0)
{
lean_object* v_p_5746_; 
v_p_5746_ = lean_ctor_get(v_head_5724_, 0);
lean_inc_ref(v_p_5746_);
lean_dec_ref_known(v_head_5724_, 1);
if (lean_obj_tag(v_p_5746_) == 0)
{
lean_object* v_p_5747_; lean_object* v_fn_5748_; lean_object* v___x_5749_; 
lean_dec_ref_known(v___x_5701_, 4);
v_p_5747_ = lean_ctor_get(v_p_5746_, 0);
lean_inc(v_p_5747_);
lean_dec_ref_known(v_p_5746_, 1);
v_fn_5748_ = lean_ctor_get(v_p_5747_, 1);
lean_inc_ref(v_fn_5748_);
lean_dec(v_p_5747_);
v___x_5749_ = lean_apply_2(v_fn_5748_, v_ctx_5692_, v_s_5693_);
v_s_5728_ = v___x_5749_;
goto v___jp_5727_;
}
else
{
lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; 
lean_dec_ref(v_p_5746_);
lean_dec(v_iniSz_5726_);
lean_dec_ref(v_ctx_5692_);
v___x_5750_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__3));
v___x_5751_ = lean_box(0);
v___x_5752_ = l_Lean_Syntax_formatStx(v___x_5701_, v___x_5751_, v___x_5698_);
v___x_5753_ = l_Std_Format_defWidth;
v___x_5754_ = lean_unsigned_to_nat(0u);
v___x_5755_ = l_Std_Format_pretty(v___x_5752_, v___x_5753_, v___x_5754_, v___x_5754_);
v___x_5756_ = lean_string_append(v___x_5750_, v___x_5755_);
lean_dec_ref(v___x_5755_);
v___x_5757_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__4));
v___x_5758_ = lean_string_append(v___x_5756_, v___x_5757_);
v___x_5759_ = lean_box(0);
v___x_5760_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5693_, v___x_5758_, v___x_5759_, v___x_5713_);
return v___x_5760_;
}
}
else
{
lean_dec_ref_known(v_tail_5725_, 2);
lean_dec_ref_known(v_head_5724_, 1);
lean_dec(v_iniSz_5726_);
lean_dec_ref(v_ctx_5692_);
goto v___jp_5702_;
}
}
}
v___jp_5727_:
{
lean_object* v_errorMsg_5729_; lean_object* v___x_5730_; uint8_t v___x_5731_; 
v_errorMsg_5729_ = lean_ctor_get(v_s_5728_, 4);
v___x_5730_ = lean_box(0);
v___x_5731_ = l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_errorMsg_5729_, v___x_5730_);
if (v___x_5731_ == 0)
{
lean_dec(v_iniSz_5726_);
return v_s_5728_;
}
else
{
lean_object* v___x_5732_; lean_object* v___x_5733_; uint8_t v___x_5734_; 
v___x_5732_ = l_Lean_Parser_ParserState_stackSize(v_s_5728_);
v___x_5733_ = lean_nat_add(v_iniSz_5726_, v___x_5696_);
lean_dec(v_iniSz_5726_);
v___x_5734_ = lean_nat_dec_eq(v___x_5732_, v___x_5733_);
lean_dec(v___x_5733_);
lean_dec(v___x_5732_);
if (v___x_5734_ == 0)
{
lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; 
v___x_5735_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__2));
v___x_5736_ = lean_box(0);
v___x_5737_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5728_, v___x_5735_, v___x_5736_, v___x_5731_);
return v___x_5737_;
}
else
{
return v_s_5728_;
}
}
}
}
}
else
{
lean_object* v___x_5761_; lean_object* v___x_5762_; uint8_t v___x_5763_; lean_object* v___x_5764_; 
lean_dec(v___x_5701_);
lean_dec_ref(v_ctx_5692_);
v___x_5761_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__5));
v___x_5762_ = lean_box(0);
v___x_5763_ = 1;
v___x_5764_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5693_, v___x_5761_, v___x_5762_, v___x_5763_);
return v___x_5764_;
}
v___jp_5702_:
{
lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; uint8_t v___x_5711_; lean_object* v___x_5712_; 
v___x_5703_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__0));
v___x_5704_ = lean_box(0);
v___x_5705_ = l_Lean_Syntax_formatStx(v___x_5701_, v___x_5704_, v___x_5698_);
v___x_5706_ = l_Std_Format_defWidth;
v___x_5707_ = lean_unsigned_to_nat(0u);
v___x_5708_ = l_Std_Format_pretty(v___x_5705_, v___x_5706_, v___x_5707_, v___x_5707_);
v___x_5709_ = lean_string_append(v___x_5703_, v___x_5708_);
lean_dec_ref(v___x_5708_);
v___x_5710_ = lean_box(0);
v___x_5711_ = 1;
v___x_5712_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5693_, v___x_5709_, v___x_5710_, v___x_5711_);
return v___x_5712_;
}
}
else
{
lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; 
lean_dec(v___x_5695_);
lean_dec_ref(v_ctx_5692_);
v___x_5765_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__6));
v___x_5766_ = lean_box(0);
v___x_5767_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5693_, v___x_5765_, v___x_5766_, v___x_5698_);
return v___x_5767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* v_offset_5768_, lean_object* v_ctx_5769_, lean_object* v_s_5770_){
_start:
{
lean_object* v_res_5771_; 
v_res_5771_ = l_Lean_Parser_parserOfStackFn(v_offset_5768_, v_ctx_5769_, v_s_5770_);
lean_dec(v_offset_5768_);
return v_res_5771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object* v_prec_5772_, lean_object* v_x_5773_){
_start:
{
lean_object* v_quotDepth_5774_; uint8_t v_suppressInsideQuot_5775_; lean_object* v_savedPos_x3f_5776_; lean_object* v_forbiddenTks_5777_; lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5784_; 
v_quotDepth_5774_ = lean_ctor_get(v_x_5773_, 1);
v_suppressInsideQuot_5775_ = lean_ctor_get_uint8(v_x_5773_, sizeof(void*)*4);
v_savedPos_x3f_5776_ = lean_ctor_get(v_x_5773_, 2);
v_forbiddenTks_5777_ = lean_ctor_get(v_x_5773_, 3);
v_isSharedCheck_5784_ = !lean_is_exclusive(v_x_5773_);
if (v_isSharedCheck_5784_ == 0)
{
lean_object* v_unused_5785_; 
v_unused_5785_ = lean_ctor_get(v_x_5773_, 0);
lean_dec(v_unused_5785_);
v___x_5779_ = v_x_5773_;
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
else
{
lean_inc(v_forbiddenTks_5777_);
lean_inc(v_savedPos_x3f_5776_);
lean_inc(v_quotDepth_5774_);
lean_dec(v_x_5773_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v___x_5782_; 
if (v_isShared_5780_ == 0)
{
lean_ctor_set(v___x_5779_, 0, v_prec_5772_);
v___x_5782_ = v___x_5779_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_prec_5772_);
lean_ctor_set(v_reuseFailAlloc_5783_, 1, v_quotDepth_5774_);
lean_ctor_set(v_reuseFailAlloc_5783_, 2, v_savedPos_x3f_5776_);
lean_ctor_set(v_reuseFailAlloc_5783_, 3, v_forbiddenTks_5777_);
lean_ctor_set_uint8(v_reuseFailAlloc_5783_, sizeof(void*)*4, v_suppressInsideQuot_5775_);
v___x_5782_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
return v___x_5782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object* v___y_5786_){
_start:
{
lean_inc(v___y_5786_);
return v___y_5786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object* v___y_5787_){
_start:
{
lean_object* v_res_5788_; 
v_res_5788_ = l_Lean_Parser_parserOfStack___lam__1(v___y_5787_);
lean_dec(v___y_5787_);
return v_res_5788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object* v___y_5789_){
_start:
{
lean_inc_ref(v___y_5789_);
return v___y_5789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object* v___y_5790_){
_start:
{
lean_object* v_res_5791_; 
v_res_5791_ = l_Lean_Parser_parserOfStack___lam__2(v___y_5790_);
lean_dec_ref(v___y_5790_);
return v_res_5791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* v_offset_5798_, lean_object* v_prec_5799_){
_start:
{
lean_object* v___f_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; 
v___f_5800_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___lam__0), 2, 1);
lean_closure_set(v___f_5800_, 0, v_prec_5799_);
v___x_5801_ = ((lean_object*)(l_Lean_Parser_parserOfStack___closed__2));
v___x_5802_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___boxed), 3, 1);
lean_closure_set(v___x_5802_, 0, v_offset_5798_);
v___x_5803_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5803_, 0, v___f_5800_);
lean_closure_set(v___x_5803_, 1, v___x_5802_);
v___x_5804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5804_, 0, v___x_5801_);
lean_ctor_set(v___x_5804_, 1, v___x_5803_);
return v___x_5804_;
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
