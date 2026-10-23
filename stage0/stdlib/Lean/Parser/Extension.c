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
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_unsafeBaseIO___redArg(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___impl(lean_object* v_x_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = lean_obj_tag_nat(v_x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___impl___boxed(lean_object* v_x_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___impl(v_x_470_);
lean_dec_ref(v_x_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(lean_object* v_t_472_, lean_object* v_k_473_){
_start:
{
switch(lean_obj_tag(v_t_472_))
{
case 0:
{
lean_object* v_val_474_; lean_object* v___x_475_; 
v_val_474_ = lean_ctor_get(v_t_472_, 0);
lean_inc_ref(v_val_474_);
lean_dec_ref_known(v_t_472_, 1);
v___x_475_ = lean_apply_1(v_k_473_, v_val_474_);
return v___x_475_;
}
case 1:
{
lean_object* v_val_476_; lean_object* v___x_477_; 
v_val_476_ = lean_ctor_get(v_t_472_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v_t_472_, 1);
v___x_477_ = lean_apply_1(v_k_473_, v_val_476_);
return v___x_477_;
}
case 2:
{
lean_object* v_catName_478_; lean_object* v_declName_479_; uint8_t v_behavior_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_catName_478_ = lean_ctor_get(v_t_472_, 0);
lean_inc(v_catName_478_);
v_declName_479_ = lean_ctor_get(v_t_472_, 1);
lean_inc(v_declName_479_);
v_behavior_480_ = lean_ctor_get_uint8(v_t_472_, sizeof(void*)*2);
lean_dec_ref_known(v_t_472_, 2);
v___x_481_ = lean_box(v_behavior_480_);
v___x_482_ = lean_apply_3(v_k_473_, v_catName_478_, v_declName_479_, v___x_481_);
return v___x_482_;
}
default: 
{
lean_object* v_catName_483_; lean_object* v_declName_484_; lean_object* v_prio_485_; lean_object* v___x_486_; 
v_catName_483_ = lean_ctor_get(v_t_472_, 0);
lean_inc(v_catName_483_);
v_declName_484_ = lean_ctor_get(v_t_472_, 1);
lean_inc(v_declName_484_);
v_prio_485_ = lean_ctor_get(v_t_472_, 2);
lean_inc(v_prio_485_);
lean_dec_ref_known(v_t_472_, 3);
v___x_486_ = lean_apply_3(v_k_473_, v_catName_483_, v_declName_484_, v_prio_485_);
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(lean_object* v_motive_487_, lean_object* v_ctorIdx_488_, lean_object* v_t_489_, lean_object* v_h_490_, lean_object* v_k_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_489_, v_k_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___boxed(lean_object* v_motive_493_, lean_object* v_ctorIdx_494_, lean_object* v_t_495_, lean_object* v_h_496_, lean_object* v_k_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(v_motive_493_, v_ctorIdx_494_, v_t_495_, v_h_496_, v_k_497_);
lean_dec(v_ctorIdx_494_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim___redArg(lean_object* v_t_499_, lean_object* v_token_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_499_, v_token_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim(lean_object* v_motive_502_, lean_object* v_t_503_, lean_object* v_h_504_, lean_object* v_token_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_503_, v_token_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim___redArg(lean_object* v_t_507_, lean_object* v_kind_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_507_, v_kind_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim(lean_object* v_motive_510_, lean_object* v_t_511_, lean_object* v_h_512_, lean_object* v_kind_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_511_, v_kind_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim___redArg(lean_object* v_t_515_, lean_object* v_category_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_515_, v_category_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim(lean_object* v_motive_518_, lean_object* v_t_519_, lean_object* v_h_520_, lean_object* v_category_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_519_, v_category_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim___redArg(lean_object* v_t_523_, lean_object* v_parser_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_523_, v_parser_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim(lean_object* v_motive_526_, lean_object* v_t_527_, lean_object* v_h_528_, lean_object* v_parser_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_527_, v_parser_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___impl(lean_object* v_x_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_obj_tag_nat(v_x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___impl___boxed(lean_object* v_x_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_Parser_ParserExtension_Entry_ctorIdx___impl(v_x_538_);
lean_dec_ref(v_x_538_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(lean_object* v_t_540_, lean_object* v_k_541_){
_start:
{
switch(lean_obj_tag(v_t_540_))
{
case 0:
{
lean_object* v_val_542_; lean_object* v___x_543_; 
v_val_542_ = lean_ctor_get(v_t_540_, 0);
lean_inc_ref(v_val_542_);
lean_dec_ref_known(v_t_540_, 1);
v___x_543_ = lean_apply_1(v_k_541_, v_val_542_);
return v___x_543_;
}
case 1:
{
lean_object* v_val_544_; lean_object* v___x_545_; 
v_val_544_ = lean_ctor_get(v_t_540_, 0);
lean_inc(v_val_544_);
lean_dec_ref_known(v_t_540_, 1);
v___x_545_ = lean_apply_1(v_k_541_, v_val_544_);
return v___x_545_;
}
case 2:
{
lean_object* v_catName_546_; lean_object* v_declName_547_; uint8_t v_behavior_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_catName_546_ = lean_ctor_get(v_t_540_, 0);
lean_inc(v_catName_546_);
v_declName_547_ = lean_ctor_get(v_t_540_, 1);
lean_inc(v_declName_547_);
v_behavior_548_ = lean_ctor_get_uint8(v_t_540_, sizeof(void*)*2);
lean_dec_ref_known(v_t_540_, 2);
v___x_549_ = lean_box(v_behavior_548_);
v___x_550_ = lean_apply_3(v_k_541_, v_catName_546_, v_declName_547_, v___x_549_);
return v___x_550_;
}
default: 
{
lean_object* v_catName_551_; lean_object* v_declName_552_; uint8_t v_leading_553_; lean_object* v_p_554_; lean_object* v_prio_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_catName_551_ = lean_ctor_get(v_t_540_, 0);
lean_inc(v_catName_551_);
v_declName_552_ = lean_ctor_get(v_t_540_, 1);
lean_inc(v_declName_552_);
v_leading_553_ = lean_ctor_get_uint8(v_t_540_, sizeof(void*)*4);
v_p_554_ = lean_ctor_get(v_t_540_, 2);
lean_inc_ref(v_p_554_);
v_prio_555_ = lean_ctor_get(v_t_540_, 3);
lean_inc(v_prio_555_);
lean_dec_ref_known(v_t_540_, 4);
v___x_556_ = lean_box(v_leading_553_);
v___x_557_ = lean_apply_5(v_k_541_, v_catName_551_, v_declName_552_, v___x_556_, v_p_554_, v_prio_555_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim(lean_object* v_motive_558_, lean_object* v_ctorIdx_559_, lean_object* v_t_560_, lean_object* v_h_561_, lean_object* v_k_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_560_, v_k_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___boxed(lean_object* v_motive_564_, lean_object* v_ctorIdx_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_k_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Parser_ParserExtension_Entry_ctorElim(v_motive_564_, v_ctorIdx_565_, v_t_566_, v_h_567_, v_k_568_);
lean_dec(v_ctorIdx_565_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim___redArg(lean_object* v_t_570_, lean_object* v_token_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_570_, v_token_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim(lean_object* v_motive_573_, lean_object* v_t_574_, lean_object* v_h_575_, lean_object* v_token_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_574_, v_token_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim___redArg(lean_object* v_t_578_, lean_object* v_kind_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_578_, v_kind_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim(lean_object* v_motive_581_, lean_object* v_t_582_, lean_object* v_h_583_, lean_object* v_kind_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_582_, v_kind_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim___redArg(lean_object* v_t_586_, lean_object* v_category_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_586_, v_category_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim(lean_object* v_motive_589_, lean_object* v_t_590_, lean_object* v_h_591_, lean_object* v_category_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_590_, v_category_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim___redArg(lean_object* v_t_594_, lean_object* v_parser_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_594_, v_parser_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim(lean_object* v_motive_597_, lean_object* v_t_598_, lean_object* v_h_599_, lean_object* v_parser_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_598_, v_parser_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object* v_x_606_){
_start:
{
switch(lean_obj_tag(v_x_606_))
{
case 0:
{
lean_object* v_val_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_val_607_ = lean_ctor_get(v_x_606_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_606_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v_x_606_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_val_607_);
lean_dec(v_x_606_);
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
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
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
case 1:
{
lean_object* v_val_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_val_615_ = lean_ctor_get(v_x_606_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v_x_606_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v_x_606_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_val_615_);
lean_dec(v_x_606_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_val_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
case 2:
{
lean_object* v_catName_623_; lean_object* v_declName_624_; uint8_t v_behavior_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_catName_623_ = lean_ctor_get(v_x_606_, 0);
v_declName_624_ = lean_ctor_get(v_x_606_, 1);
v_behavior_625_ = lean_ctor_get_uint8(v_x_606_, sizeof(void*)*2);
v_isSharedCheck_632_ = !lean_is_exclusive(v_x_606_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v_x_606_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_declName_624_);
lean_inc(v_catName_623_);
lean_dec(v_x_606_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_catName_623_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_declName_624_);
lean_ctor_set_uint8(v_reuseFailAlloc_631_, sizeof(void*)*2, v_behavior_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
default: 
{
lean_object* v_catName_633_; lean_object* v_declName_634_; lean_object* v_prio_635_; lean_object* v___x_636_; 
v_catName_633_ = lean_ctor_get(v_x_606_, 0);
lean_inc(v_catName_633_);
v_declName_634_ = lean_ctor_get(v_x_606_, 1);
lean_inc(v_declName_634_);
v_prio_635_ = lean_ctor_get(v_x_606_, 3);
lean_inc(v_prio_635_);
lean_dec_ref_known(v_x_606_, 4);
v___x_636_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_636_, 0, v_catName_633_);
lean_ctor_set(v___x_636_, 1, v_declName_634_);
lean_ctor_set(v___x_636_, 2, v_prio_635_);
return v___x_636_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_638_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
lean_ctor_set(v___x_639_, 2, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default(void){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0, &l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0_once, _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_643_ = l_Lean_Parser_builtinTokenTable;
v___x_644_ = lean_st_ref_get(v___x_643_);
v___x_645_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_646_ = lean_st_ref_get(v___x_645_);
v___x_647_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_648_ = lean_st_ref_get(v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_649_, 0, v___x_644_);
lean_ctor_set(v___x_649_, 1, v___x_646_);
lean_ctor_set(v___x_649_, 2, v___x_648_);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object* v_tokens_656_, lean_object* v_tk_657_){
_start:
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = ((lean_object*)(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0));
v___x_659_ = lean_string_dec_eq(v_tk_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Data_Trie_find_x3f___redArg(v_tokens_656_, v_tk_657_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_inc_ref(v_tk_657_);
v___x_661_ = l_Lean_Data_Trie_insert___redArg(v_tokens_656_, v_tk_657_, v_tk_657_);
lean_dec_ref(v_tk_657_);
v___x_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
else
{
lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v_tk_657_);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v___x_660_, 0);
lean_dec(v_unused_670_);
v___x_664_ = v___x_660_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_dec(v___x_660_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v_tokens_656_);
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_tokens_656_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v___x_671_; 
lean_dec_ref(v_tk_657_);
lean_dec_ref(v_tokens_656_);
v___x_671_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1));
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg(lean_object* v_catName_674_){
_start:
{
lean_object* v___x_675_; uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_675_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0));
v___x_676_ = 1;
v___x_677_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_674_, v___x_676_);
v___x_678_ = lean_string_append(v___x_675_, v___x_677_);
lean_dec_ref(v___x_677_);
v___x_679_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_680_ = lean_string_append(v___x_678_, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object* v_00_u03b1_682_, lean_object* v_catName_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object* v_categories_687_, lean_object* v_catName_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__0));
v___x_690_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__1));
v___x_691_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_689_, v___x_690_, v_categories_687_, v_catName_688_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory___boxed(lean_object* v_categories_692_, lean_object* v_catName_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Parser_getCategory(v_categories_692_, v_catName_693_);
lean_dec_ref(v_categories_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(lean_object* v_as_696_){
_start:
{
lean_object* v___f_697_; lean_object* v___x_698_; 
v___f_697_ = ((lean_object*)(l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0));
v___x_698_ = l_List_eraseDupsBy___redArg(v___f_697_, v_as_696_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(lean_object* v_p_699_, lean_object* v_prio_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
if (lean_obj_tag(v_x_702_) == 0)
{
lean_dec(v_prio_700_);
lean_dec_ref(v_p_699_);
return v_x_701_;
}
else
{
lean_object* v_head_703_; lean_object* v_tail_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_724_; 
v_head_703_ = lean_ctor_get(v_x_702_, 0);
v_tail_704_ = lean_ctor_get(v_x_702_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_x_702_);
if (v_isSharedCheck_724_ == 0)
{
v___x_706_ = v_x_702_;
v_isShared_707_ = v_isSharedCheck_724_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_tail_704_);
lean_inc(v_head_703_);
lean_dec(v_x_702_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_724_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_leadingTable_708_; lean_object* v_leadingParsers_709_; lean_object* v_trailingTable_710_; lean_object* v_trailingParsers_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_723_; 
v_leadingTable_708_ = lean_ctor_get(v_x_701_, 0);
v_leadingParsers_709_ = lean_ctor_get(v_x_701_, 1);
v_trailingTable_710_ = lean_ctor_get(v_x_701_, 2);
v_trailingParsers_711_ = lean_ctor_get(v_x_701_, 3);
v_isSharedCheck_723_ = !lean_is_exclusive(v_x_701_);
if (v_isSharedCheck_723_ == 0)
{
v___x_713_ = v_x_701_;
v_isShared_714_ = v_isSharedCheck_723_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_trailingParsers_711_);
lean_inc(v_trailingTable_710_);
lean_inc(v_leadingParsers_709_);
lean_inc(v_leadingTable_708_);
lean_dec(v_x_701_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_723_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
lean_inc(v_prio_700_);
lean_inc_ref(v_p_699_);
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 0);
lean_ctor_set(v___x_706_, 1, v_prio_700_);
lean_ctor_set(v___x_706_, 0, v_p_699_);
v___x_716_ = v___x_706_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_p_699_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_prio_700_);
v___x_716_ = v_reuseFailAlloc_722_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = l_Lean_Parser_TokenMap_insert___redArg(v_leadingTable_708_, v_head_703_, v___x_716_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_717_);
v___x_719_ = v___x_713_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_leadingParsers_709_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_trailingTable_710_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_trailingParsers_711_);
v___x_719_ = v_reuseFailAlloc_721_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
v_x_701_ = v___x_719_;
v_x_702_ = v_tail_704_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_725_, lean_object* v_vals_726_, lean_object* v_i_727_, lean_object* v_k_728_){
_start:
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = lean_array_get_size(v_keys_725_);
v___x_730_ = lean_nat_dec_lt(v_i_727_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
lean_dec(v_i_727_);
v___x_731_ = lean_box(0);
return v___x_731_;
}
else
{
lean_object* v_k_x27_732_; uint8_t v___x_733_; 
v_k_x27_732_ = lean_array_fget_borrowed(v_keys_725_, v_i_727_);
v___x_733_ = lean_name_eq(v_k_728_, v_k_x27_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = lean_nat_add(v_i_727_, v___x_734_);
lean_dec(v_i_727_);
v_i_727_ = v___x_735_;
goto _start;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_array_fget_borrowed(v_vals_726_, v_i_727_);
lean_dec(v_i_727_);
lean_inc(v___x_737_);
v___x_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_739_, lean_object* v_vals_740_, lean_object* v_i_741_, lean_object* v_k_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_739_, v_vals_740_, v_i_741_, v_k_742_);
lean_dec(v_k_742_);
lean_dec_ref(v_vals_740_);
lean_dec_ref(v_keys_739_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(lean_object* v_x_744_, size_t v_x_745_, lean_object* v_x_746_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
lean_object* v_es_747_; lean_object* v___x_748_; size_t v___x_749_; size_t v___x_750_; lean_object* v_j_751_; lean_object* v___x_752_; 
v_es_747_ = lean_ctor_get(v_x_744_, 0);
v___x_748_ = lean_box(2);
v___x_749_ = ((size_t)31ULL);
v___x_750_ = lean_usize_land(v_x_745_, v___x_749_);
v_j_751_ = lean_usize_to_nat(v___x_750_);
v___x_752_ = lean_array_get_borrowed(v___x_748_, v_es_747_, v_j_751_);
lean_dec(v_j_751_);
switch(lean_obj_tag(v___x_752_))
{
case 0:
{
lean_object* v_key_753_; lean_object* v_val_754_; uint8_t v___x_755_; 
v_key_753_ = lean_ctor_get(v___x_752_, 0);
v_val_754_ = lean_ctor_get(v___x_752_, 1);
v___x_755_ = lean_name_eq(v_x_746_, v_key_753_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; 
v___x_756_ = lean_box(0);
return v___x_756_;
}
else
{
lean_object* v___x_757_; 
lean_inc(v_val_754_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v_val_754_);
return v___x_757_;
}
}
case 1:
{
lean_object* v_node_758_; size_t v___x_759_; size_t v___x_760_; 
v_node_758_ = lean_ctor_get(v___x_752_, 0);
v___x_759_ = ((size_t)5ULL);
v___x_760_ = lean_usize_shift_right(v_x_745_, v___x_759_);
v_x_744_ = v_node_758_;
v_x_745_ = v___x_760_;
goto _start;
}
default: 
{
lean_object* v___x_762_; 
v___x_762_ = lean_box(0);
return v___x_762_;
}
}
}
else
{
lean_object* v_ks_763_; lean_object* v_vs_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_ks_763_ = lean_ctor_get(v_x_744_, 0);
v_vs_764_ = lean_ctor_get(v_x_744_, 1);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_ks_763_, v_vs_764_, v___x_765_, v_x_746_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg___boxed(lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
size_t v_x_496__boxed_770_; lean_object* v_res_771_; 
v_x_496__boxed_770_ = lean_unbox_usize(v_x_768_);
lean_dec(v_x_768_);
v_res_771_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_767_, v_x_496__boxed_770_, v_x_769_);
lean_dec(v_x_769_);
lean_dec_ref(v_x_767_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
uint64_t v___y_775_; 
if (lean_obj_tag(v_x_773_) == 0)
{
uint64_t v___x_778_; 
v___x_778_ = 1723ULL;
v___y_775_ = v___x_778_;
goto v___jp_774_;
}
else
{
uint64_t v_hash_779_; 
v_hash_779_ = lean_ctor_get_uint64(v_x_773_, sizeof(void*)*2);
v___y_775_ = v_hash_779_;
goto v___jp_774_;
}
v___jp_774_:
{
size_t v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_uint64_to_usize(v___y_775_);
v___x_777_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_772_, v___x_776_, v_x_773_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg___boxed(lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_780_, v_x_781_);
lean_dec(v_x_781_);
lean_dec_ref(v_x_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
if (lean_obj_tag(v_a_783_) == 0)
{
lean_object* v___x_785_; 
v___x_785_ = l_List_reverse___redArg(v_a_784_);
return v___x_785_;
}
else
{
lean_object* v_head_786_; lean_object* v_tail_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_797_; 
v_head_786_ = lean_ctor_get(v_a_783_, 0);
v_tail_787_ = lean_ctor_get(v_a_783_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_a_783_);
if (v_isSharedCheck_797_ == 0)
{
v___x_789_ = v_a_783_;
v_isShared_790_ = v_isSharedCheck_797_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_tail_787_);
lean_inc(v_head_786_);
lean_dec(v_a_783_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_797_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = lean_box(0);
v___x_792_ = l_Lean_Name_str___override(v___x_791_, v_head_786_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 1, v_a_784_);
lean_ctor_set(v___x_789_, 0, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_a_784_);
v___x_794_ = v_reuseFailAlloc_796_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
v_a_783_ = v_tail_787_;
v_a_784_ = v___x_794_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object* v_categories_798_, lean_object* v_catName_799_, lean_object* v_declName_800_, lean_object* v_p_801_, lean_object* v_prio_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_798_, v_catName_799_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v___x_804_; 
lean_dec(v_prio_802_);
lean_dec_ref(v_p_801_);
lean_dec(v_declName_800_);
lean_dec_ref(v_categories_798_);
v___x_804_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_799_);
return v___x_804_;
}
else
{
lean_object* v_val_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_851_; 
v_val_805_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_851_ == 0)
{
v___x_807_ = v___x_803_;
v_isShared_808_ = v_isSharedCheck_851_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_val_805_);
lean_dec(v___x_803_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_851_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v_info_809_; lean_object* v_declName_810_; lean_object* v_kinds_811_; lean_object* v_tables_812_; uint8_t v_behavior_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_850_; 
v_info_809_ = lean_ctor_get(v_p_801_, 0);
v_declName_810_ = lean_ctor_get(v_val_805_, 0);
v_kinds_811_ = lean_ctor_get(v_val_805_, 1);
v_tables_812_ = lean_ctor_get(v_val_805_, 2);
v_behavior_813_ = lean_ctor_get_uint8(v_val_805_, sizeof(void*)*3);
v_isSharedCheck_850_ = !lean_is_exclusive(v_val_805_);
if (v_isSharedCheck_850_ == 0)
{
v___x_815_ = v_val_805_;
v_isShared_816_ = v_isSharedCheck_850_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_tables_812_);
lean_inc(v_kinds_811_);
lean_inc(v_declName_810_);
lean_dec(v_val_805_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_850_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_firstTokens_817_; lean_object* v_kinds_818_; lean_object* v_tks_820_; 
v_firstTokens_817_ = lean_ctor_get(v_info_809_, 2);
v_kinds_818_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_811_, v_declName_800_);
switch(lean_obj_tag(v_firstTokens_817_))
{
case 2:
{
lean_object* v_a_832_; 
v_a_832_ = lean_ctor_get(v_firstTokens_817_, 0);
lean_inc(v_a_832_);
v_tks_820_ = v_a_832_;
goto v___jp_819_;
}
case 3:
{
lean_object* v_a_833_; 
v_a_833_ = lean_ctor_get(v_firstTokens_817_, 0);
lean_inc(v_a_833_);
v_tks_820_ = v_a_833_;
goto v___jp_819_;
}
default: 
{
lean_object* v_leadingTable_834_; lean_object* v_leadingParsers_835_; lean_object* v_trailingTable_836_; lean_object* v_trailingParsers_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_849_; 
lean_del_object(v___x_815_);
lean_del_object(v___x_807_);
v_leadingTable_834_ = lean_ctor_get(v_tables_812_, 0);
v_leadingParsers_835_ = lean_ctor_get(v_tables_812_, 1);
v_trailingTable_836_ = lean_ctor_get(v_tables_812_, 2);
v_trailingParsers_837_ = lean_ctor_get(v_tables_812_, 3);
v_isSharedCheck_849_ = !lean_is_exclusive(v_tables_812_);
if (v_isSharedCheck_849_ == 0)
{
v___x_839_ = v_tables_812_;
v_isShared_840_ = v_isSharedCheck_849_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_trailingParsers_837_);
lean_inc(v_trailingTable_836_);
lean_inc(v_leadingParsers_835_);
lean_inc(v_leadingTable_834_);
lean_dec(v_tables_812_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_849_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v_tables_844_; 
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v_p_801_);
lean_ctor_set(v___x_841_, 1, v_prio_802_);
v___x_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v_leadingParsers_835_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_842_);
v_tables_844_ = v___x_839_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_leadingTable_834_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_848_, 2, v_trailingTable_836_);
lean_ctor_set(v_reuseFailAlloc_848_, 3, v_trailingParsers_837_);
v_tables_844_ = v_reuseFailAlloc_848_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_845_, 0, v_declName_810_);
lean_ctor_set(v___x_845_, 1, v_kinds_818_);
lean_ctor_set(v___x_845_, 2, v_tables_844_);
lean_ctor_set_uint8(v___x_845_, sizeof(void*)*3, v_behavior_813_);
v___x_846_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_798_, v_catName_799_, v___x_845_);
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
}
}
v___jp_819_:
{
lean_object* v___x_821_; lean_object* v_tks_822_; lean_object* v___x_823_; lean_object* v_tables_824_; lean_object* v___x_826_; 
v___x_821_ = lean_box(0);
v_tks_822_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_820_, v___x_821_);
v___x_823_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_822_);
v_tables_824_ = l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(v_p_801_, v_prio_802_, v_tables_812_, v___x_823_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 2, v_tables_824_);
lean_ctor_set(v___x_815_, 1, v_kinds_818_);
v___x_826_ = v___x_815_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_declName_810_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_kinds_818_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_tables_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_831_, sizeof(void*)*3, v_behavior_813_);
v___x_826_ = v_reuseFailAlloc_831_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_798_, v_catName_799_, v___x_826_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_827_);
v___x_829_ = v___x_807_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(lean_object* v_00_u03b2_852_, lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_853_, v_x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___boxed(lean_object* v_00_u03b2_856_, lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(v_00_u03b2_856_, v_x_857_, v_x_858_);
lean_dec(v_x_858_);
lean_dec_ref(v_x_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_object* v_00_u03b2_860_, lean_object* v_x_861_, size_t v_x_862_, lean_object* v_x_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_861_, v_x_862_, v_x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___boxed(lean_object* v_00_u03b2_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
size_t v_x_665__boxed_869_; lean_object* v_res_870_; 
v_x_665__boxed_869_ = lean_unbox_usize(v_x_867_);
lean_dec(v_x_867_);
v_res_870_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(v_00_u03b2_865_, v_x_866_, v_x_665__boxed_869_, v_x_868_);
lean_dec(v_x_868_);
lean_dec_ref(v_x_866_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_871_, lean_object* v_keys_872_, lean_object* v_vals_873_, lean_object* v_heq_874_, lean_object* v_i_875_, lean_object* v_k_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_872_, v_vals_873_, v_i_875_, v_k_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_878_, lean_object* v_keys_879_, lean_object* v_vals_880_, lean_object* v_heq_881_, lean_object* v_i_882_, lean_object* v_k_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(v_00_u03b2_878_, v_keys_879_, v_vals_880_, v_heq_881_, v_i_882_, v_k_883_);
lean_dec(v_k_883_);
lean_dec_ref(v_vals_880_);
lean_dec_ref(v_keys_879_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(lean_object* v_p_885_, lean_object* v_prio_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
if (lean_obj_tag(v_x_888_) == 0)
{
lean_dec(v_prio_886_);
lean_dec_ref(v_p_885_);
return v_x_887_;
}
else
{
lean_object* v_head_889_; lean_object* v_tail_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_910_; 
v_head_889_ = lean_ctor_get(v_x_888_, 0);
v_tail_890_ = lean_ctor_get(v_x_888_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_x_888_);
if (v_isSharedCheck_910_ == 0)
{
v___x_892_ = v_x_888_;
v_isShared_893_ = v_isSharedCheck_910_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_tail_890_);
lean_inc(v_head_889_);
lean_dec(v_x_888_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_910_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_leadingTable_894_; lean_object* v_leadingParsers_895_; lean_object* v_trailingTable_896_; lean_object* v_trailingParsers_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_909_; 
v_leadingTable_894_ = lean_ctor_get(v_x_887_, 0);
v_leadingParsers_895_ = lean_ctor_get(v_x_887_, 1);
v_trailingTable_896_ = lean_ctor_get(v_x_887_, 2);
v_trailingParsers_897_ = lean_ctor_get(v_x_887_, 3);
v_isSharedCheck_909_ = !lean_is_exclusive(v_x_887_);
if (v_isSharedCheck_909_ == 0)
{
v___x_899_ = v_x_887_;
v_isShared_900_ = v_isSharedCheck_909_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_trailingParsers_897_);
lean_inc(v_trailingTable_896_);
lean_inc(v_leadingParsers_895_);
lean_inc(v_leadingTable_894_);
lean_dec(v_x_887_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_909_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
lean_inc(v_prio_886_);
lean_inc_ref(v_p_885_);
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 0);
lean_ctor_set(v___x_892_, 1, v_prio_886_);
lean_ctor_set(v___x_892_, 0, v_p_885_);
v___x_902_ = v___x_892_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_p_885_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_prio_886_);
v___x_902_ = v_reuseFailAlloc_908_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = l_Lean_Parser_TokenMap_insert___redArg(v_trailingTable_896_, v_head_889_, v___x_902_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 2, v___x_903_);
v___x_905_ = v___x_899_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_leadingTable_894_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_leadingParsers_895_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_trailingParsers_897_);
v___x_905_ = v_reuseFailAlloc_907_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
v_x_887_ = v___x_905_;
v_x_888_ = v_tail_890_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object* v_tables_911_, lean_object* v_p_912_, lean_object* v_prio_913_){
_start:
{
lean_object* v_tks_915_; lean_object* v_info_920_; lean_object* v_firstTokens_921_; 
v_info_920_ = lean_ctor_get(v_p_912_, 0);
v_firstTokens_921_ = lean_ctor_get(v_info_920_, 2);
switch(lean_obj_tag(v_firstTokens_921_))
{
case 2:
{
lean_object* v_a_922_; 
v_a_922_ = lean_ctor_get(v_firstTokens_921_, 0);
lean_inc(v_a_922_);
v_tks_915_ = v_a_922_;
goto v___jp_914_;
}
case 3:
{
lean_object* v_a_923_; 
v_a_923_ = lean_ctor_get(v_firstTokens_921_, 0);
lean_inc(v_a_923_);
v_tks_915_ = v_a_923_;
goto v___jp_914_;
}
default: 
{
lean_object* v_leadingTable_924_; lean_object* v_leadingParsers_925_; lean_object* v_trailingTable_926_; lean_object* v_trailingParsers_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_936_; 
v_leadingTable_924_ = lean_ctor_get(v_tables_911_, 0);
v_leadingParsers_925_ = lean_ctor_get(v_tables_911_, 1);
v_trailingTable_926_ = lean_ctor_get(v_tables_911_, 2);
v_trailingParsers_927_ = lean_ctor_get(v_tables_911_, 3);
v_isSharedCheck_936_ = !lean_is_exclusive(v_tables_911_);
if (v_isSharedCheck_936_ == 0)
{
v___x_929_ = v_tables_911_;
v_isShared_930_ = v_isSharedCheck_936_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_trailingParsers_927_);
lean_inc(v_trailingTable_926_);
lean_inc(v_leadingParsers_925_);
lean_inc(v_leadingTable_924_);
lean_dec(v_tables_911_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_936_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v_p_912_);
lean_ctor_set(v___x_931_, 1, v_prio_913_);
v___x_932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v_trailingParsers_927_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 3, v___x_932_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_leadingTable_924_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_leadingParsers_925_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_trailingTable_926_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
v___jp_914_:
{
lean_object* v___x_916_; lean_object* v_tks_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_916_ = lean_box(0);
v_tks_917_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_915_, v___x_916_);
v___x_918_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_917_);
v___x_919_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(v_p_912_, v_prio_913_, v_tables_911_, v___x_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object* v_categories_937_, lean_object* v_catName_938_, lean_object* v_declName_939_, lean_object* v_p_940_, lean_object* v_prio_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_937_, v_catName_938_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v___x_943_; 
lean_dec(v_prio_941_);
lean_dec_ref(v_p_940_);
lean_dec(v_declName_939_);
lean_dec_ref(v_categories_937_);
v___x_943_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_938_);
return v___x_943_;
}
else
{
lean_object* v_val_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_965_; 
v_val_944_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_965_ == 0)
{
v___x_946_ = v___x_942_;
v_isShared_947_ = v_isSharedCheck_965_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_val_944_);
lean_dec(v___x_942_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_965_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_declName_948_; lean_object* v_kinds_949_; lean_object* v_tables_950_; uint8_t v_behavior_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_964_; 
v_declName_948_ = lean_ctor_get(v_val_944_, 0);
v_kinds_949_ = lean_ctor_get(v_val_944_, 1);
v_tables_950_ = lean_ctor_get(v_val_944_, 2);
v_behavior_951_ = lean_ctor_get_uint8(v_val_944_, sizeof(void*)*3);
v_isSharedCheck_964_ = !lean_is_exclusive(v_val_944_);
if (v_isSharedCheck_964_ == 0)
{
v___x_953_ = v_val_944_;
v_isShared_954_ = v_isSharedCheck_964_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_tables_950_);
lean_inc(v_kinds_949_);
lean_inc(v_declName_948_);
lean_dec(v_val_944_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_964_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_kinds_955_; lean_object* v_tables_956_; lean_object* v___x_958_; 
v_kinds_955_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_949_, v_declName_939_);
v_tables_956_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(v_tables_950_, v_p_940_, v_prio_941_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 2, v_tables_956_);
lean_ctor_set(v___x_953_, 1, v_kinds_955_);
v___x_958_ = v___x_953_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_declName_948_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_kinds_955_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_tables_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_963_, sizeof(void*)*3, v_behavior_951_);
v___x_958_ = v_reuseFailAlloc_963_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_937_, v_catName_938_, v___x_958_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_959_);
v___x_961_ = v___x_946_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser(lean_object* v_categories_966_, lean_object* v_catName_967_, lean_object* v_declName_968_, uint8_t v_leading_969_, lean_object* v_p_970_, lean_object* v_prio_971_){
_start:
{
if (v_leading_969_ == 0)
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Parser_addTrailingParser(v_categories_966_, v_catName_967_, v_declName_968_, v_p_970_, v_prio_971_);
return v___x_972_;
}
else
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_Parser_addLeadingParser(v_categories_966_, v_catName_967_, v_declName_968_, v_p_970_, v_prio_971_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object* v_categories_974_, lean_object* v_catName_975_, lean_object* v_declName_976_, lean_object* v_leading_977_, lean_object* v_p_978_, lean_object* v_prio_979_){
_start:
{
uint8_t v_leading_boxed_980_; lean_object* v_res_981_; 
v_leading_boxed_980_ = lean_unbox(v_leading_977_);
v_res_981_ = l_Lean_Parser_addParser(v_categories_974_, v_catName_975_, v_declName_976_, v_leading_boxed_980_, v_p_978_, v_prio_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
if (lean_obj_tag(v_x_983_) == 0)
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v_x_982_);
return v___x_984_;
}
else
{
lean_object* v_head_985_; lean_object* v_tail_986_; lean_object* v___x_987_; 
v_head_985_ = lean_ctor_get(v_x_983_, 0);
lean_inc(v_head_985_);
v_tail_986_ = lean_ctor_get(v_x_983_, 1);
lean_inc(v_tail_986_);
lean_dec_ref_known(v_x_983_, 2);
v___x_987_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_x_982_, v_head_985_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_dec(v_tail_986_);
return v___x_987_;
}
else
{
lean_object* v_a_988_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v_x_982_ = v_a_988_;
v_x_983_ = v_tail_986_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object* v_tokenTable_990_, lean_object* v_info_991_){
_start:
{
lean_object* v_collectTokens_992_; lean_object* v___x_993_; lean_object* v_newTokens_994_; lean_object* v___x_995_; 
v_collectTokens_992_ = lean_ctor_get(v_info_991_, 0);
lean_inc_ref(v_collectTokens_992_);
lean_dec_ref(v_info_991_);
v___x_993_ = lean_box(0);
v_newTokens_994_ = lean_apply_1(v_collectTokens_992_, v___x_993_);
v___x_995_ = l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(v_tokenTable_990_, v_newTokens_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object* v_info_998_, lean_object* v_declName_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1001_ = l_Lean_Parser_builtinTokenTable;
v___x_1002_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_1003_ = lean_st_ref_swap(v___x_1001_, v___x_1002_);
v___x_1004_ = l_Lean_Parser_addParserTokens(v___x_1003_, v_info_998_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1021_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1021_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1021_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1009_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0));
v___x_1010_ = l_Lean_privateToUserName(v_declName_999_);
v___x_1011_ = 1;
v___x_1012_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1010_, v___x_1011_);
v___x_1013_ = lean_string_append(v___x_1009_, v___x_1012_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_1015_ = lean_string_append(v___x_1013_, v___x_1014_);
v___x_1016_ = lean_string_append(v___x_1015_, v_a_1005_);
lean_dec(v_a_1005_);
v___x_1017_ = lean_mk_io_user_error(v___x_1016_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set_tag(v___x_1007_, 1);
lean_ctor_set(v___x_1007_, 0, v___x_1017_);
v___x_1019_ = v___x_1007_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_declName_999_);
v_a_1022_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1024_ = v___x_1004_;
v_isShared_1025_ = v_isSharedCheck_1031_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1004_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1031_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_st_ref_swap(v___x_1001_, v_a_1022_);
lean_dec(v___x_1027_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1029_ = v___x_1024_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1026_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___boxed(lean_object* v_info_1032_, lean_object* v_declName_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_1032_, v_declName_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(lean_object* v_msg_1036_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1038_ = lean_panic_fn_borrowed(v___x_1037_, v_msg_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object* v_s_1042_, lean_object* v_e_1043_){
_start:
{
switch(lean_obj_tag(v_e_1043_))
{
case 0:
{
lean_object* v_val_1044_; lean_object* v_tokens_1045_; lean_object* v_kinds_1046_; lean_object* v_categories_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1065_; 
v_val_1044_ = lean_ctor_get(v_e_1043_, 0);
lean_inc_ref(v_val_1044_);
lean_dec_ref_known(v_e_1043_, 1);
v_tokens_1045_ = lean_ctor_get(v_s_1042_, 0);
v_kinds_1046_ = lean_ctor_get(v_s_1042_, 1);
v_categories_1047_ = lean_ctor_get(v_s_1042_, 2);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_s_1042_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1049_ = v_s_1042_;
v_isShared_1050_ = v_isSharedCheck_1065_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_categories_1047_);
lean_inc(v_kinds_1046_);
lean_inc(v_tokens_1045_);
lean_dec(v_s_1042_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1065_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; 
v___x_1051_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_1045_, v_val_1044_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_del_object(v___x_1049_);
lean_dec_ref(v_categories_1047_);
lean_dec_ref(v_kinds_1046_);
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1054_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1055_ = lean_unsigned_to_nat(166u);
v___x_1056_ = lean_unsigned_to_nat(26u);
v___x_1057_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1058_ = lean_string_append(v___x_1057_, v_a_1052_);
lean_dec(v_a_1052_);
v___x_1059_ = l_mkPanicMessageWithDecl(v___x_1053_, v___x_1054_, v___x_1055_, v___x_1056_, v___x_1058_);
lean_dec_ref(v___x_1058_);
v___x_1060_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1059_);
return v___x_1060_;
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; 
v_a_1061_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1051_, 1);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v_a_1061_);
v___x_1063_ = v___x_1049_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1061_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_kinds_1046_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_categories_1047_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
case 1:
{
lean_object* v_val_1066_; lean_object* v_tokens_1067_; lean_object* v_kinds_1068_; lean_object* v_categories_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1077_; 
v_val_1066_ = lean_ctor_get(v_e_1043_, 0);
lean_inc(v_val_1066_);
lean_dec_ref_known(v_e_1043_, 1);
v_tokens_1067_ = lean_ctor_get(v_s_1042_, 0);
v_kinds_1068_ = lean_ctor_get(v_s_1042_, 1);
v_categories_1069_ = lean_ctor_get(v_s_1042_, 2);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_s_1042_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1071_ = v_s_1042_;
v_isShared_1072_ = v_isSharedCheck_1077_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_categories_1069_);
lean_inc(v_kinds_1068_);
lean_inc(v_tokens_1067_);
lean_dec(v_s_1042_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1077_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1073_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_1068_, v_val_1066_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___x_1073_);
v___x_1075_ = v___x_1071_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_tokens_1067_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_categories_1069_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
case 2:
{
lean_object* v_catName_1078_; lean_object* v_declName_1079_; uint8_t v_behavior_1080_; lean_object* v_tokens_1081_; lean_object* v_kinds_1082_; lean_object* v_categories_1083_; uint8_t v___x_1084_; 
v_catName_1078_ = lean_ctor_get(v_e_1043_, 0);
lean_inc(v_catName_1078_);
v_declName_1079_ = lean_ctor_get(v_e_1043_, 1);
lean_inc(v_declName_1079_);
v_behavior_1080_ = lean_ctor_get_uint8(v_e_1043_, sizeof(void*)*2);
lean_dec_ref_known(v_e_1043_, 2);
v_tokens_1081_ = lean_ctor_get(v_s_1042_, 0);
v_kinds_1082_ = lean_ctor_get(v_s_1042_, 1);
v_categories_1083_ = lean_ctor_get(v_s_1042_, 2);
v___x_1084_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_1083_, v_catName_1078_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1095_; 
lean_inc_ref(v_categories_1083_);
lean_inc_ref(v_kinds_1082_);
lean_inc_ref(v_tokens_1081_);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_s_1042_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; lean_object* v_unused_1097_; lean_object* v_unused_1098_; 
v_unused_1096_ = lean_ctor_get(v_s_1042_, 2);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_s_1042_, 1);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_s_1042_, 0);
lean_dec(v_unused_1098_);
v___x_1086_ = v_s_1042_;
v_isShared_1087_ = v_isSharedCheck_1095_;
goto v_resetjp_1085_;
}
else
{
lean_dec(v_s_1042_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1095_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1088_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_1089_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_1090_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1090_, 0, v_declName_1079_);
lean_ctor_set(v___x_1090_, 1, v___x_1088_);
lean_ctor_set(v___x_1090_, 2, v___x_1089_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*3, v_behavior_1080_);
v___x_1091_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_1083_, v_catName_1078_, v___x_1090_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 2, v___x_1091_);
v___x_1093_ = v___x_1086_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_tokens_1081_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_kinds_1082_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
else
{
lean_dec(v_declName_1079_);
lean_dec(v_catName_1078_);
return v_s_1042_;
}
}
default: 
{
lean_object* v_catName_1099_; lean_object* v_declName_1100_; uint8_t v_leading_1101_; lean_object* v_p_1102_; lean_object* v_prio_1103_; lean_object* v_tokens_1104_; lean_object* v_kinds_1105_; lean_object* v_categories_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1124_; 
v_catName_1099_ = lean_ctor_get(v_e_1043_, 0);
lean_inc(v_catName_1099_);
v_declName_1100_ = lean_ctor_get(v_e_1043_, 1);
lean_inc(v_declName_1100_);
v_leading_1101_ = lean_ctor_get_uint8(v_e_1043_, sizeof(void*)*4);
v_p_1102_ = lean_ctor_get(v_e_1043_, 2);
lean_inc_ref(v_p_1102_);
v_prio_1103_ = lean_ctor_get(v_e_1043_, 3);
lean_inc(v_prio_1103_);
lean_dec_ref_known(v_e_1043_, 4);
v_tokens_1104_ = lean_ctor_get(v_s_1042_, 0);
v_kinds_1105_ = lean_ctor_get(v_s_1042_, 1);
v_categories_1106_ = lean_ctor_get(v_s_1042_, 2);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_s_1042_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1108_ = v_s_1042_;
v_isShared_1109_ = v_isSharedCheck_1124_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_categories_1106_);
lean_inc(v_kinds_1105_);
lean_inc(v_tokens_1104_);
lean_dec(v_s_1042_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1124_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Parser_addParser(v_categories_1106_, v_catName_1099_, v_declName_1100_, v_leading_1101_, v_p_1102_, v_prio_1103_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_del_object(v___x_1108_);
lean_dec_ref(v_kinds_1105_);
lean_dec_ref(v_tokens_1104_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1110_, 1);
v___x_1112_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1113_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1114_ = lean_unsigned_to_nat(176u);
v___x_1115_ = lean_unsigned_to_nat(30u);
v___x_1116_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1117_ = lean_string_append(v___x_1116_, v_a_1111_);
lean_dec(v_a_1111_);
v___x_1118_ = l_mkPanicMessageWithDecl(v___x_1112_, v___x_1113_, v___x_1114_, v___x_1115_, v___x_1117_);
lean_dec_ref(v___x_1117_);
v___x_1119_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1118_);
return v___x_1119_;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; 
v_a_1120_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1110_, 1);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 2, v_a_1120_);
v___x_1122_ = v___x_1108_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_tokens_1104_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_kinds_1105_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_a_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl___redArg(lean_object* v_x_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_obj_tag_nat(v_x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl___redArg___boxed(lean_object* v_x_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Parser_AliasValue_ctorIdx___impl___redArg(v_x_1127_);
lean_dec_ref(v_x_1127_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl(lean_object* v_00_u03b1_1129_, lean_object* v_x_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_obj_tag_nat(v_x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl___boxed(lean_object* v_00_u03b1_1132_, lean_object* v_x_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_Parser_AliasValue_ctorIdx___impl(v_00_u03b1_1132_, v_x_1133_);
lean_dec_ref(v_x_1133_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___redArg(lean_object* v_t_1135_, lean_object* v_k_1136_){
_start:
{
lean_object* v_p_1137_; lean_object* v___x_1138_; 
v_p_1137_ = lean_ctor_get(v_t_1135_, 0);
lean_inc(v_p_1137_);
lean_dec_ref(v_t_1135_);
v___x_1138_ = lean_apply_1(v_k_1136_, v_p_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim(lean_object* v_00_u03b1_1139_, lean_object* v_motive_1140_, lean_object* v_ctorIdx_1141_, lean_object* v_t_1142_, lean_object* v_h_1143_, lean_object* v_k_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1142_, v_k_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___boxed(lean_object* v_00_u03b1_1146_, lean_object* v_motive_1147_, lean_object* v_ctorIdx_1148_, lean_object* v_t_1149_, lean_object* v_h_1150_, lean_object* v_k_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Parser_AliasValue_ctorElim(v_00_u03b1_1146_, v_motive_1147_, v_ctorIdx_1148_, v_t_1149_, v_h_1150_, v_k_1151_);
lean_dec(v_ctorIdx_1148_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim___redArg(lean_object* v_t_1153_, lean_object* v_const_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1153_, v_const_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim(lean_object* v_00_u03b1_1156_, lean_object* v_motive_1157_, lean_object* v_t_1158_, lean_object* v_h_1159_, lean_object* v_const_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1158_, v_const_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim___redArg(lean_object* v_t_1162_, lean_object* v_unary_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1162_, v_unary_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim(lean_object* v_00_u03b1_1165_, lean_object* v_motive_1166_, lean_object* v_t_1167_, lean_object* v_h_1168_, lean_object* v_unary_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1167_, v_unary_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim___redArg(lean_object* v_t_1171_, lean_object* v_binary_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1171_, v_binary_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim(lean_object* v_00_u03b1_1174_, lean_object* v_motive_1175_, lean_object* v_t_1176_, lean_object* v_h_1177_, lean_object* v_binary_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1176_, v_binary_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_Parser_registerAliasCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__0));
v___x_1182_ = lean_mk_io_user_error(v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg(lean_object* v_mapRef_1185_, lean_object* v_aliasName_1186_, lean_object* v_value_1187_){
_start:
{
uint8_t v___x_1189_; 
v___x_1189_ = l_Lean_initializing();
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v_value_1187_);
lean_dec(v_aliasName_1186_);
v___x_1190_ = lean_obj_once(&l_Lean_Parser_registerAliasCore___redArg___closed__1, &l_Lean_Parser_registerAliasCore___redArg___closed__1_once, _init_l_Lean_Parser_registerAliasCore___redArg___closed__1);
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
else
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = lean_st_ref_get(v_mapRef_1185_);
v___x_1193_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_aliasName_1186_, v___x_1192_);
lean_dec(v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1194_ = lean_st_ref_take(v_mapRef_1185_);
v___x_1195_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1186_, v_value_1187_, v___x_1194_);
v___x_1196_ = lean_st_ref_put(v_mapRef_1185_, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_dec_ref(v_value_1187_);
v___x_1198_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__2));
v___x_1199_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1186_, v___x_1193_);
v___x_1200_ = lean_string_append(v___x_1198_, v___x_1199_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__3));
v___x_1202_ = lean_string_append(v___x_1200_, v___x_1201_);
v___x_1203_ = lean_mk_io_user_error(v___x_1202_);
v___x_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg___boxed(lean_object* v_mapRef_1205_, lean_object* v_aliasName_1206_, lean_object* v_value_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1205_, v_aliasName_1206_, v_value_1207_);
lean_dec(v_mapRef_1205_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore(lean_object* v_00_u03b1_1210_, lean_object* v_mapRef_1211_, lean_object* v_aliasName_1212_, lean_object* v_value_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1211_, v_aliasName_1212_, v_value_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___boxed(lean_object* v_00_u03b1_1216_, lean_object* v_mapRef_1217_, lean_object* v_aliasName_1218_, lean_object* v_value_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_Parser_registerAliasCore(v_00_u03b1_1216_, v_mapRef_1217_, v_aliasName_1218_, v_value_1219_);
lean_dec(v_mapRef_1217_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg(lean_object* v_mapRef_1222_, lean_object* v_aliasName_1223_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_st_ref_get(v_mapRef_1222_);
v___x_1226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1225_, v_aliasName_1223_);
lean_dec(v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg___boxed(lean_object* v_mapRef_1228_, lean_object* v_aliasName_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1228_, v_aliasName_1229_);
lean_dec(v_aliasName_1229_);
lean_dec(v_mapRef_1228_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias(lean_object* v_00_u03b1_1232_, lean_object* v_mapRef_1233_, lean_object* v_aliasName_1234_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1233_, v_aliasName_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___boxed(lean_object* v_00_u03b1_1237_, lean_object* v_mapRef_1238_, lean_object* v_aliasName_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Parser_getAlias(v_00_u03b1_1237_, v_mapRef_1238_, v_aliasName_1239_);
lean_dec(v_aliasName_1239_);
lean_dec(v_mapRef_1238_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object* v_mapRef_1246_, lean_object* v_aliasName_1247_){
_start:
{
lean_object* v___x_1249_; lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1289_; 
v___x_1249_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1246_, v_aliasName_1247_);
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1289_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1289_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
if (lean_obj_tag(v_a_1250_) == 0)
{
lean_object* v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1254_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1255_ = 1;
v___x_1256_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1247_, v___x_1255_);
v___x_1257_ = lean_string_append(v___x_1254_, v___x_1256_);
lean_dec_ref(v___x_1256_);
v___x_1258_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1259_ = lean_string_append(v___x_1257_, v___x_1258_);
v___x_1260_ = lean_mk_io_user_error(v___x_1259_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set_tag(v___x_1252_, 1);
lean_ctor_set(v___x_1252_, 0, v___x_1260_);
v___x_1262_ = v___x_1252_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
else
{
lean_object* v_val_1264_; 
v_val_1264_ = lean_ctor_get(v_a_1250_, 0);
lean_inc(v_val_1264_);
lean_dec_ref_known(v_a_1250_, 1);
switch(lean_obj_tag(v_val_1264_))
{
case 0:
{
lean_object* v_p_1265_; lean_object* v___x_1267_; 
lean_dec(v_aliasName_1247_);
v_p_1265_ = lean_ctor_get(v_val_1264_, 0);
lean_inc(v_p_1265_);
lean_dec_ref_known(v_val_1264_, 1);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v_p_1265_);
v___x_1267_ = v___x_1252_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_p_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
case 1:
{
lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
lean_dec_ref_known(v_val_1264_, 1);
v___x_1269_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1270_ = 1;
v___x_1271_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1247_, v___x_1270_);
v___x_1272_ = lean_string_append(v___x_1269_, v___x_1271_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__2));
v___x_1274_ = lean_string_append(v___x_1272_, v___x_1273_);
v___x_1275_ = lean_mk_io_user_error(v___x_1274_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set_tag(v___x_1252_, 1);
lean_ctor_set(v___x_1252_, 0, v___x_1275_);
v___x_1277_ = v___x_1252_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
default: 
{
lean_object* v___x_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
lean_dec_ref_known(v_val_1264_, 1);
v___x_1279_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1280_ = 1;
v___x_1281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1247_, v___x_1280_);
v___x_1282_ = lean_string_append(v___x_1279_, v___x_1281_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__3));
v___x_1284_ = lean_string_append(v___x_1282_, v___x_1283_);
v___x_1285_ = lean_mk_io_user_error(v___x_1284_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set_tag(v___x_1252_, 1);
lean_ctor_set(v___x_1252_, 0, v___x_1285_);
v___x_1287_ = v___x_1252_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object* v_mapRef_1290_, lean_object* v_aliasName_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1290_, v_aliasName_1291_);
lean_dec(v_mapRef_1290_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias(lean_object* v_00_u03b1_1294_, lean_object* v_mapRef_1295_, lean_object* v_aliasName_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1295_, v_aliasName_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object* v_00_u03b1_1299_, lean_object* v_mapRef_1300_, lean_object* v_aliasName_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_Parser_getConstAlias(v_00_u03b1_1299_, v_mapRef_1300_, v_aliasName_1301_);
lean_dec(v_mapRef_1300_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object* v_mapRef_1305_, lean_object* v_aliasName_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1338_; 
v___x_1308_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1305_, v_aliasName_1306_);
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1338_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1338_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
if (lean_obj_tag(v_a_1309_) == 0)
{
lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1313_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1314_ = 1;
v___x_1315_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1306_, v___x_1314_);
v___x_1316_ = lean_string_append(v___x_1313_, v___x_1315_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
v___x_1319_ = lean_mk_io_user_error(v___x_1318_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set_tag(v___x_1311_, 1);
lean_ctor_set(v___x_1311_, 0, v___x_1319_);
v___x_1321_ = v___x_1311_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
else
{
lean_object* v_val_1323_; 
v_val_1323_ = lean_ctor_get(v_a_1309_, 0);
lean_inc(v_val_1323_);
lean_dec_ref_known(v_a_1309_, 1);
if (lean_obj_tag(v_val_1323_) == 1)
{
lean_object* v_p_1324_; lean_object* v___x_1326_; 
lean_dec(v_aliasName_1306_);
v_p_1324_ = lean_ctor_get(v_val_1323_, 0);
lean_inc(v_p_1324_);
lean_dec_ref_known(v_val_1323_, 1);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v_p_1324_);
v___x_1326_ = v___x_1311_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_p_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
else
{
lean_object* v___x_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
lean_dec(v_val_1323_);
v___x_1328_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1329_ = 1;
v___x_1330_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1306_, v___x_1329_);
v___x_1331_ = lean_string_append(v___x_1328_, v___x_1330_);
lean_dec_ref(v___x_1330_);
v___x_1332_ = ((lean_object*)(l_Lean_Parser_getUnaryAlias___redArg___closed__0));
v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
v___x_1334_ = lean_mk_io_user_error(v___x_1333_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set_tag(v___x_1311_, 1);
lean_ctor_set(v___x_1311_, 0, v___x_1334_);
v___x_1336_ = v___x_1311_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object* v_mapRef_1339_, lean_object* v_aliasName_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1339_, v_aliasName_1340_);
lean_dec(v_mapRef_1339_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias(lean_object* v_00_u03b1_1343_, lean_object* v_mapRef_1344_, lean_object* v_aliasName_1345_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1344_, v_aliasName_1345_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object* v_00_u03b1_1348_, lean_object* v_mapRef_1349_, lean_object* v_aliasName_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_Parser_getUnaryAlias(v_00_u03b1_1348_, v_mapRef_1349_, v_aliasName_1350_);
lean_dec(v_mapRef_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object* v_mapRef_1354_, lean_object* v_aliasName_1355_){
_start:
{
lean_object* v___x_1357_; lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1387_; 
v___x_1357_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1354_, v_aliasName_1355_);
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1387_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1387_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
if (lean_obj_tag(v_a_1358_) == 0)
{
lean_object* v___x_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1362_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1363_ = 1;
v___x_1364_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1355_, v___x_1363_);
v___x_1365_ = lean_string_append(v___x_1362_, v___x_1364_);
lean_dec_ref(v___x_1364_);
v___x_1366_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1367_ = lean_string_append(v___x_1365_, v___x_1366_);
v___x_1368_ = lean_mk_io_user_error(v___x_1367_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set_tag(v___x_1360_, 1);
lean_ctor_set(v___x_1360_, 0, v___x_1368_);
v___x_1370_ = v___x_1360_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
else
{
lean_object* v_val_1372_; 
v_val_1372_ = lean_ctor_get(v_a_1358_, 0);
lean_inc(v_val_1372_);
lean_dec_ref_known(v_a_1358_, 1);
if (lean_obj_tag(v_val_1372_) == 2)
{
lean_object* v_p_1373_; lean_object* v___x_1375_; 
lean_dec(v_aliasName_1355_);
v_p_1373_ = lean_ctor_get(v_val_1372_, 0);
lean_inc(v_p_1373_);
lean_dec_ref_known(v_val_1372_, 1);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v_p_1373_);
v___x_1375_ = v___x_1360_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_p_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
else
{
lean_object* v___x_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
lean_dec(v_val_1372_);
v___x_1377_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1378_ = 1;
v___x_1379_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1355_, v___x_1378_);
v___x_1380_ = lean_string_append(v___x_1377_, v___x_1379_);
lean_dec_ref(v___x_1379_);
v___x_1381_ = ((lean_object*)(l_Lean_Parser_getBinaryAlias___redArg___closed__0));
v___x_1382_ = lean_string_append(v___x_1380_, v___x_1381_);
v___x_1383_ = lean_mk_io_user_error(v___x_1382_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set_tag(v___x_1360_, 1);
lean_ctor_set(v___x_1360_, 0, v___x_1383_);
v___x_1385_ = v___x_1360_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg___boxed(lean_object* v_mapRef_1388_, lean_object* v_aliasName_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1388_, v_aliasName_1389_);
lean_dec(v_mapRef_1388_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias(lean_object* v_00_u03b1_1392_, lean_object* v_mapRef_1393_, lean_object* v_aliasName_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1393_, v_aliasName_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___boxed(lean_object* v_00_u03b1_1397_, lean_object* v_mapRef_1398_, lean_object* v_aliasName_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_Parser_getBinaryAlias(v_00_u03b1_1397_, v_mapRef_1398_, v_aliasName_1399_);
lean_dec(v_mapRef_1398_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = lean_box(1);
v___x_1416_ = lean_st_mk_ref(v___x_1415_);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object* v_a_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(lean_object* v_t_1420_, lean_object* v_k_1421_, lean_object* v_fallback_1422_){
_start:
{
if (lean_obj_tag(v_t_1420_) == 0)
{
lean_object* v_k_1423_; lean_object* v_v_1424_; lean_object* v_l_1425_; lean_object* v_r_1426_; uint8_t v___x_1427_; 
v_k_1423_ = lean_ctor_get(v_t_1420_, 1);
v_v_1424_ = lean_ctor_get(v_t_1420_, 2);
v_l_1425_ = lean_ctor_get(v_t_1420_, 3);
v_r_1426_ = lean_ctor_get(v_t_1420_, 4);
v___x_1427_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1421_, v_k_1423_);
switch(v___x_1427_)
{
case 0:
{
v_t_1420_ = v_l_1425_;
goto _start;
}
case 1:
{
lean_inc(v_v_1424_);
return v_v_1424_;
}
default: 
{
v_t_1420_ = v_r_1426_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_1422_);
return v_fallback_1422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg___boxed(lean_object* v_t_1430_, lean_object* v_k_1431_, lean_object* v_fallback_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1430_, v_k_1431_, v_fallback_1432_);
lean_dec(v_fallback_1432_);
lean_dec(v_k_1431_);
lean_dec(v_t_1430_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo(lean_object* v_aliasName_1440_){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1442_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1443_ = lean_st_ref_get(v___x_1442_);
v___x_1444_ = ((lean_object*)(l_Lean_Parser_getParserAliasInfo___closed__1));
v___x_1445_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v___x_1443_, v_aliasName_1440_, v___x_1444_);
lean_dec(v___x_1443_);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo___boxed(lean_object* v_aliasName_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Parser_getParserAliasInfo(v_aliasName_1447_);
lean_dec(v_aliasName_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(lean_object* v_00_u03b4_1450_, lean_object* v_t_1451_, lean_object* v_k_1452_, lean_object* v_fallback_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1451_, v_k_1452_, v_fallback_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___boxed(lean_object* v_00_u03b4_1455_, lean_object* v_t_1456_, lean_object* v_k_1457_, lean_object* v_fallback_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(v_00_u03b4_1455_, v_t_1456_, v_k_1457_, v_fallback_1458_);
lean_dec(v_fallback_1458_);
lean_dec(v_k_1457_);
lean_dec(v_t_1456_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias(lean_object* v_aliasName_1460_, lean_object* v_declName_1461_, lean_object* v_p_1462_, lean_object* v_kind_x3f_1463_, lean_object* v_info_1464_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = l_Lean_Parser_parserAliasesRef;
lean_inc(v_aliasName_1460_);
v___x_1483_ = l_Lean_Parser_registerAliasCore___redArg(v___x_1482_, v_aliasName_1460_, v_p_1462_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_dec_ref_known(v___x_1483_, 1);
if (lean_obj_tag(v_kind_x3f_1463_) == 1)
{
lean_object* v_val_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_val_1484_ = lean_ctor_get(v_kind_x3f_1463_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v_kind_x3f_1463_, 1);
v___x_1485_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1486_ = lean_st_ref_take(v___x_1485_);
lean_inc(v_aliasName_1460_);
v___x_1487_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1460_, v_val_1484_, v___x_1486_);
v___x_1488_ = lean_st_ref_put(v___x_1485_, v___x_1487_);
goto v___jp_1466_;
}
else
{
lean_dec(v_kind_x3f_1463_);
goto v___jp_1466_;
}
}
else
{
lean_dec_ref(v_info_1464_);
lean_dec(v_kind_x3f_1463_);
lean_dec(v_declName_1461_);
lean_dec(v_aliasName_1460_);
return v___x_1483_;
}
v___jp_1466_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v_stackSz_x3f_1469_; uint8_t v_autoGroupArgs_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1480_; 
v___x_1467_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1468_ = lean_st_ref_take(v___x_1467_);
v_stackSz_x3f_1469_ = lean_ctor_get(v_info_1464_, 1);
v_autoGroupArgs_1470_ = lean_ctor_get_uint8(v_info_1464_, sizeof(void*)*2);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_info_1464_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v_info_1464_, 0);
lean_dec(v_unused_1481_);
v___x_1472_ = v_info_1464_;
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_stackSz_x3f_1469_);
lean_dec(v_info_1464_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v_declName_1461_);
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_declName_1461_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_stackSz_x3f_1469_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*2, v_autoGroupArgs_1470_);
v___x_1475_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1476_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1460_, v___x_1475_, v___x_1468_);
v___x_1477_ = lean_st_ref_put(v___x_1467_, v___x_1476_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias___boxed(lean_object* v_aliasName_1489_, lean_object* v_declName_1490_, lean_object* v_p_1491_, lean_object* v_kind_x3f_1492_, lean_object* v_info_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_Parser_registerAlias(v_aliasName_1489_, v_declName_1490_, v_p_1491_, v_kind_x3f_1492_, v_info_1493_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue___lam__0(lean_object* v_p_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_p_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0(lean_object* v_p_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_p_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0(lean_object* v_p_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_p_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias(lean_object* v_aliasName_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1526_; 
v___x_1510_ = l_Lean_Parser_parserAliasesRef;
v___x_1511_ = l_Lean_Parser_getAlias___redArg(v___x_1510_, v_aliasName_1508_);
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1526_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1526_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
if (lean_obj_tag(v_a_1512_) == 1)
{
uint8_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
lean_dec_ref_known(v_a_1512_, 1);
v___x_1516_ = 1;
v___x_1517_ = lean_box(v___x_1516_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1517_);
v___x_1519_ = v___x_1514_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
else
{
uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
lean_dec(v_a_1512_);
v___x_1521_ = 0;
v___x_1522_ = lean_box(v___x_1521_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1522_);
v___x_1524_ = v___x_1514_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object* v_aliasName_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Parser_isParserAlias(v_aliasName_1527_);
lean_dec(v_aliasName_1527_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object* v_aliasName_1530_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1532_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1533_ = lean_st_ref_get(v___x_1532_);
v___x_1534_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1533_, v_aliasName_1530_);
lean_dec(v___x_1533_);
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f___boxed(lean_object* v_aliasName_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v_aliasName_1536_);
lean_dec(v_aliasName_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object* v_aliasName_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = l_Lean_Parser_parserAliasesRef;
v___x_1542_ = lean_box(0);
v___x_1543_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1541_, v_aliasName_1539_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v___x_1543_, 0);
lean_dec(v_unused_1551_);
v___x_1545_ = v___x_1543_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_dec(v___x_1543_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1542_);
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1542_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_a_1552_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1543_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1543_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias___boxed(lean_object* v_aliasName_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_Parser_ensureUnaryParserAlias(v_aliasName_1560_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object* v_aliasName_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = l_Lean_Parser_parserAliasesRef;
v___x_1566_ = lean_box(0);
v___x_1567_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1565_, v_aliasName_1563_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; 
v_unused_1575_ = lean_ctor_get(v___x_1567_, 0);
lean_dec(v_unused_1575_);
v___x_1569_ = v___x_1567_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_dec(v___x_1567_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1566_);
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1566_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_a_1576_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1567_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1567_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias___boxed(lean_object* v_aliasName_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Parser_ensureBinaryParserAlias(v_aliasName_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object* v_aliasName_1587_){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = l_Lean_Parser_parserAliasesRef;
v___x_1590_ = lean_box(0);
v___x_1591_ = l_Lean_Parser_getConstAlias___redArg(v___x_1589_, v_aliasName_1587_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v___x_1591_, 0);
lean_dec(v_unused_1599_);
v___x_1593_ = v___x_1591_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_dec(v___x_1591_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1590_);
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1590_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_a_1600_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1591_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1591_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias___boxed(lean_object* v_aliasName_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Parser_ensureConstantParserAlias(v_aliasName_1608_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* v_constName_1619_, lean_object* v_compileParserDescr_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_env_1632_; lean_object* v_opts_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; 
v_env_1632_ = lean_ctor_get(v_a_1621_, 0);
v_opts_1633_ = lean_ctor_get(v_a_1621_, 1);
v___x_1634_ = 0;
lean_inc(v_constName_1619_);
lean_inc_ref(v_env_1632_);
v___x_1635_ = l_Lean_Environment_find_x3f(v_env_1632_, v_constName_1619_, v___x_1634_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec_ref(v_compileParserDescr_1620_);
v___x_1636_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_1637_ = 1;
v___x_1638_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1619_, v___x_1637_);
v___x_1639_ = lean_string_append(v___x_1636_, v___x_1638_);
lean_dec_ref(v___x_1638_);
v___x_1640_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_1641_ = lean_string_append(v___x_1639_, v___x_1640_);
v___x_1642_ = lean_mk_io_user_error(v___x_1641_);
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
else
{
lean_object* v_val_1644_; lean_object* v___x_1645_; 
v_val_1644_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_val_1644_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1645_ = l_Lean_ConstantInfo_type(v_val_1644_);
lean_dec(v_val_1644_);
if (lean_obj_tag(v___x_1645_) == 4)
{
lean_object* v_declName_1646_; 
v_declName_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_declName_1646_);
lean_dec_ref_known(v___x_1645_, 2);
if (lean_obj_tag(v_declName_1646_) == 1)
{
lean_object* v_pre_1647_; 
v_pre_1647_ = lean_ctor_get(v_declName_1646_, 0);
lean_inc(v_pre_1647_);
if (lean_obj_tag(v_pre_1647_) == 1)
{
lean_object* v_pre_1648_; 
v_pre_1648_ = lean_ctor_get(v_pre_1647_, 0);
switch(lean_obj_tag(v_pre_1648_))
{
case 1:
{
lean_object* v_pre_1649_; 
lean_inc_ref(v_pre_1648_);
lean_dec_ref(v_compileParserDescr_1620_);
v_pre_1649_ = lean_ctor_get(v_pre_1648_, 0);
if (lean_obj_tag(v_pre_1649_) == 0)
{
lean_object* v_str_1650_; lean_object* v_str_1651_; lean_object* v_str_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v_str_1650_ = lean_ctor_get(v_declName_1646_, 1);
lean_inc_ref(v_str_1650_);
lean_dec_ref_known(v_declName_1646_, 2);
v_str_1651_ = lean_ctor_get(v_pre_1647_, 1);
lean_inc_ref(v_str_1651_);
lean_dec_ref_known(v_pre_1647_, 2);
v_str_1652_ = lean_ctor_get(v_pre_1648_, 1);
lean_inc_ref(v_str_1652_);
lean_dec_ref_known(v_pre_1648_, 2);
v___x_1653_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1654_ = lean_string_dec_eq(v_str_1652_, v___x_1653_);
lean_dec_ref(v_str_1652_);
if (v___x_1654_ == 0)
{
lean_dec_ref(v_str_1651_);
lean_dec_ref(v_str_1650_);
goto v___jp_1623_;
}
else
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_1656_ = lean_string_dec_eq(v_str_1651_, v___x_1655_);
lean_dec_ref(v_str_1651_);
if (v___x_1656_ == 0)
{
lean_dec_ref(v_str_1650_);
goto v___jp_1623_;
}
else
{
lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_1658_ = lean_string_dec_eq(v_str_1650_, v___x_1657_);
if (v___x_1658_ == 0)
{
uint8_t v___x_1659_; 
v___x_1659_ = lean_string_dec_eq(v_str_1650_, v___x_1655_);
lean_dec_ref(v_str_1650_);
if (v___x_1659_ == 0)
{
goto v___jp_1623_;
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = l_Lean_Environment_evalConst___redArg(v_env_1632_, v_opts_1633_, v_constName_1619_, v___x_1659_);
lean_dec(v_constName_1619_);
v___x_1661_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1660_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1671_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1671_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1671_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1666_ = lean_box(v___x_1659_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v_a_1662_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1667_);
v___x_1669_ = v___x_1664_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
v_a_1672_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1661_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1661_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec_ref(v_str_1650_);
v___x_1680_ = l_Lean_Environment_evalConst___redArg(v_env_1632_, v_opts_1633_, v_constName_1619_, v___x_1658_);
lean_dec(v_constName_1619_);
v___x_1681_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1680_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1691_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1686_ = lean_box(v___x_1634_);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v_a_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1687_);
v___x_1689_ = v___x_1684_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
v_a_1692_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1681_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1681_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1648_, 2);
lean_dec_ref_known(v_pre_1647_, 2);
lean_dec_ref_known(v_declName_1646_, 2);
goto v___jp_1623_;
}
}
case 0:
{
lean_object* v_str_1700_; lean_object* v_str_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_str_1700_ = lean_ctor_get(v_declName_1646_, 1);
lean_inc_ref(v_str_1700_);
lean_dec_ref_known(v_declName_1646_, 2);
v_str_1701_ = lean_ctor_get(v_pre_1647_, 1);
lean_inc_ref(v_str_1701_);
lean_dec_ref_known(v_pre_1647_, 2);
v___x_1702_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1703_ = lean_string_dec_eq(v_str_1701_, v___x_1702_);
lean_dec_ref(v_str_1701_);
if (v___x_1703_ == 0)
{
lean_dec_ref(v_str_1700_);
lean_dec_ref(v_compileParserDescr_1620_);
goto v___jp_1623_;
}
else
{
lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_1705_ = lean_string_dec_eq(v_str_1700_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_1707_ = lean_string_dec_eq(v_str_1700_, v___x_1706_);
lean_dec_ref(v_str_1700_);
if (v___x_1707_ == 0)
{
lean_dec_ref(v_compileParserDescr_1620_);
goto v___jp_1623_;
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = l_Lean_Environment_evalConst___redArg(v_env_1632_, v_opts_1633_, v_constName_1619_, v___x_1707_);
lean_dec(v_constName_1619_);
v___x_1709_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1708_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1711_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
lean_inc_ref(v_a_1621_);
v___x_1711_ = lean_apply_3(v_compileParserDescr_1620_, v_a_1710_, v_a_1621_, lean_box(0));
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1721_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1721_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1721_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1716_ = lean_box(v___x_1705_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
lean_ctor_set(v___x_1717_, 1, v_a_1712_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1717_);
v___x_1719_ = v___x_1714_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
v_a_1722_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1711_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1711_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec_ref(v_compileParserDescr_1620_);
v_a_1730_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1709_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1709_);
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
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec_ref(v_str_1700_);
v___x_1738_ = l_Lean_Environment_evalConst___redArg(v_env_1632_, v_opts_1633_, v_constName_1619_, v___x_1705_);
lean_dec(v_constName_1619_);
v___x_1739_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1738_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
lean_inc_ref(v_a_1621_);
v___x_1741_ = lean_apply_3(v_compileParserDescr_1620_, v_a_1740_, v_a_1621_, lean_box(0));
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1751_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1751_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1751_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1746_ = lean_box(v___x_1705_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v_a_1742_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1747_);
v___x_1749_ = v___x_1744_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
v_a_1752_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1741_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1741_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v_compileParserDescr_1620_);
v_a_1760_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1739_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1739_);
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
}
}
default: 
{
lean_dec_ref_known(v_pre_1647_, 2);
lean_dec_ref_known(v_declName_1646_, 2);
lean_dec_ref(v_compileParserDescr_1620_);
goto v___jp_1623_;
}
}
}
else
{
lean_dec_ref_known(v_declName_1646_, 2);
lean_dec(v_pre_1647_);
lean_dec_ref(v_compileParserDescr_1620_);
goto v___jp_1623_;
}
}
else
{
lean_dec(v_declName_1646_);
lean_dec_ref(v_compileParserDescr_1620_);
goto v___jp_1623_;
}
}
else
{
lean_dec_ref(v___x_1645_);
lean_dec_ref(v_compileParserDescr_1620_);
goto v___jp_1623_;
}
}
v___jp_1623_:
{
lean_object* v___x_1624_; uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1624_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__0));
v___x_1625_ = 1;
v___x_1626_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1619_, v___x_1625_);
v___x_1627_ = lean_string_append(v___x_1624_, v___x_1626_);
lean_dec_ref(v___x_1626_);
v___x_1628_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1));
v___x_1629_ = lean_string_append(v___x_1627_, v___x_1628_);
v___x_1630_ = lean_mk_io_user_error(v___x_1629_);
v___x_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object* v_constName_1768_, lean_object* v_compileParserDescr_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1768_, v_compileParserDescr_1769_, v_a_1770_);
lean_dec_ref(v_a_1770_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed(lean_object* v_categories_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1773_, v_a_1774_, v_a_1775_);
lean_dec_ref(v_a_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(lean_object* v_categories_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
switch(lean_obj_tag(v_a_1779_))
{
case 0:
{
lean_object* v_name_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_dec_ref(v_categories_1778_);
v_name_1782_ = lean_ctor_get(v_a_1779_, 0);
lean_inc(v_name_1782_);
lean_dec_ref_known(v_a_1779_, 1);
v___x_1783_ = l_Lean_Parser_parserAliasesRef;
v___x_1784_ = l_Lean_Parser_getConstAlias___redArg(v___x_1783_, v_name_1782_);
return v___x_1784_;
}
case 1:
{
lean_object* v_name_1785_; lean_object* v_p_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_name_1785_ = lean_ctor_get(v_a_1779_, 0);
lean_inc(v_name_1785_);
v_p_1786_ = lean_ctor_get(v_a_1779_, 1);
lean_inc_ref(v_p_1786_);
lean_dec_ref_known(v_a_1779_, 2);
v___x_1787_ = l_Lean_Parser_parserAliasesRef;
v___x_1788_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1787_, v_name_1785_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1778_, v_p_1786_, v_a_1780_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1799_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1799_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1795_ = lean_apply_1(v_a_1789_, v_a_1791_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1795_);
v___x_1797_ = v___x_1793_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
else
{
lean_dec(v_a_1789_);
return v___x_1790_;
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec_ref(v_p_1786_);
lean_dec_ref(v_categories_1778_);
v_a_1800_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1788_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1788_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
case 2:
{
lean_object* v_name_1808_; lean_object* v_p_u2081_1809_; lean_object* v_p_u2082_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_name_1808_ = lean_ctor_get(v_a_1779_, 0);
lean_inc(v_name_1808_);
v_p_u2081_1809_ = lean_ctor_get(v_a_1779_, 1);
lean_inc_ref(v_p_u2081_1809_);
v_p_u2082_1810_ = lean_ctor_get(v_a_1779_, 2);
lean_inc_ref(v_p_u2082_1810_);
lean_dec_ref_known(v_a_1779_, 3);
v___x_1811_ = l_Lean_Parser_parserAliasesRef;
v___x_1812_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1811_, v_name_1808_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1814_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1812_, 1);
lean_inc_ref(v_categories_1778_);
v___x_1814_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1778_, v_p_u2081_1809_, v_a_1780_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1816_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1814_, 1);
v___x_1816_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1778_, v_p_u2082_1810_, v_a_1780_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1825_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1825_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1825_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1821_ = lean_apply_2(v_a_1813_, v_a_1815_, v_a_1817_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1821_);
v___x_1823_ = v___x_1819_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
else
{
lean_dec(v_a_1815_);
lean_dec(v_a_1813_);
return v___x_1816_;
}
}
else
{
lean_dec(v_a_1813_);
lean_dec_ref(v_p_u2082_1810_);
lean_dec_ref(v_categories_1778_);
return v___x_1814_;
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v_p_u2082_1810_);
lean_dec_ref(v_p_u2081_1809_);
lean_dec_ref(v_categories_1778_);
v_a_1826_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1812_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1812_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
case 3:
{
lean_object* v_kind_1834_; lean_object* v_prec_1835_; lean_object* v_p_1836_; lean_object* v___x_1837_; 
v_kind_1834_ = lean_ctor_get(v_a_1779_, 0);
lean_inc(v_kind_1834_);
v_prec_1835_ = lean_ctor_get(v_a_1779_, 1);
lean_inc(v_prec_1835_);
v_p_1836_ = lean_ctor_get(v_a_1779_, 2);
lean_inc_ref(v_p_1836_);
lean_dec_ref_known(v_a_1779_, 3);
v___x_1837_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1778_, v_p_1836_, v_a_1780_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1846_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = l_Lean_Parser_leadingNode(v_kind_1834_, v_prec_1835_, v_a_1838_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
lean_dec(v_prec_1835_);
lean_dec(v_kind_1834_);
return v___x_1837_;
}
}
case 4:
{
lean_object* v_kind_1847_; lean_object* v_prec_1848_; lean_object* v_lhsPrec_1849_; lean_object* v_p_1850_; lean_object* v___x_1851_; 
v_kind_1847_ = lean_ctor_get(v_a_1779_, 0);
lean_inc(v_kind_1847_);
v_prec_1848_ = lean_ctor_get(v_a_1779_, 1);
lean_inc(v_prec_1848_);
v_lhsPrec_1849_ = lean_ctor_get(v_a_1779_, 2);
lean_inc(v_lhsPrec_1849_);
v_p_1850_ = lean_ctor_get(v_a_1779_, 3);
lean_inc_ref(v_p_1850_);
lean_dec_ref_known(v_a_1779_, 4);
v___x_1851_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1778_, v_p_1850_, v_a_1780_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1860_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1856_ = l_Lean_Parser_trailingNode(v_kind_1847_, v_prec_1848_, v_lhsPrec_1849_, v_a_1852_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1856_);
v___x_1858_ = v___x_1854_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
else
{
lean_dec(v_lhsPrec_1849_);
lean_dec(v_prec_1848_);
lean_dec(v_kind_1847_);
return v___x_1851_;
}
}
case 5:
{
lean_object* v_val_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v_categories_1778_);
v_val_1861_ = lean_ctor_get(v_a_1779_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_a_1779_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1863_ = v_a_1779_;
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_val_1861_);
lean_dec(v_a_1779_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1869_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = l_Lean_Parser_symbol(v_val_1861_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set_tag(v___x_1863_, 0);
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
case 6:
{
lean_object* v_val_1870_; uint8_t v_includeIdent_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
lean_dec_ref(v_categories_1778_);
v_val_1870_ = lean_ctor_get(v_a_1779_, 0);
lean_inc_ref(v_val_1870_);
v_includeIdent_1871_ = lean_ctor_get_uint8(v_a_1779_, sizeof(void*)*1);
lean_dec_ref_known(v_a_1779_, 1);
v___x_1872_ = l_Lean_Parser_nonReservedSymbol(v_val_1870_, v_includeIdent_1871_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
return v___x_1873_;
}
case 7:
{
lean_object* v_catName_1874_; lean_object* v_rbp_1875_; lean_object* v___x_1876_; 
v_catName_1874_ = lean_ctor_get(v_a_1779_, 0);
lean_inc(v_catName_1874_);
v_rbp_1875_ = lean_ctor_get(v_a_1779_, 1);
lean_inc(v_rbp_1875_);
lean_dec_ref_known(v_a_1779_, 2);
v___x_1876_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_1778_, v_catName_1874_);
lean_dec_ref(v_categories_1778_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec(v_rbp_1875_);
v___x_1877_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_1874_);
v___x_1878_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1877_);
return v___x_1878_;
}
else
{
lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1886_; 
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1886_ == 0)
{
lean_object* v_unused_1887_; 
v_unused_1887_ = lean_ctor_get(v___x_1876_, 0);
lean_dec(v_unused_1887_);
v___x_1880_ = v___x_1876_;
v_isShared_1881_ = v_isSharedCheck_1886_;
goto v_resetjp_1879_;
}
else
{
lean_dec(v___x_1876_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1886_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = l_Lean_Parser_categoryParser(v_catName_1874_, v_rbp_1875_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set_tag(v___x_1880_, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1882_);
v___x_1884_ = v___x_1880_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
case 8:
{
lean_object* v_declName_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_declName_1888_ = lean_ctor_get(v_a_1779_, 0);
lean_inc(v_declName_1888_);
lean_dec_ref_known(v_a_1779_, 1);
v___x_1889_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed), 4, 1);
lean_closure_set(v___x_1889_, 0, v_categories_1778_);
v___x_1890_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_declName_1888_, v___x_1889_, v_a_1780_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1899_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_snd_1895_; lean_object* v___x_1897_; 
v_snd_1895_ = lean_ctor_get(v_a_1891_, 1);
lean_inc(v_snd_1895_);
lean_dec(v_a_1891_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v_snd_1895_);
v___x_1897_ = v___x_1893_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_snd_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
v_a_1900_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1890_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1890_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
case 9:
{
lean_object* v_name_1908_; lean_object* v_kind_1909_; lean_object* v_p_1910_; lean_object* v___x_1911_; 
v_name_1908_ = lean_ctor_get(v_a_1779_, 0);
lean_inc_ref(v_name_1908_);
v_kind_1909_ = lean_ctor_get(v_a_1779_, 1);
lean_inc(v_kind_1909_);
v_p_1910_ = lean_ctor_get(v_a_1779_, 2);
lean_inc_ref(v_p_1910_);
lean_dec_ref_known(v_a_1779_, 3);
v___x_1911_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1778_, v_p_1910_, v_a_1780_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1922_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_1922_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1922_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
uint8_t v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1916_ = 1;
lean_inc(v_kind_1909_);
v___x_1917_ = l_Lean_Parser_nodeWithAntiquot(v_name_1908_, v_kind_1909_, v_a_1912_, v___x_1916_);
v___x_1918_ = l_Lean_Parser_withCache(v_kind_1909_, v___x_1917_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v___x_1918_);
v___x_1920_ = v___x_1914_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
else
{
lean_dec(v_kind_1909_);
lean_dec_ref(v_name_1908_);
return v___x_1911_;
}
}
case 10:
{
lean_object* v_p_1923_; lean_object* v_sep_1924_; lean_object* v_psep_1925_; uint8_t v_allowTrailingSep_1926_; lean_object* v___x_1927_; 
v_p_1923_ = lean_ctor_get(v_a_1779_, 0);
lean_inc_ref(v_p_1923_);
v_sep_1924_ = lean_ctor_get(v_a_1779_, 1);
lean_inc_ref(v_sep_1924_);
v_psep_1925_ = lean_ctor_get(v_a_1779_, 2);
lean_inc_ref(v_psep_1925_);
v_allowTrailingSep_1926_ = lean_ctor_get_uint8(v_a_1779_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1779_, 3);
lean_inc_ref(v_categories_1778_);
v___x_1927_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1778_, v_p_1923_, v_a_1780_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1778_, v_psep_1925_, v_a_1780_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1938_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1938_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1938_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = l_Lean_Parser_sepBy(v_a_1928_, v_sep_1924_, v_a_1930_, v_allowTrailingSep_1926_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1934_);
v___x_1936_ = v___x_1932_;
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
lean_dec(v_a_1928_);
lean_dec_ref(v_sep_1924_);
return v___x_1929_;
}
}
else
{
lean_dec_ref(v_psep_1925_);
lean_dec_ref(v_sep_1924_);
lean_dec_ref(v_categories_1778_);
return v___x_1927_;
}
}
case 11:
{
lean_object* v_p_1939_; lean_object* v_sep_1940_; lean_object* v_psep_1941_; uint8_t v_allowTrailingSep_1942_; lean_object* v___x_1943_; 
v_p_1939_ = lean_ctor_get(v_a_1779_, 0);
lean_inc_ref(v_p_1939_);
v_sep_1940_ = lean_ctor_get(v_a_1779_, 1);
lean_inc_ref(v_sep_1940_);
v_psep_1941_ = lean_ctor_get(v_a_1779_, 2);
lean_inc_ref(v_psep_1941_);
v_allowTrailingSep_1942_ = lean_ctor_get_uint8(v_a_1779_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1779_, 3);
lean_inc_ref(v_categories_1778_);
v___x_1943_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1778_, v_p_1939_, v_a_1780_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1945_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v___x_1945_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1778_, v_psep_1941_, v_a_1780_);
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
v___x_1950_ = l_Lean_Parser_sepBy1(v_a_1944_, v_sep_1940_, v_a_1946_, v_allowTrailingSep_1942_);
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
lean_dec_ref(v_categories_1778_);
return v___x_1943_;
}
}
default: 
{
lean_object* v_val_1955_; lean_object* v_asciiVal_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec_ref(v_categories_1778_);
v_val_1955_ = lean_ctor_get(v_a_1779_, 0);
lean_inc_ref(v_val_1955_);
v_asciiVal_1956_ = lean_ctor_get(v_a_1779_, 1);
lean_inc_ref(v_asciiVal_1956_);
lean_dec_ref_known(v_a_1779_, 2);
v___x_1957_ = l_Lean_Parser_unicodeSymbol___redArg(v_val_1955_, v_asciiVal_1956_);
v___x_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
return v___x_1958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr(lean_object* v_categories_1959_, lean_object* v_d_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1959_, v_d_1960_, v_a_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object* v_categories_1964_, lean_object* v_d_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Parser_compileParserDescr(v_categories_1964_, v_d_1965_, v_a_1966_);
lean_dec_ref(v_a_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0(lean_object* v_categories_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1969_, v___y_1970_, v___y_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0___boxed(lean_object* v_categories_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Parser_mkParserOfConstant___lam__0(v_categories_1974_, v___y_1975_, v___y_1976_);
lean_dec_ref(v___y_1976_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* v_categories_1979_, lean_object* v_constName_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v___f_1983_; lean_object* v___x_1984_; 
v___f_1983_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserOfConstant___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1983_, 0, v_categories_1979_);
v___x_1984_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1980_, v___f_1983_, v_a_1981_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___boxed(lean_object* v_categories_1985_, lean_object* v_constName_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Parser_mkParserOfConstant(v_categories_1985_, v_constName_1986_, v_a_1987_);
lean_dec_ref(v_a_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = lean_box(0);
v___x_1992_ = lean_st_mk_ref(v___x_1991_);
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object* v_a_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object* v_hook_1996_){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1998_ = l_Lean_Parser_parserAttributeHooks;
v___x_1999_ = lean_st_ref_take(v___x_1998_);
v___x_2000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2000_, 0, v_hook_1996_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___x_2001_ = lean_st_ref_put(v___x_1998_, v___x_2000_);
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook___boxed(lean_object* v_hook_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Parser_registerParserAttributeHook(v_hook_2003_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(lean_object* v_catName_2006_, lean_object* v_declName_2007_, uint8_t v_builtin_2008_, lean_object* v_as_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
if (lean_obj_tag(v_as_2009_) == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec(v_declName_2007_);
lean_dec(v_catName_2006_);
v___x_2013_ = lean_box(0);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
else
{
lean_object* v_head_2015_; lean_object* v_tail_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_head_2015_ = lean_ctor_get(v_as_2009_, 0);
lean_inc(v_head_2015_);
v_tail_2016_ = lean_ctor_get(v_as_2009_, 1);
lean_inc(v_tail_2016_);
lean_dec_ref_known(v_as_2009_, 2);
v___x_2017_ = lean_box(v_builtin_2008_);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
lean_inc(v_declName_2007_);
lean_inc(v_catName_2006_);
v___x_2018_ = lean_apply_6(v_head_2015_, v_catName_2006_, v_declName_2007_, v___x_2017_, v___y_2010_, v___y_2011_, lean_box(0));
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_dec_ref_known(v___x_2018_, 1);
v_as_2009_ = v_tail_2016_;
goto _start;
}
else
{
lean_dec(v_tail_2016_);
lean_dec(v_declName_2007_);
lean_dec(v_catName_2006_);
return v___x_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0___boxed(lean_object* v_catName_2020_, lean_object* v_declName_2021_, lean_object* v_builtin_2022_, lean_object* v_as_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
uint8_t v_builtin_boxed_2027_; lean_object* v_res_2028_; 
v_builtin_boxed_2027_ = lean_unbox(v_builtin_2022_);
v_res_2028_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2020_, v_declName_2021_, v_builtin_boxed_2027_, v_as_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object* v_catName_2029_, lean_object* v_declName_2030_, uint8_t v_builtin_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = l_Lean_Parser_parserAttributeHooks;
v___x_2036_ = lean_st_ref_get(v___x_2035_);
v___x_2037_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2029_, v_declName_2030_, v_builtin_2031_, v___x_2036_, v_a_2032_, v_a_2033_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object* v_catName_2038_, lean_object* v_declName_2039_, lean_object* v_builtin_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
uint8_t v_builtin_boxed_2044_; lean_object* v_res_2045_; 
v_builtin_boxed_2044_ = lean_unbox(v_builtin_2040_);
v_res_2045_ = l_Lean_Parser_runParserAttributeHooks(v_catName_2038_, v_declName_2039_, v_builtin_boxed_2044_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2046_, lean_object* v_decl_2047_, lean_object* v_stx_2048_, uint8_t v_x_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2048_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2053_) == 0)
{
uint8_t v___x_2054_; lean_object* v___x_2055_; 
lean_dec_ref_known(v___x_2053_, 1);
v___x_2054_ = 1;
v___x_2055_ = l_Lean_Parser_runParserAttributeHooks(v___x_2046_, v_decl_2047_, v___x_2054_, v___y_2050_, v___y_2051_);
return v___x_2055_;
}
else
{
lean_dec(v_decl_2047_);
lean_dec(v___x_2046_);
return v___x_2053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2056_, lean_object* v_decl_2057_, lean_object* v_stx_2058_, lean_object* v_x_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
uint8_t v_x_1104__boxed_2063_; lean_object* v_res_2064_; 
v_x_1104__boxed_2063_ = lean_unbox(v_x_2059_);
v_res_2064_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2056_, v_decl_2057_, v_stx_2058_, v_x_1104__boxed_2063_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
return v_res_2064_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2067_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2068_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2069_ = lean_unsigned_to_nat(0u);
v___x_2070_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
lean_ctor_set(v___x_2070_, 2, v___x_2069_);
lean_ctor_set(v___x_2070_, 3, v___x_2069_);
lean_ctor_set(v___x_2070_, 4, v___x_2068_);
lean_ctor_set(v___x_2070_, 5, v___x_2068_);
lean_ctor_set(v___x_2070_, 6, v___x_2068_);
lean_ctor_set(v___x_2070_, 7, v___x_2068_);
lean_ctor_set(v___x_2070_, 8, v___x_2068_);
lean_ctor_set(v___x_2070_, 9, v___x_2068_);
lean_ctor_set(v___x_2070_, 10, v___x_2068_);
lean_ctor_set(v___x_2070_, 11, v___x_2067_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = lean_unsigned_to_nat(32u);
v___x_2072_ = lean_mk_empty_array_with_capacity(v___x_2071_);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2074_ = ((size_t)5ULL);
v___x_2075_ = lean_unsigned_to_nat(0u);
v___x_2076_ = lean_unsigned_to_nat(32u);
v___x_2077_ = lean_mk_empty_array_with_capacity(v___x_2076_);
v___x_2078_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_2079_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v___x_2077_);
lean_ctor_set(v___x_2079_, 2, v___x_2075_);
lean_ctor_set(v___x_2079_, 3, v___x_2075_);
lean_ctor_set_usize(v___x_2079_, 4, v___x_2074_);
return v___x_2079_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2080_ = lean_box(1);
v___x_2081_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2082_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___x_2081_);
lean_ctor_set(v___x_2083_, 2, v___x_2080_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; lean_object* v_toCold_2089_; lean_object* v_env_2090_; lean_object* v_options_2091_; uint8_t v___x_2092_; lean_object* v_env_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2088_ = lean_st_ref_get(v___y_2086_);
v_toCold_2089_ = lean_ctor_get(v___y_2085_, 0);
v_env_2090_ = lean_ctor_get(v___x_2088_, 0);
lean_inc_ref(v_env_2090_);
lean_dec(v___x_2088_);
v_options_2091_ = lean_ctor_get(v_toCold_2089_, 2);
v___x_2092_ = 0;
v_env_2093_ = l_Lean_Environment_setRecordingDeps(v_env_2090_, v___x_2092_);
v___x_2094_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2095_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_2091_);
v___x_2096_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2096_, 0, v_env_2093_);
lean_ctor_set(v___x_2096_, 1, v___x_2094_);
lean_ctor_set(v___x_2096_, 2, v___x_2095_);
lean_ctor_set(v___x_2096_, 3, v_options_2091_);
v___x_2097_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v_msgData_2084_);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_ref_2108_; lean_object* v___x_2109_; lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2118_; 
v_ref_2108_ = lean_ctor_get(v___y_2105_, 2);
v___x_2109_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msg_2104_, v___y_2105_, v___y_2106_);
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
lean_inc(v_ref_2108_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v_ref_2108_);
lean_ctor_set(v___x_2114_, 1, v_a_2110_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 1);
lean_ctor_set(v___x_2112_, 0, v___x_2114_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
return v_res_2123_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2126_ = l_Lean_stringToMessageData(v___x_2125_);
return v___x_2126_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2129_ = l_Lean_stringToMessageData(v___x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2130_, lean_object* v_decl_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2135_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2136_ = l_Lean_MessageData_ofName(v___x_2130_);
v___x_2137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2135_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2139_, v___y_2132_, v___y_2133_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2141_, lean_object* v_decl_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2141_, v_decl_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v_decl_2142_);
return v_res_2146_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = lean_unsigned_to_nat(3646333153u);
v___x_2190_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2191_ = l_Lean_Name_num___override(v___x_2190_, v___x_2189_);
return v___x_2191_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2194_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2195_ = l_Lean_Name_str___override(v___x_2194_, v___x_2193_);
return v___x_2195_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2198_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2199_ = l_Lean_Name_str___override(v___x_2198_, v___x_2197_);
return v___x_2199_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = lean_unsigned_to_nat(2u);
v___x_2201_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2202_ = l_Lean_Name_num___override(v___x_2201_, v___x_2200_);
return v___x_2202_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2209_ = 0;
v___x_2210_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2211_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2212_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2213_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v___x_2211_);
lean_ctor_set(v___x_2213_, 2, v___x_2210_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*3, v___x_2209_);
return v___x_2213_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2214_; lean_object* v___f_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___f_2214_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___f_2215_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2216_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v___f_2215_);
lean_ctor_set(v___x_2217_, 2, v___f_2214_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2220_ = l_Lean_registerBuiltinAttribute(v___x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2223_, lean_object* v_msg_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2224_, v___y_2225_, v___y_2226_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2229_, lean_object* v_msg_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(v_00_u03b1_2229_, v_msg_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2235_, lean_object* v_decl_2236_, lean_object* v_stx_2237_, uint8_t v_x_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2237_, v___y_2239_, v___y_2240_);
if (lean_obj_tag(v___x_2242_) == 0)
{
uint8_t v___x_2243_; lean_object* v___x_2244_; 
lean_dec_ref_known(v___x_2242_, 1);
v___x_2243_ = 0;
v___x_2244_ = l_Lean_Parser_runParserAttributeHooks(v___x_2235_, v_decl_2236_, v___x_2243_, v___y_2239_, v___y_2240_);
return v___x_2244_;
}
else
{
lean_dec(v_decl_2236_);
lean_dec(v___x_2235_);
return v___x_2242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2245_, lean_object* v_decl_2246_, lean_object* v_stx_2247_, lean_object* v_x_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
uint8_t v_x_212__boxed_2252_; lean_object* v_res_2253_; 
v_x_212__boxed_2252_ = lean_unbox(v_x_2248_);
v_res_2253_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2245_, v_decl_2246_, v_stx_2247_, v_x_212__boxed_2252_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2253_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = lean_unsigned_to_nat(3789407938u);
v___x_2257_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2258_ = l_Lean_Name_num___override(v___x_2257_, v___x_2256_);
return v___x_2258_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2259_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2260_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2261_ = l_Lean_Name_str___override(v___x_2260_, v___x_2259_);
return v___x_2261_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2263_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2264_ = l_Lean_Name_str___override(v___x_2263_, v___x_2262_);
return v___x_2264_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2265_ = lean_unsigned_to_nat(2u);
v___x_2266_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2267_ = l_Lean_Name_num___override(v___x_2266_, v___x_2265_);
return v___x_2267_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2274_ = 0;
v___x_2275_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2276_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2277_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2278_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v___x_2276_);
lean_ctor_set(v___x_2278_, 2, v___x_2275_);
lean_ctor_set_uint8(v___x_2278_, sizeof(void*)*3, v___x_2274_);
return v___x_2278_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2279_; lean_object* v___f_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___f_2279_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___f_2280_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2281_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v___f_2280_);
lean_ctor_set(v___x_2282_, 2, v___f_2279_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2285_ = l_Lean_registerBuiltinAttribute(v___x_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v_a_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object* v_s_2288_, lean_object* v_x_2289_, lean_object* v_a_2290_){
_start:
{
switch(lean_obj_tag(v_x_2289_))
{
case 0:
{
lean_object* v_val_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2300_; 
lean_dec_ref(v_s_2288_);
v_val_2292_ = lean_ctor_get(v_x_2289_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_x_2289_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2294_ = v_x_2289_;
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_val_2292_);
lean_dec(v_x_2289_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_val_2292_);
v___x_2297_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
}
}
case 1:
{
lean_object* v_val_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2309_; 
lean_dec_ref(v_s_2288_);
v_val_2301_ = lean_ctor_get(v_x_2289_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_x_2289_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2303_ = v_x_2289_;
v_isShared_2304_ = v_isSharedCheck_2309_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_val_2301_);
lean_dec(v_x_2289_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2309_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_val_2301_);
v___x_2306_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
}
case 2:
{
lean_object* v_catName_2310_; lean_object* v_declName_2311_; uint8_t v_behavior_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v_s_2288_);
v_catName_2310_ = lean_ctor_get(v_x_2289_, 0);
v_declName_2311_ = lean_ctor_get(v_x_2289_, 1);
v_behavior_2312_ = lean_ctor_get_uint8(v_x_2289_, sizeof(void*)*2);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_x_2289_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2314_ = v_x_2289_;
v_isShared_2315_ = v_isSharedCheck_2320_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_declName_2311_);
lean_inc(v_catName_2310_);
lean_dec(v_x_2289_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2320_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_catName_2310_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_declName_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2319_, sizeof(void*)*2, v_behavior_2312_);
v___x_2317_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
}
}
default: 
{
lean_object* v_catName_2321_; lean_object* v_declName_2322_; lean_object* v_prio_2323_; lean_object* v_categories_2324_; lean_object* v___x_2325_; 
v_catName_2321_ = lean_ctor_get(v_x_2289_, 0);
lean_inc(v_catName_2321_);
v_declName_2322_ = lean_ctor_get(v_x_2289_, 1);
lean_inc_n(v_declName_2322_, 2);
v_prio_2323_ = lean_ctor_get(v_x_2289_, 2);
lean_inc(v_prio_2323_);
lean_dec_ref_known(v_x_2289_, 3);
v_categories_2324_ = lean_ctor_get(v_s_2288_, 2);
lean_inc_ref(v_categories_2324_);
lean_dec_ref(v_s_2288_);
v___x_2325_ = l_Lean_Parser_mkParserOfConstant(v_categories_2324_, v_declName_2322_, v_a_2290_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2337_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2337_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2337_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_fst_2330_; lean_object* v_snd_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2335_; 
v_fst_2330_ = lean_ctor_get(v_a_2326_, 0);
lean_inc(v_fst_2330_);
v_snd_2331_ = lean_ctor_get(v_a_2326_, 1);
lean_inc(v_snd_2331_);
lean_dec(v_a_2326_);
v___x_2332_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_2332_, 0, v_catName_2321_);
lean_ctor_set(v___x_2332_, 1, v_declName_2322_);
lean_ctor_set(v___x_2332_, 2, v_snd_2331_);
lean_ctor_set(v___x_2332_, 3, v_prio_2323_);
v___x_2333_ = lean_unbox(v_fst_2330_);
lean_dec(v_fst_2330_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*4, v___x_2333_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2332_);
v___x_2335_ = v___x_2328_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2332_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_prio_2323_);
lean_dec(v_declName_2322_);
lean_dec(v_catName_2321_);
v_a_2338_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2325_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2325_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object* v_s_2346_, lean_object* v_x_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(v_s_2346_, v_x_2347_, v_a_2348_);
lean_dec_ref(v_a_2348_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v_x_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v_a_2352_);
lean_inc_ref_n(v___x_2353_, 2);
v___x_2354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
lean_ctor_set(v___x_2354_, 2, v___x_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_x_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v_x_2355_, v_a_2356_);
lean_dec_ref(v_x_2355_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v___y_2358_){
_start:
{
lean_inc_ref(v___y_2358_);
return v___y_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v___y_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v___y_2359_);
lean_dec_ref(v___y_2359_);
return v_res_2360_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2371_; uint8_t v___x_2372_; lean_object* v___f_2373_; lean_object* v___f_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2371_ = lean_box(0);
v___x_2372_ = 0;
v___f_2373_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___f_2374_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2375_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2376_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2377_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2378_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed), 1, 0);
v___x_2379_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2380_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v___x_2378_);
lean_ctor_set(v___x_2380_, 2, v___x_2377_);
lean_ctor_set(v___x_2380_, 3, v___x_2376_);
lean_ctor_set(v___x_2380_, 4, v___x_2375_);
lean_ctor_set(v___x_2380_, 5, v___f_2374_);
lean_ctor_set(v___x_2380_, 6, v___f_2373_);
lean_ctor_set(v___x_2380_, 7, v___x_2371_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*8, v___x_2372_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*8 + 1, v___x_2372_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_);
v___x_2383_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_a_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object* v_env_2386_, lean_object* v_catName_2387_){
_start:
{
lean_object* v___x_2388_; lean_object* v_ext_2389_; lean_object* v_toEnvExtension_2390_; lean_object* v_asyncMode_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v_categories_2395_; lean_object* v___x_2396_; 
v___x_2388_ = l_Lean_Parser_parserExtension;
v_ext_2389_ = lean_ctor_get(v___x_2388_, 1);
v_toEnvExtension_2390_ = lean_ctor_get(v_ext_2389_, 0);
v_asyncMode_2391_ = lean_ctor_get(v_toEnvExtension_2390_, 2);
v___x_2392_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2393_ = 0;
v___x_2394_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2392_, v___x_2388_, v_env_2386_, v_asyncMode_2391_, v___x_2393_);
v_categories_2395_ = lean_ctor_get(v___x_2394_, 2);
lean_inc_ref(v_categories_2395_);
lean_dec(v___x_2394_);
v___x_2396_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2395_, v_catName_2387_);
lean_dec_ref(v_categories_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object* v_env_2397_, lean_object* v_catName_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_Parser_getParserCategory_x3f(v_env_2397_, v_catName_2398_);
lean_dec(v_catName_2398_);
return v_res_2399_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isParserCategory(lean_object* v_env_2400_, lean_object* v_catName_2401_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_Parser_getParserCategory_x3f(v_env_2400_, v_catName_2401_);
if (lean_obj_tag(v___x_2402_) == 0)
{
uint8_t v___x_2403_; 
v___x_2403_ = 0;
return v___x_2403_;
}
else
{
uint8_t v___x_2404_; 
lean_dec_ref_known(v___x_2402_, 1);
v___x_2404_ = 1;
return v___x_2404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object* v_env_2405_, lean_object* v_catName_2406_){
_start:
{
uint8_t v_res_2407_; lean_object* v_r_2408_; 
v_res_2407_ = l_Lean_Parser_isParserCategory(v_env_2405_, v_catName_2406_);
lean_dec(v_catName_2406_);
v_r_2408_ = lean_box(v_res_2407_);
return v_r_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKindCategories___lam__0(lean_object* v_kind_2409_, lean_object* v_x_2410_, lean_object* v_____s_2411_){
_start:
{
lean_object* v_snd_2412_; lean_object* v_fst_2413_; lean_object* v_kinds_2414_; uint8_t v___x_2415_; 
v_snd_2412_ = lean_ctor_get(v_x_2410_, 1);
lean_inc(v_snd_2412_);
v_fst_2413_ = lean_ctor_get(v_x_2410_, 0);
lean_inc(v_fst_2413_);
lean_dec_ref(v_x_2410_);
v_kinds_2414_ = lean_ctor_get(v_snd_2412_, 1);
lean_inc_ref(v_kinds_2414_);
lean_dec(v_snd_2412_);
v___x_2415_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_2414_, v_kind_2409_);
lean_dec_ref(v_kinds_2414_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; 
lean_dec(v_fst_2413_);
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_____s_2411_);
return v___x_2416_;
}
else
{
lean_object* v_cats_2417_; lean_object* v___x_2418_; 
v_cats_2417_ = lean_array_push(v_____s_2411_, v_fst_2413_);
v___x_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2418_, 0, v_cats_2417_);
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKindCategories___lam__0___boxed(lean_object* v_kind_2419_, lean_object* v_x_2420_, lean_object* v_____s_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Parser_getSyntaxNodeKindCategories___lam__0(v_kind_2419_, v_x_2420_, v_____s_2421_);
lean_dec(v_kind_2419_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_2423_, lean_object* v_keys_2424_, lean_object* v_vals_2425_, lean_object* v_i_2426_, lean_object* v_acc_2427_){
_start:
{
lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2428_ = lean_array_get_size(v_keys_2424_);
v___x_2429_ = lean_nat_dec_lt(v_i_2426_, v___x_2428_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; 
lean_dec(v_i_2426_);
lean_dec_ref(v_f_2423_);
v___x_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_acc_2427_);
return v___x_2430_;
}
else
{
lean_object* v_k_2431_; lean_object* v_v_2432_; lean_object* v___x_2433_; 
v_k_2431_ = lean_array_fget_borrowed(v_keys_2424_, v_i_2426_);
v_v_2432_ = lean_array_fget_borrowed(v_vals_2425_, v_i_2426_);
lean_inc_ref(v_f_2423_);
lean_inc(v_v_2432_);
lean_inc(v_k_2431_);
v___x_2433_ = lean_apply_3(v_f_2423_, v_acc_2427_, v_k_2431_, v_v_2432_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_dec(v_i_2426_);
lean_dec_ref(v_f_2423_);
return v___x_2433_;
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2433_, 1);
v___x_2435_ = lean_unsigned_to_nat(1u);
v___x_2436_ = lean_nat_add(v_i_2426_, v___x_2435_);
lean_dec(v_i_2426_);
v_i_2426_ = v___x_2436_;
v_acc_2427_ = v_a_2434_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_2438_, lean_object* v_keys_2439_, lean_object* v_vals_2440_, lean_object* v_i_2441_, lean_object* v_acc_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2438_, v_keys_2439_, v_vals_2440_, v_i_2441_, v_acc_2442_);
lean_dec_ref(v_vals_2440_);
lean_dec_ref(v_keys_2439_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2444_, lean_object* v_as_2445_, size_t v_i_2446_, size_t v_stop_2447_, lean_object* v_b_2448_){
_start:
{
lean_object* v_a_2450_; lean_object* v___y_2455_; uint8_t v___x_2457_; 
v___x_2457_ = lean_usize_dec_eq(v_i_2446_, v_stop_2447_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_array_uget_borrowed(v_as_2445_, v_i_2446_);
switch(lean_obj_tag(v___x_2458_))
{
case 0:
{
lean_object* v_key_2459_; lean_object* v_val_2460_; lean_object* v___x_2461_; 
v_key_2459_ = lean_ctor_get(v___x_2458_, 0);
v_val_2460_ = lean_ctor_get(v___x_2458_, 1);
lean_inc_ref(v_f_2444_);
lean_inc(v_val_2460_);
lean_inc(v_key_2459_);
v___x_2461_ = lean_apply_3(v_f_2444_, v_b_2448_, v_key_2459_, v_val_2460_);
v___y_2455_ = v___x_2461_;
goto v___jp_2454_;
}
case 1:
{
lean_object* v_node_2462_; lean_object* v___x_2463_; 
v_node_2462_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_node_2462_);
lean_inc_ref(v_f_2444_);
v___x_2463_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(v_f_2444_, v_node_2462_, v_b_2448_);
v___y_2455_ = v___x_2463_;
goto v___jp_2454_;
}
default: 
{
v_a_2450_ = v_b_2448_;
goto v___jp_2449_;
}
}
}
else
{
lean_object* v___x_2464_; 
lean_dec_ref(v_f_2444_);
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v_b_2448_);
return v___x_2464_;
}
v___jp_2449_:
{
size_t v___x_2451_; size_t v___x_2452_; 
v___x_2451_ = ((size_t)1ULL);
v___x_2452_ = lean_usize_add(v_i_2446_, v___x_2451_);
v_i_2446_ = v___x_2452_;
v_b_2448_ = v_a_2450_;
goto _start;
}
v___jp_2454_:
{
if (lean_obj_tag(v___y_2455_) == 0)
{
lean_dec_ref(v_f_2444_);
return v___y_2455_;
}
else
{
lean_object* v_a_2456_; 
v_a_2456_ = lean_ctor_get(v___y_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___y_2455_, 1);
v_a_2450_ = v_a_2456_;
goto v___jp_2449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2465_, lean_object* v_x_2466_, lean_object* v_x_2467_){
_start:
{
if (lean_obj_tag(v_x_2466_) == 0)
{
lean_object* v_es_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2481_; 
v_es_2468_ = lean_ctor_get(v_x_2466_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_x_2466_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2470_ = v_x_2466_;
v_isShared_2471_ = v_isSharedCheck_2481_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_es_2468_);
lean_dec(v_x_2466_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2481_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2472_ = lean_unsigned_to_nat(0u);
v___x_2473_ = lean_array_get_size(v_es_2468_);
v___x_2474_ = lean_nat_dec_lt(v___x_2472_, v___x_2473_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2476_; 
lean_dec_ref(v_es_2468_);
lean_dec_ref(v_f_2465_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set_tag(v___x_2470_, 1);
lean_ctor_set(v___x_2470_, 0, v_x_2467_);
v___x_2476_ = v___x_2470_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_x_2467_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
else
{
size_t v___x_2478_; size_t v___x_2479_; lean_object* v___x_2480_; 
lean_del_object(v___x_2470_);
v___x_2478_ = ((size_t)0ULL);
v___x_2479_ = lean_usize_of_nat(v___x_2473_);
v___x_2480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2465_, v_es_2468_, v___x_2478_, v___x_2479_, v_x_2467_);
lean_dec_ref(v_es_2468_);
return v___x_2480_;
}
}
}
else
{
lean_object* v_ks_2482_; lean_object* v_vs_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v_ks_2482_ = lean_ctor_get(v_x_2466_, 0);
lean_inc_ref(v_ks_2482_);
v_vs_2483_ = lean_ctor_get(v_x_2466_, 1);
lean_inc_ref(v_vs_2483_);
lean_dec_ref_known(v_x_2466_, 2);
v___x_2484_ = lean_unsigned_to_nat(0u);
v___x_2485_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2465_, v_ks_2482_, v_vs_2483_, v___x_2484_, v_x_2467_);
lean_dec_ref(v_vs_2483_);
lean_dec_ref(v_ks_2482_);
return v___x_2485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_2486_, lean_object* v_as_2487_, lean_object* v_i_2488_, lean_object* v_stop_2489_, lean_object* v_b_2490_){
_start:
{
size_t v_i_boxed_2491_; size_t v_stop_boxed_2492_; lean_object* v_res_2493_; 
v_i_boxed_2491_ = lean_unbox_usize(v_i_2488_);
lean_dec(v_i_2488_);
v_stop_boxed_2492_ = lean_unbox_usize(v_stop_2489_);
lean_dec(v_stop_2489_);
v_res_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2486_, v_as_2487_, v_i_boxed_2491_, v_stop_boxed_2492_, v_b_2490_);
lean_dec_ref(v_as_2487_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg___lam__0(lean_object* v_f_2494_, lean_object* v_s_2495_, lean_object* v_a_2496_, lean_object* v_b_2497_){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v_a_2496_);
lean_ctor_set(v___x_2498_, 1, v_b_2497_);
v___x_2499_ = lean_apply_2(v_f_2494_, v___x_2498_, v_s_2495_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
v_a_2508_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2499_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2499_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg(lean_object* v_map_2516_, lean_object* v_init_2517_, lean_object* v_f_2518_){
_start:
{
lean_object* v___f_2519_; lean_object* v___x_2520_; lean_object* v_a_2521_; 
v___f_2519_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2519_, 0, v_f_2518_);
lean_inc_ref(v_map_2516_);
v___x_2520_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(v___f_2519_, v_map_2516_, v_init_2517_);
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref(v___x_2520_);
return v_a_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg___boxed(lean_object* v_map_2522_, lean_object* v_init_2523_, lean_object* v_f_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg(v_map_2522_, v_init_2523_, v_f_2524_);
lean_dec_ref(v_map_2522_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKindCategories(lean_object* v_env_2528_, lean_object* v_kind_2529_){
_start:
{
lean_object* v___x_2530_; lean_object* v_ext_2531_; lean_object* v_toEnvExtension_2532_; lean_object* v_asyncMode_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; lean_object* v___x_2536_; lean_object* v_categories_2537_; lean_object* v___f_2538_; lean_object* v_cats_2539_; lean_object* v___x_2540_; 
v___x_2530_ = l_Lean_Parser_parserExtension;
v_ext_2531_ = lean_ctor_get(v___x_2530_, 1);
v_toEnvExtension_2532_ = lean_ctor_get(v_ext_2531_, 0);
v_asyncMode_2533_ = lean_ctor_get(v_toEnvExtension_2532_, 2);
v___x_2534_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2535_ = 0;
v___x_2536_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2534_, v___x_2530_, v_env_2528_, v_asyncMode_2533_, v___x_2535_);
v_categories_2537_ = lean_ctor_get(v___x_2536_, 2);
lean_inc_ref(v_categories_2537_);
lean_dec(v___x_2536_);
v___f_2538_ = lean_alloc_closure((void*)(l_Lean_Parser_getSyntaxNodeKindCategories___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2538_, 0, v_kind_2529_);
v_cats_2539_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKindCategories___closed__0));
v___x_2540_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg(v_categories_2537_, v_cats_2539_, v___f_2538_);
lean_dec_ref(v_categories_2537_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0(lean_object* v_00_u03c3_2541_, lean_object* v_00_u03b2_2542_, lean_object* v_map_2543_, lean_object* v_init_2544_, lean_object* v_f_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___redArg(v_map_2543_, v_init_2544_, v_f_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0___boxed(lean_object* v_00_u03c3_2547_, lean_object* v_00_u03b2_2548_, lean_object* v_map_2549_, lean_object* v_init_2550_, lean_object* v_f_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0(v_00_u03c3_2547_, v_00_u03b2_2548_, v_map_2549_, v_init_2550_, v_f_2551_);
lean_dec_ref(v_map_2549_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0___redArg(lean_object* v_map_2553_, lean_object* v_f_2554_, lean_object* v_init_2555_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(v_f_2554_, v_map_2553_, v_init_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0(lean_object* v_00_u03c3_2557_, lean_object* v_00_u03c3_2558_, lean_object* v_00_u03b2_2559_, lean_object* v_map_2560_, lean_object* v_f_2561_, lean_object* v_init_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(v_f_2561_, v_map_2560_, v_init_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2564_, lean_object* v_00_u03c3_2565_, lean_object* v_00_u03b1_2566_, lean_object* v_00_u03b2_2567_, lean_object* v_f_2568_, lean_object* v_x_2569_, lean_object* v_x_2570_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1___redArg(v_f_2568_, v_x_2569_, v_x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2572_, lean_object* v_00_u03b2_2573_, lean_object* v_00_u03c3_2574_, lean_object* v_00_u03c3_2575_, lean_object* v_f_2576_, lean_object* v_as_2577_, size_t v_i_2578_, size_t v_stop_2579_, lean_object* v_b_2580_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___redArg(v_f_2576_, v_as_2577_, v_i_2578_, v_stop_2579_, v_b_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2582_, lean_object* v_00_u03b2_2583_, lean_object* v_00_u03c3_2584_, lean_object* v_00_u03c3_2585_, lean_object* v_f_2586_, lean_object* v_as_2587_, lean_object* v_i_2588_, lean_object* v_stop_2589_, lean_object* v_b_2590_){
_start:
{
size_t v_i_boxed_2591_; size_t v_stop_boxed_2592_; lean_object* v_res_2593_; 
v_i_boxed_2591_ = lean_unbox_usize(v_i_2588_);
lean_dec(v_i_2588_);
v_stop_boxed_2592_ = lean_unbox_usize(v_stop_2589_);
lean_dec(v_stop_2589_);
v_res_2593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2582_, v_00_u03b2_2583_, v_00_u03c3_2584_, v_00_u03c3_2585_, v_f_2586_, v_as_2587_, v_i_boxed_2591_, v_stop_boxed_2592_, v_b_2590_);
lean_dec_ref(v_as_2587_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_2594_, lean_object* v_00_u03c3_2595_, lean_object* v_00_u03b1_2596_, lean_object* v_00_u03b2_2597_, lean_object* v_f_2598_, lean_object* v_keys_2599_, lean_object* v_vals_2600_, lean_object* v_heq_2601_, lean_object* v_i_2602_, lean_object* v_acc_2603_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___redArg(v_f_2598_, v_keys_2599_, v_vals_2600_, v_i_2602_, v_acc_2603_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_2605_, lean_object* v_00_u03c3_2606_, lean_object* v_00_u03b1_2607_, lean_object* v_00_u03b2_2608_, lean_object* v_f_2609_, lean_object* v_keys_2610_, lean_object* v_vals_2611_, lean_object* v_heq_2612_, lean_object* v_i_2613_, lean_object* v_acc_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Parser_getSyntaxNodeKindCategories_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_2605_, v_00_u03c3_2606_, v_00_u03b1_2607_, v_00_u03b2_2608_, v_f_2609_, v_keys_2610_, v_vals_2611_, v_heq_2612_, v_i_2613_, v_acc_2614_);
lean_dec_ref(v_vals_2611_);
lean_dec_ref(v_keys_2610_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object* v_env_2616_, lean_object* v_catName_2617_, lean_object* v_declName_2618_, uint8_t v_behavior_2619_){
_start:
{
uint8_t v___x_2620_; 
lean_inc_ref(v_env_2616_);
v___x_2620_ = l_Lean_Parser_isParserCategory(v_env_2616_, v_catName_2617_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2621_ = l_Lean_Parser_parserExtension;
v___x_2622_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2622_, 0, v_catName_2617_);
lean_ctor_set(v___x_2622_, 1, v_declName_2618_);
lean_ctor_set_uint8(v___x_2622_, sizeof(void*)*2, v_behavior_2619_);
v___x_2623_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2621_, v_env_2616_, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
return v___x_2624_;
}
else
{
lean_object* v___x_2625_; 
lean_dec(v_declName_2618_);
lean_dec_ref(v_env_2616_);
v___x_2625_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_2617_);
return v___x_2625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* v_env_2626_, lean_object* v_catName_2627_, lean_object* v_declName_2628_, lean_object* v_behavior_2629_){
_start:
{
uint8_t v_behavior_boxed_2630_; lean_object* v_res_2631_; 
v_behavior_boxed_2630_ = lean_unbox(v_behavior_2629_);
v_res_2631_ = l_Lean_Parser_addParserCategory(v_env_2626_, v_catName_2627_, v_declName_2628_, v_behavior_boxed_2630_);
return v_res_2631_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object* v_env_2632_, lean_object* v_catName_2633_){
_start:
{
lean_object* v___x_2634_; lean_object* v_ext_2635_; lean_object* v_toEnvExtension_2636_; lean_object* v_asyncMode_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v_categories_2641_; lean_object* v___x_2642_; 
v___x_2634_ = l_Lean_Parser_parserExtension;
v_ext_2635_ = lean_ctor_get(v___x_2634_, 1);
v_toEnvExtension_2636_ = lean_ctor_get(v_ext_2635_, 0);
v_asyncMode_2637_ = lean_ctor_get(v_toEnvExtension_2636_, 2);
v___x_2638_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2639_ = 0;
v___x_2640_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2638_, v___x_2634_, v_env_2632_, v_asyncMode_2637_, v___x_2639_);
v_categories_2641_ = lean_ctor_get(v___x_2640_, 2);
lean_inc_ref(v_categories_2641_);
lean_dec(v___x_2640_);
v___x_2642_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2641_, v_catName_2633_);
lean_dec_ref(v_categories_2641_);
if (lean_obj_tag(v___x_2642_) == 0)
{
uint8_t v___x_2643_; 
v___x_2643_ = 0;
return v___x_2643_;
}
else
{
lean_object* v_val_2644_; uint8_t v_behavior_2645_; 
v_val_2644_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_val_2644_);
lean_dec_ref_known(v___x_2642_, 1);
v_behavior_2645_ = lean_ctor_get_uint8(v_val_2644_, sizeof(void*)*3);
lean_dec(v_val_2644_);
return v_behavior_2645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object* v_env_2646_, lean_object* v_catName_2647_){
_start:
{
uint8_t v_res_2648_; lean_object* v_r_2649_; 
v_res_2648_ = l_Lean_Parser_leadingIdentBehavior(v_env_2646_, v_catName_2647_);
lean_dec(v_catName_2647_);
v_r_2649_ = lean_box(v_res_2648_);
return v_r_2649_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(lean_object* v_x_2650_, lean_object* v_x_2651_){
_start:
{
if (lean_obj_tag(v_x_2651_) == 0)
{
return v_x_2650_;
}
else
{
lean_object* v_head_2652_; lean_object* v_tail_2653_; lean_object* v___x_2654_; 
v_head_2652_ = lean_ctor_get(v_x_2651_, 0);
lean_inc_n(v_head_2652_, 2);
v_tail_2653_ = lean_ctor_get(v_x_2651_, 1);
lean_inc(v_tail_2653_);
lean_dec_ref_known(v_x_2651_, 2);
v___x_2654_ = l_Lean_Data_Trie_insert___redArg(v_x_2650_, v_head_2652_, v_head_2652_);
lean_dec(v_head_2652_);
v_x_2650_ = v___x_2654_;
v_x_2651_ = v_tail_2653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__0(lean_object* v_info_2656_, lean_object* v_ctx_2657_){
_start:
{
lean_object* v_toInputContext_2658_; lean_object* v_toParserModuleContext_2659_; lean_object* v_toCacheableParserContext_2660_; lean_object* v_tokens_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2672_; 
v_toInputContext_2658_ = lean_ctor_get(v_ctx_2657_, 0);
v_toParserModuleContext_2659_ = lean_ctor_get(v_ctx_2657_, 1);
v_toCacheableParserContext_2660_ = lean_ctor_get(v_ctx_2657_, 2);
v_tokens_2661_ = lean_ctor_get(v_ctx_2657_, 3);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_ctx_2657_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2663_ = v_ctx_2657_;
v_isShared_2664_ = v_isSharedCheck_2672_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_tokens_2661_);
lean_inc(v_toCacheableParserContext_2660_);
lean_inc(v_toParserModuleContext_2659_);
lean_inc(v_toInputContext_2658_);
lean_dec(v_ctx_2657_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2672_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v_collectTokens_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
v_collectTokens_2665_ = lean_ctor_get(v_info_2656_, 0);
lean_inc_ref(v_collectTokens_2665_);
lean_dec_ref(v_info_2656_);
v___x_2666_ = lean_box(0);
v___x_2667_ = lean_apply_1(v_collectTokens_2665_, v___x_2666_);
v___x_2668_ = l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(v_tokens_2661_, v___x_2667_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 3, v___x_2668_);
v___x_2670_ = v___x_2663_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_toInputContext_2658_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_toParserModuleContext_2659_);
lean_ctor_set(v_reuseFailAlloc_2671_, 2, v_toCacheableParserContext_2660_);
lean_ctor_set(v_reuseFailAlloc_2671_, 3, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1(lean_object* v_categories_2673_, lean_object* v_declName_2674_, lean_object* v___x_2675_, lean_object* v_ctx_2676_, lean_object* v_s_2677_, lean_object* v_evalFallback_x3f_2678_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_Parser_mkParserOfConstant(v_categories_2673_, v_declName_2674_, v___x_2675_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v_snd_2682_; lean_object* v_info_2683_; lean_object* v_fn_2684_; lean_object* v___f_2685_; lean_object* v___x_2686_; 
lean_dec(v_evalFallback_x3f_2678_);
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v_snd_2682_ = lean_ctor_get(v_a_2681_, 1);
lean_inc(v_snd_2682_);
lean_dec(v_a_2681_);
v_info_2683_ = lean_ctor_get(v_snd_2682_, 0);
lean_inc_ref(v_info_2683_);
v_fn_2684_ = lean_ctor_get(v_snd_2682_, 1);
lean_inc_ref(v_fn_2684_);
lean_dec(v_snd_2682_);
v___f_2685_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__0), 2, 1);
lean_closure_set(v___f_2685_, 0, v_info_2683_);
v___x_2686_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2685_, v_fn_2684_, v_ctx_2676_, v_s_2677_);
return v___x_2686_;
}
else
{
if (lean_obj_tag(v_evalFallback_x3f_2678_) == 1)
{
lean_object* v_val_2687_; lean_object* v___x_2688_; 
lean_dec_ref_known(v___x_2680_, 1);
v_val_2687_ = lean_ctor_get(v_evalFallback_x3f_2678_, 0);
lean_inc(v_val_2687_);
lean_dec_ref_known(v_evalFallback_x3f_2678_, 1);
v___x_2688_ = lean_apply_2(v_val_2687_, v_ctx_2676_, v_s_2677_);
return v___x_2688_;
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; lean_object* v___x_2693_; 
lean_dec(v_evalFallback_x3f_2678_);
lean_dec_ref(v_ctx_2676_);
v_a_2689_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2690_ = lean_io_error_to_string(v_a_2689_);
v___x_2691_ = lean_box(0);
v___x_2692_ = 1;
v___x_2693_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2677_, v___x_2690_, v___x_2691_, v___x_2692_);
return v___x_2693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed(lean_object* v_categories_2694_, lean_object* v_declName_2695_, lean_object* v___x_2696_, lean_object* v_ctx_2697_, lean_object* v_s_2698_, lean_object* v_evalFallback_x3f_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_Parser_evalParserConstUnsafe___lam__1(v_categories_2694_, v_declName_2695_, v___x_2696_, v_ctx_2697_, v_s_2698_, v_evalFallback_x3f_2699_);
lean_dec_ref(v___x_2696_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* v_declName_2702_, lean_object* v_evalFallback_x3f_2703_, lean_object* v_ctx_2704_, lean_object* v_s_2705_){
_start:
{
lean_object* v_toParserModuleContext_2706_; lean_object* v_env_2707_; lean_object* v_options_2708_; lean_object* v___x_2709_; lean_object* v_ext_2710_; lean_object* v_toEnvExtension_2711_; lean_object* v_asyncMode_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v_categories_2716_; lean_object* v___x_2717_; lean_object* v___f_2718_; lean_object* v___x_2719_; 
v_toParserModuleContext_2706_ = lean_ctor_get(v_ctx_2704_, 1);
v_env_2707_ = lean_ctor_get(v_toParserModuleContext_2706_, 0);
v_options_2708_ = lean_ctor_get(v_toParserModuleContext_2706_, 1);
v___x_2709_ = l_Lean_Parser_parserExtension;
v_ext_2710_ = lean_ctor_get(v___x_2709_, 1);
v_toEnvExtension_2711_ = lean_ctor_get(v_ext_2710_, 0);
v_asyncMode_2712_ = lean_ctor_get(v_toEnvExtension_2711_, 2);
v___x_2713_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2714_ = 0;
lean_inc_ref_n(v_env_2707_, 2);
v___x_2715_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2713_, v___x_2709_, v_env_2707_, v_asyncMode_2712_, v___x_2714_);
v_categories_2716_ = lean_ctor_get(v___x_2715_, 2);
lean_inc_ref(v_categories_2716_);
lean_dec(v___x_2715_);
lean_inc_ref(v_options_2708_);
v___x_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2717_, 0, v_env_2707_);
lean_ctor_set(v___x_2717_, 1, v_options_2708_);
v___f_2718_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2718_, 0, v_categories_2716_);
lean_closure_set(v___f_2718_, 1, v_declName_2702_);
lean_closure_set(v___f_2718_, 2, v___x_2717_);
lean_closure_set(v___f_2718_, 3, v_ctx_2704_);
lean_closure_set(v___f_2718_, 4, v_s_2705_);
lean_closure_set(v___f_2718_, 5, v_evalFallback_x3f_2703_);
v___x_2719_ = l_unsafeBaseIO___redArg(v___f_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object* v_name_2720_, lean_object* v_decl_2721_, lean_object* v_ref_2722_){
_start:
{
lean_object* v_defValue_2724_; lean_object* v_descr_2725_; lean_object* v_deprecation_x3f_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_defValue_2724_ = lean_ctor_get(v_decl_2721_, 0);
v_descr_2725_ = lean_ctor_get(v_decl_2721_, 1);
v_deprecation_x3f_2726_ = lean_ctor_get(v_decl_2721_, 2);
v___x_2727_ = lean_alloc_ctor(1, 0, 1);
v___x_2728_ = lean_unbox(v_defValue_2724_);
lean_ctor_set_uint8(v___x_2727_, 0, v___x_2728_);
lean_inc(v_deprecation_x3f_2726_);
lean_inc_ref(v_descr_2725_);
lean_inc_n(v_name_2720_, 2);
v___x_2729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2729_, 0, v_name_2720_);
lean_ctor_set(v___x_2729_, 1, v_ref_2722_);
lean_ctor_set(v___x_2729_, 2, v___x_2727_);
lean_ctor_set(v___x_2729_, 3, v_descr_2725_);
lean_ctor_set(v___x_2729_, 4, v_deprecation_x3f_2726_);
v___x_2730_ = lean_register_option(v_name_2720_, v___x_2729_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2738_; 
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2738_ == 0)
{
lean_object* v_unused_2739_; 
v_unused_2739_ = lean_ctor_get(v___x_2730_, 0);
lean_dec(v_unused_2739_);
v___x_2732_ = v___x_2730_;
v_isShared_2733_ = v_isSharedCheck_2738_;
goto v_resetjp_2731_;
}
else
{
lean_dec(v___x_2730_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2738_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
lean_inc(v_defValue_2724_);
v___x_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2734_, 0, v_name_2720_);
lean_ctor_set(v___x_2734_, 1, v_defValue_2724_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2734_);
v___x_2736_ = v___x_2732_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v_name_2720_);
v_a_2740_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2730_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2730_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2748_, lean_object* v_decl_2749_, lean_object* v_ref_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v_name_2748_, v_decl_2749_, v_ref_2750_);
lean_dec_ref(v_decl_2749_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2770_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2771_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2772_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2773_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v___x_2770_, v___x_2771_, v___x_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object* v_a_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(lean_object* v_o_2779_, lean_object* v_k_2780_, uint8_t v_v_2781_){
_start:
{
lean_object* v_map_2782_; uint8_t v_hasTrace_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2797_; 
v_map_2782_ = lean_ctor_get(v_o_2779_, 0);
v_hasTrace_2783_ = lean_ctor_get_uint8(v_o_2779_, sizeof(void*)*1);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_o_2779_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2785_ = v_o_2779_;
v_isShared_2786_ = v_isSharedCheck_2797_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_map_2782_);
lean_dec(v_o_2779_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2797_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2787_, 0, v_v_2781_);
lean_inc(v_k_2780_);
v___x_2788_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2780_, v___x_2787_, v_map_2782_);
if (v_hasTrace_2783_ == 0)
{
lean_object* v___x_2789_; uint8_t v___x_2790_; lean_object* v___x_2792_; 
v___x_2789_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_2790_ = l_Lean_Name_isPrefixOf(v___x_2789_, v_k_2780_);
lean_dec(v_k_2780_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v___x_2788_);
v___x_2792_ = v___x_2785_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2788_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*1, v___x_2790_);
return v___x_2792_;
}
}
else
{
lean_object* v___x_2795_; 
lean_dec(v_k_2780_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v___x_2788_);
v___x_2795_ = v___x_2785_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2788_);
lean_ctor_set_uint8(v_reuseFailAlloc_2796_, sizeof(void*)*1, v_hasTrace_2783_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___boxed(lean_object* v_o_2798_, lean_object* v_k_2799_, lean_object* v_v_2800_){
_start:
{
uint8_t v_v_boxed_2801_; lean_object* v_res_2802_; 
v_v_boxed_2801_ = lean_unbox(v_v_2800_);
v_res_2802_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_o_2798_, v_k_2799_, v_v_boxed_2801_);
return v_res_2802_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(lean_object* v_opts_2803_, lean_object* v_opt_2804_){
_start:
{
lean_object* v_name_2805_; lean_object* v_defValue_2806_; lean_object* v_map_2807_; lean_object* v___x_2808_; 
v_name_2805_ = lean_ctor_get(v_opt_2804_, 0);
v_defValue_2806_ = lean_ctor_get(v_opt_2804_, 1);
v_map_2807_ = lean_ctor_get(v_opts_2803_, 0);
v___x_2808_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2807_, v_name_2805_);
if (lean_obj_tag(v___x_2808_) == 0)
{
uint8_t v___x_2809_; 
v___x_2809_ = lean_unbox(v_defValue_2806_);
return v___x_2809_;
}
else
{
lean_object* v_val_2810_; 
v_val_2810_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_val_2810_);
lean_dec_ref_known(v___x_2808_, 1);
if (lean_obj_tag(v_val_2810_) == 1)
{
uint8_t v_v_2811_; 
v_v_2811_ = lean_ctor_get_uint8(v_val_2810_, 0);
lean_dec_ref_known(v_val_2810_, 0);
return v_v_2811_;
}
else
{
uint8_t v___x_2812_; 
lean_dec(v_val_2810_);
v___x_2812_ = lean_unbox(v_defValue_2806_);
return v___x_2812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1___boxed(lean_object* v_opts_2813_, lean_object* v_opt_2814_){
_start:
{
uint8_t v_res_2815_; lean_object* v_r_2816_; 
v_res_2815_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_opts_2813_, v_opt_2814_);
lean_dec_ref(v_opt_2814_);
lean_dec_ref(v_opts_2813_);
v_r_2816_ = lean_box(v_res_2815_);
return v_r_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0(uint8_t v_suppressInsideQuot_2822_, lean_object* v_ctx_2823_){
_start:
{
lean_object* v_toParserModuleContext_2824_; lean_object* v_toInputContext_2825_; lean_object* v_toCacheableParserContext_2826_; lean_object* v_tokens_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2847_; 
v_toParserModuleContext_2824_ = lean_ctor_get(v_ctx_2823_, 1);
v_toInputContext_2825_ = lean_ctor_get(v_ctx_2823_, 0);
v_toCacheableParserContext_2826_ = lean_ctor_get(v_ctx_2823_, 2);
v_tokens_2827_ = lean_ctor_get(v_ctx_2823_, 3);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_ctx_2823_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2829_ = v_ctx_2823_;
v_isShared_2830_ = v_isSharedCheck_2847_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_tokens_2827_);
lean_inc(v_toCacheableParserContext_2826_);
lean_inc(v_toParserModuleContext_2824_);
lean_inc(v_toInputContext_2825_);
lean_dec(v_ctx_2823_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2847_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v_env_2831_; lean_object* v_options_2832_; lean_object* v_currNamespace_2833_; lean_object* v_openDecls_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2846_; 
v_env_2831_ = lean_ctor_get(v_toParserModuleContext_2824_, 0);
v_options_2832_ = lean_ctor_get(v_toParserModuleContext_2824_, 1);
v_currNamespace_2833_ = lean_ctor_get(v_toParserModuleContext_2824_, 2);
v_openDecls_2834_ = lean_ctor_get(v_toParserModuleContext_2824_, 3);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_toParserModuleContext_2824_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2836_ = v_toParserModuleContext_2824_;
v_isShared_2837_ = v_isSharedCheck_2846_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_openDecls_2834_);
lean_inc(v_currNamespace_2833_);
lean_inc(v_options_2832_);
lean_inc(v_env_2831_);
lean_dec(v_toParserModuleContext_2824_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2846_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2838_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_2839_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_2832_, v___x_2838_, v_suppressInsideQuot_2822_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 1, v___x_2839_);
v___x_2841_ = v___x_2836_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_env_2831_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2845_, 2, v_currNamespace_2833_);
lean_ctor_set(v_reuseFailAlloc_2845_, 3, v_openDecls_2834_);
v___x_2841_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2843_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 1, v___x_2841_);
v___x_2843_ = v___x_2829_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_toInputContext_2825_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2844_, 2, v_toCacheableParserContext_2826_);
lean_ctor_set(v_reuseFailAlloc_2844_, 3, v_tokens_2827_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0___boxed(lean_object* v_suppressInsideQuot_2848_, lean_object* v_ctx_2849_){
_start:
{
uint8_t v_suppressInsideQuot_boxed_2850_; lean_object* v_res_2851_; 
v_suppressInsideQuot_boxed_2850_ = lean_unbox(v_suppressInsideQuot_2848_);
v_res_2851_ = l_Lean_Parser_evalInsideQuot___lam__0(v_suppressInsideQuot_boxed_2850_, v_ctx_2849_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object* v_fn_2852_, lean_object* v_declName_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_toCacheableParserContext_2856_; lean_object* v_toParserModuleContext_2857_; lean_object* v_quotDepth_2858_; uint8_t v_suppressInsideQuot_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v_toCacheableParserContext_2856_ = lean_ctor_get(v___y_2854_, 2);
v_toParserModuleContext_2857_ = lean_ctor_get(v___y_2854_, 1);
v_quotDepth_2858_ = lean_ctor_get(v_toCacheableParserContext_2856_, 1);
v_suppressInsideQuot_2859_ = lean_ctor_get_uint8(v_toCacheableParserContext_2856_, sizeof(void*)*4);
v___x_2860_ = lean_unsigned_to_nat(0u);
v___x_2861_ = lean_nat_dec_lt(v___x_2860_, v_quotDepth_2858_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_dec(v_declName_2853_);
v___x_2862_ = lean_apply_2(v_fn_2852_, v___y_2854_, v___y_2855_);
return v___x_2862_;
}
else
{
if (v_suppressInsideQuot_2859_ == 0)
{
lean_object* v_env_2863_; lean_object* v_options_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; 
v_env_2863_ = lean_ctor_get(v_toParserModuleContext_2857_, 0);
v_options_2864_ = lean_ctor_get(v_toParserModuleContext_2857_, 1);
v___x_2865_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_2866_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_2864_, v___x_2865_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; 
lean_dec(v_declName_2853_);
v___x_2867_ = lean_apply_2(v_fn_2852_, v___y_2854_, v___y_2855_);
return v___x_2867_;
}
else
{
uint8_t v___x_2868_; 
lean_inc(v_declName_2853_);
lean_inc_ref(v_env_2863_);
v___x_2868_ = l_Lean_Environment_contains(v_env_2863_, v_declName_2853_, v___x_2866_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; 
lean_dec(v_declName_2853_);
v___x_2869_ = lean_apply_2(v_fn_2852_, v___y_2854_, v___y_2855_);
return v___x_2869_;
}
else
{
lean_object* v___x_2870_; lean_object* v___f_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2870_ = lean_box(v_suppressInsideQuot_2859_);
v___f_2871_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2871_, 0, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2872_, 0, v_fn_2852_);
v___x_2873_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_2873_, 0, v_declName_2853_);
lean_closure_set(v___x_2873_, 1, v___x_2872_);
v___x_2874_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2871_, v___x_2873_, v___y_2854_, v___y_2855_);
return v___x_2874_;
}
}
}
else
{
lean_object* v___x_2875_; 
lean_dec(v_declName_2853_);
v___x_2875_ = lean_apply_2(v_fn_2852_, v___y_2854_, v___y_2855_);
return v___x_2875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object* v_declName_2876_, lean_object* v_p_2877_){
_start:
{
lean_object* v_info_2878_; lean_object* v_fn_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2887_; 
v_info_2878_ = lean_ctor_get(v_p_2877_, 0);
v_fn_2879_ = lean_ctor_get(v_p_2877_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_p_2877_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2881_ = v_p_2877_;
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_fn_2879_);
lean_inc(v_info_2878_);
lean_dec(v_p_2877_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___f_2883_; lean_object* v___x_2885_; 
v___f_2883_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__1), 4, 2);
lean_closure_set(v___f_2883_, 0, v_fn_2879_);
lean_closure_set(v___f_2883_, 1, v_declName_2876_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 1, v___f_2883_);
v___x_2885_ = v___x_2881_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_info_2878_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v___f_2883_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser(lean_object* v_catName_2888_, lean_object* v_declName_2889_, uint8_t v_leading_2890_, lean_object* v_p_2891_, lean_object* v_prio_2892_){
_start:
{
lean_object* v_p_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_inc_n(v_declName_2889_, 2);
v_p_2894_ = l_Lean_Parser_evalInsideQuot(v_declName_2889_, v_p_2891_);
v___x_2895_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_2896_ = lean_st_ref_get(v___x_2895_);
lean_inc_ref(v_p_2894_);
v___x_2897_ = l_Lean_Parser_addParser(v___x_2896_, v_catName_2888_, v_declName_2889_, v_leading_2890_, v_p_2894_, v_prio_2892_);
v___x_2898_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_2897_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2900_; lean_object* v_info_2901_; lean_object* v_collectKinds_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2898_, 1);
v___x_2900_ = lean_st_ref_swap(v___x_2895_, v_a_2899_);
lean_dec(v___x_2900_);
v_info_2901_ = lean_ctor_get(v_p_2894_, 0);
lean_inc_ref(v_info_2901_);
lean_dec_ref(v_p_2894_);
v_collectKinds_2902_ = lean_ctor_get(v_info_2901_, 1);
v___x_2903_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_2904_ = lean_st_ref_take(v___x_2903_);
lean_inc_ref(v_collectKinds_2902_);
v___x_2905_ = lean_apply_1(v_collectKinds_2902_, v___x_2904_);
v___x_2906_ = lean_st_ref_put(v___x_2903_, v___x_2905_);
v___x_2907_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_2901_, v_declName_2889_);
return v___x_2907_;
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec_ref(v_p_2894_);
lean_dec(v_declName_2889_);
v_a_2908_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2898_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2898_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* v_catName_2916_, lean_object* v_declName_2917_, lean_object* v_leading_2918_, lean_object* v_p_2919_, lean_object* v_prio_2920_, lean_object* v_a_2921_){
_start:
{
uint8_t v_leading_boxed_2922_; lean_object* v_res_2923_; 
v_leading_boxed_2922_ = lean_unbox(v_leading_2918_);
v_res_2923_ = l_Lean_Parser_addBuiltinParser(v_catName_2916_, v_declName_2917_, v_leading_boxed_2922_, v_p_2919_, v_prio_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* v_catName_2924_, lean_object* v_declName_2925_, lean_object* v_p_2926_, lean_object* v_prio_2927_){
_start:
{
uint8_t v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = 1;
v___x_2930_ = l_Lean_Parser_addBuiltinParser(v_catName_2924_, v_declName_2925_, v___x_2929_, v_p_2926_, v_prio_2927_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object* v_catName_2931_, lean_object* v_declName_2932_, lean_object* v_p_2933_, lean_object* v_prio_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_Parser_addBuiltinLeadingParser(v_catName_2931_, v_declName_2932_, v_p_2933_, v_prio_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* v_catName_2937_, lean_object* v_declName_2938_, lean_object* v_p_2939_, lean_object* v_prio_2940_){
_start:
{
uint8_t v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = 0;
v___x_2943_ = l_Lean_Parser_addBuiltinParser(v_catName_2937_, v_declName_2938_, v___x_2942_, v_p_2939_, v_prio_2940_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object* v_catName_2944_, lean_object* v_declName_2945_, lean_object* v_p_2946_, lean_object* v_prio_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lean_Parser_addBuiltinTrailingParser(v_catName_2944_, v_declName_2945_, v_p_2946_, v_prio_2947_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object* v_kind_2950_){
_start:
{
uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = 1;
lean_inc(v_kind_2950_);
v___x_2952_ = l_Lean_Name_toString(v_kind_2950_, v___x_2951_);
v___x_2953_ = l_Lean_Parser_mkAntiquot(v___x_2952_, v_kind_2950_, v___x_2951_, v___x_2951_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object* v_kind_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v___x_2957_; lean_object* v_fn_2958_; lean_object* v___x_2959_; 
v___x_2957_ = l_Lean_Parser_mkCategoryAntiquotParser(v_kind_2954_);
v_fn_2958_ = lean_ctor_get(v___x_2957_, 1);
lean_inc_ref(v_fn_2958_);
lean_dec_ref(v___x_2957_);
v___x_2959_ = lean_apply_2(v_fn_2958_, v_a_2955_, v_a_2956_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl___lam__0(lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v___x_2963_; lean_object* v_fn_2964_; lean_object* v___x_2965_; 
v___x_2963_ = l_Lean_Parser_mkCategoryAntiquotParser(v___y_2960_);
v_fn_2964_ = lean_ctor_get(v___x_2963_, 1);
lean_inc_ref(v_fn_2964_);
lean_dec_ref(v___x_2963_);
v___x_2965_ = lean_apply_2(v_fn_2964_, v___y_2961_, v___y_2962_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* v_catName_2974_, lean_object* v_ctx_2975_, lean_object* v_s_2976_){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; uint8_t v___x_2980_; lean_object* v___y_2982_; 
v___x_2977_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2978_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__1));
v___x_2979_ = lean_name_eq(v_catName_2974_, v___x_2978_);
v___x_2980_ = 1;
if (v___x_2979_ == 0)
{
v___y_2982_ = v_catName_2974_;
goto v___jp_2981_;
}
else
{
lean_object* v___x_3005_; 
lean_dec(v_catName_2974_);
v___x_3005_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__5));
v___y_2982_ = v___x_3005_;
goto v___jp_2981_;
}
v___jp_2981_:
{
lean_object* v_toParserModuleContext_2983_; lean_object* v_env_2984_; lean_object* v___x_2985_; lean_object* v_ext_2986_; lean_object* v_toEnvExtension_2987_; lean_object* v_asyncMode_2988_; uint8_t v___x_2989_; lean_object* v___x_2990_; lean_object* v_categories_2991_; lean_object* v___x_2992_; 
v_toParserModuleContext_2983_ = lean_ctor_get(v_ctx_2975_, 1);
v_env_2984_ = lean_ctor_get(v_toParserModuleContext_2983_, 0);
v___x_2985_ = l_Lean_Parser_parserExtension;
v_ext_2986_ = lean_ctor_get(v___x_2985_, 1);
v_toEnvExtension_2987_ = lean_ctor_get(v_ext_2986_, 0);
v_asyncMode_2988_ = lean_ctor_get(v_toEnvExtension_2987_, 2);
v___x_2989_ = 0;
lean_inc_ref(v_env_2984_);
v___x_2990_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2977_, v___x_2985_, v_env_2984_, v_asyncMode_2988_, v___x_2989_);
v_categories_2991_ = lean_ctor_get(v___x_2990_, 2);
lean_inc_ref(v_categories_2991_);
lean_dec(v___x_2990_);
v___x_2992_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2991_, v___y_2982_);
lean_dec_ref(v_categories_2991_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
lean_dec_ref(v_ctx_2975_);
v___x_2993_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__2));
v___x_2994_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2982_, v___x_2980_);
v___x_2995_ = lean_string_append(v___x_2993_, v___x_2994_);
lean_dec_ref(v___x_2994_);
v___x_2996_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__3));
v___x_2997_ = lean_string_append(v___x_2995_, v___x_2996_);
v___x_2998_ = lean_box(0);
v___x_2999_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2976_, v___x_2997_, v___x_2998_, v___x_2980_);
return v___x_2999_;
}
else
{
lean_object* v_val_3000_; lean_object* v_tables_3001_; uint8_t v_behavior_3002_; lean_object* v___f_3003_; lean_object* v___x_3004_; 
v_val_3000_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_val_3000_);
lean_dec_ref_known(v___x_2992_, 1);
v_tables_3001_ = lean_ctor_get(v_val_3000_, 2);
lean_inc_ref(v_tables_3001_);
v_behavior_3002_ = lean_ctor_get_uint8(v_val_3000_, sizeof(void*)*3);
lean_dec(v_val_3000_);
lean_inc(v___y_2982_);
v___f_3003_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl___lam__0), 3, 1);
lean_closure_set(v___f_3003_, 0, v___y_2982_);
v___x_3004_ = l_Lean_Parser_prattParser(v___y_2982_, v_tables_3001_, v_behavior_3002_, v___f_3003_, v_ctx_2975_, v_s_2976_);
return v___x_3004_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3008_ = l_Lean_Parser_categoryParserFnRef;
v___x_3009_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_));
v___x_3010_ = lean_box(0);
v___x_3011_ = lean_st_ref_swap(v___x_3008_, v___x_3009_);
lean_dec(v___x_3011_);
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
return v_res_3014_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
return v___x_3016_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0);
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object* v_ext_3019_, lean_object* v_b_3020_, uint8_t v_kind_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_toCold_3025_; lean_object* v_currNamespace_3026_; lean_object* v___x_3027_; lean_object* v_env_3028_; lean_object* v_nextMacroScope_3029_; lean_object* v_ngen_3030_; lean_object* v_auxDeclNGen_3031_; lean_object* v_traceState_3032_; lean_object* v_recordedDeps_3033_; lean_object* v_messages_3034_; lean_object* v_infoState_3035_; lean_object* v_snapshotTasks_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3048_; 
v_toCold_3025_ = lean_ctor_get(v___y_3022_, 0);
v_currNamespace_3026_ = lean_ctor_get(v_toCold_3025_, 4);
v___x_3027_ = lean_st_ref_take(v___y_3023_);
v_env_3028_ = lean_ctor_get(v___x_3027_, 0);
v_nextMacroScope_3029_ = lean_ctor_get(v___x_3027_, 1);
v_ngen_3030_ = lean_ctor_get(v___x_3027_, 2);
v_auxDeclNGen_3031_ = lean_ctor_get(v___x_3027_, 3);
v_traceState_3032_ = lean_ctor_get(v___x_3027_, 4);
v_recordedDeps_3033_ = lean_ctor_get(v___x_3027_, 6);
v_messages_3034_ = lean_ctor_get(v___x_3027_, 7);
v_infoState_3035_ = lean_ctor_get(v___x_3027_, 8);
v_snapshotTasks_3036_ = lean_ctor_get(v___x_3027_, 9);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3048_ == 0)
{
lean_object* v_unused_3049_; 
v_unused_3049_ = lean_ctor_get(v___x_3027_, 5);
lean_dec(v_unused_3049_);
v___x_3038_ = v___x_3027_;
v_isShared_3039_ = v_isSharedCheck_3048_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_snapshotTasks_3036_);
lean_inc(v_infoState_3035_);
lean_inc(v_messages_3034_);
lean_inc(v_recordedDeps_3033_);
lean_inc(v_traceState_3032_);
lean_inc(v_auxDeclNGen_3031_);
lean_inc(v_ngen_3030_);
lean_inc(v_nextMacroScope_3029_);
lean_inc(v_env_3028_);
lean_dec(v___x_3027_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3048_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3044_; 
v___x_3040_ = lean_box(0);
lean_inc(v_currNamespace_3026_);
v___x_3041_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3028_, v_ext_3019_, v_b_3020_, v_kind_3021_, v_currNamespace_3026_);
v___x_3042_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 5, v___x_3042_);
lean_ctor_set(v___x_3038_, 0, v___x_3041_);
v___x_3044_ = v___x_3038_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_nextMacroScope_3029_);
lean_ctor_set(v_reuseFailAlloc_3047_, 2, v_ngen_3030_);
lean_ctor_set(v_reuseFailAlloc_3047_, 3, v_auxDeclNGen_3031_);
lean_ctor_set(v_reuseFailAlloc_3047_, 4, v_traceState_3032_);
lean_ctor_set(v_reuseFailAlloc_3047_, 5, v___x_3042_);
lean_ctor_set(v_reuseFailAlloc_3047_, 6, v_recordedDeps_3033_);
lean_ctor_set(v_reuseFailAlloc_3047_, 7, v_messages_3034_);
lean_ctor_set(v_reuseFailAlloc_3047_, 8, v_infoState_3035_);
lean_ctor_set(v_reuseFailAlloc_3047_, 9, v_snapshotTasks_3036_);
v___x_3044_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = lean_st_ref_put(v___y_3023_, v___x_3044_);
v___x_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3040_);
return v___x_3046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object* v_ext_3050_, lean_object* v_b_3051_, lean_object* v_kind_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
uint8_t v_kind_boxed_3056_; lean_object* v_res_3057_; 
v_kind_boxed_3056_ = lean_unbox(v_kind_3052_);
v_res_3057_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_3050_, v_b_3051_, v_kind_boxed_3056_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object* v_00_u03b1_3058_, lean_object* v_00_u03b2_3059_, lean_object* v_00_u03c3_3060_, lean_object* v_ext_3061_, lean_object* v_b_3062_, uint8_t v_kind_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_3061_, v_b_3062_, v_kind_3063_, v___y_3064_, v___y_3065_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object* v_00_u03b1_3068_, lean_object* v_00_u03b2_3069_, lean_object* v_00_u03c3_3070_, lean_object* v_ext_3071_, lean_object* v_b_3072_, lean_object* v_kind_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
uint8_t v_kind_boxed_3077_; lean_object* v_res_3078_; 
v_kind_boxed_3077_ = lean_unbox(v_kind_3073_);
v_res_3078_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(v_00_u03b1_3068_, v_00_u03b2_3069_, v_00_u03c3_3070_, v_ext_3071_, v_b_3072_, v_kind_boxed_3077_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object* v_x_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
if (lean_obj_tag(v_x_3079_) == 0)
{
lean_object* v_a_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v_a_3083_ = lean_ctor_get(v_x_3079_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v_x_3079_, 1);
v___x_3084_ = l_Lean_stringToMessageData(v_a_3083_);
v___x_3085_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3084_, v___y_3080_, v___y_3081_);
return v___x_3085_;
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
v_a_3086_ = lean_ctor_get(v_x_3079_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_x_3079_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v_x_3079_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v_x_3079_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
lean_ctor_set_tag(v___x_3088_, 0);
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object* v_x_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object* v_tk_3099_, uint8_t v_kind_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v_env_3106_; lean_object* v___x_3107_; lean_object* v_ext_3108_; lean_object* v_toEnvExtension_3109_; lean_object* v_asyncMode_3110_; uint8_t v___x_3111_; lean_object* v___x_3112_; lean_object* v_tokens_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3104_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3105_ = lean_st_ref_get(v_a_3102_);
v_env_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc_ref(v_env_3106_);
lean_dec(v___x_3105_);
v___x_3107_ = l_Lean_Parser_parserExtension;
v_ext_3108_ = lean_ctor_get(v___x_3107_, 1);
v_toEnvExtension_3109_ = lean_ctor_get(v_ext_3108_, 0);
v_asyncMode_3110_ = lean_ctor_get(v_toEnvExtension_3109_, 2);
v___x_3111_ = 0;
v___x_3112_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3104_, v___x_3107_, v_env_3106_, v_asyncMode_3110_, v___x_3111_);
v_tokens_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc_ref(v_tokens_3113_);
lean_dec(v___x_3112_);
lean_inc_ref(v_tk_3099_);
v___x_3114_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_3113_, v_tk_3099_);
v___x_3115_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v___x_3114_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec_ref_known(v___x_3115_, 1);
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v_tk_3099_);
v___x_3117_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_3107_, v___x_3116_, v_kind_3100_, v_a_3101_, v_a_3102_);
return v___x_3117_;
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v_tk_3099_);
v_a_3118_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3115_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3115_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object* v_tk_3126_, lean_object* v_kind_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
uint8_t v_kind_boxed_3131_; lean_object* v_res_3132_; 
v_kind_boxed_3131_ = lean_unbox(v_kind_3127_);
v_res_3132_ = l_Lean_Parser_addToken(v_tk_3126_, v_kind_boxed_3131_, v_a_3128_, v_a_3129_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_object* v_00_u03b1_3133_, lean_object* v_x_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_3134_, v___y_3135_, v___y_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___boxed(lean_object* v_00_u03b1_3139_, lean_object* v_x_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(v_00_u03b1_3139_, v_x_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object* v_env_3145_, lean_object* v_k_3146_){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3147_ = l_Lean_Parser_parserExtension;
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_k_3146_);
v___x_3149_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_3147_, v_env_3145_, v___x_3148_);
return v___x_3149_;
}
}
static uint8_t _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0(void){
_start:
{
lean_object* v___x_3150_; uint8_t v___x_3151_; 
v___x_3150_ = lean_box(0);
v___x_3151_ = lean_internal_is_stage0(v___x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object* v_env_3152_, lean_object* v_k_3153_){
_start:
{
lean_object* v___x_3154_; lean_object* v_ext_3155_; lean_object* v_toEnvExtension_3156_; lean_object* v_asyncMode_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; lean_object* v___x_3160_; lean_object* v_kinds_3161_; uint8_t v___x_3162_; 
v___x_3154_ = l_Lean_Parser_parserExtension;
v_ext_3155_ = lean_ctor_get(v___x_3154_, 1);
v_toEnvExtension_3156_ = lean_ctor_get(v_ext_3155_, 0);
v_asyncMode_3157_ = lean_ctor_get(v_toEnvExtension_3156_, 2);
v___x_3158_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3159_ = 0;
lean_inc_ref(v_env_3152_);
v___x_3160_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3158_, v___x_3154_, v_env_3152_, v_asyncMode_3157_, v___x_3159_);
v_kinds_3161_ = lean_ctor_get(v___x_3160_, 1);
lean_inc_ref(v_kinds_3161_);
lean_dec(v___x_3160_);
v___x_3162_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_3161_, v_k_3153_);
lean_dec_ref(v_kinds_3161_);
if (v___x_3162_ == 0)
{
uint8_t v___x_3163_; 
v___x_3163_ = lean_uint8_once(&l_Lean_Parser_isValidSyntaxNodeKind___closed__0, &l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once, _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0);
if (v___x_3163_ == 0)
{
lean_dec(v_k_3153_);
lean_dec_ref(v_env_3152_);
return v___x_3159_;
}
else
{
uint8_t v___x_3164_; 
v___x_3164_ = l_Lean_Environment_contains(v_env_3152_, v_k_3153_, v___x_3163_);
return v___x_3164_;
}
}
else
{
lean_dec(v_k_3153_);
lean_dec_ref(v_env_3152_);
return v___x_3162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* v_env_3165_, lean_object* v_k_3166_){
_start:
{
uint8_t v_res_3167_; lean_object* v_r_3168_; 
v_res_3167_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_3165_, v_k_3166_);
v_r_3168_ = lean_box(v_res_3167_);
return v_r_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds___lam__0(lean_object* v_ks_3169_, lean_object* v_k_3170_, lean_object* v_x_3171_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3172_, 0, v_k_3170_);
lean_ctor_set(v___x_3172_, 1, v_ks_3169_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3173_, lean_object* v_keys_3174_, lean_object* v_vals_3175_, lean_object* v_i_3176_, lean_object* v_acc_3177_){
_start:
{
lean_object* v___x_3178_; uint8_t v___x_3179_; 
v___x_3178_ = lean_array_get_size(v_keys_3174_);
v___x_3179_ = lean_nat_dec_lt(v_i_3176_, v___x_3178_);
if (v___x_3179_ == 0)
{
lean_dec(v_i_3176_);
lean_dec(v_f_3173_);
return v_acc_3177_;
}
else
{
lean_object* v_k_3180_; lean_object* v_v_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v_k_3180_ = lean_array_fget_borrowed(v_keys_3174_, v_i_3176_);
v_v_3181_ = lean_array_fget_borrowed(v_vals_3175_, v_i_3176_);
lean_inc(v_f_3173_);
lean_inc(v_v_3181_);
lean_inc(v_k_3180_);
v___x_3182_ = lean_apply_3(v_f_3173_, v_acc_3177_, v_k_3180_, v_v_3181_);
v___x_3183_ = lean_unsigned_to_nat(1u);
v___x_3184_ = lean_nat_add(v_i_3176_, v___x_3183_);
lean_dec(v_i_3176_);
v_i_3176_ = v___x_3184_;
v_acc_3177_ = v___x_3182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3186_, lean_object* v_keys_3187_, lean_object* v_vals_3188_, lean_object* v_i_3189_, lean_object* v_acc_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3186_, v_keys_3187_, v_vals_3188_, v_i_3189_, v_acc_3190_);
lean_dec_ref(v_vals_3188_);
lean_dec_ref(v_keys_3187_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3192_, lean_object* v_as_3193_, size_t v_i_3194_, size_t v_stop_3195_, lean_object* v_b_3196_){
_start:
{
lean_object* v___y_3198_; uint8_t v___x_3202_; 
v___x_3202_ = lean_usize_dec_eq(v_i_3194_, v_stop_3195_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; 
v___x_3203_ = lean_array_uget_borrowed(v_as_3193_, v_i_3194_);
switch(lean_obj_tag(v___x_3203_))
{
case 0:
{
lean_object* v_key_3204_; lean_object* v_val_3205_; lean_object* v___x_3206_; 
v_key_3204_ = lean_ctor_get(v___x_3203_, 0);
v_val_3205_ = lean_ctor_get(v___x_3203_, 1);
lean_inc(v_f_3192_);
lean_inc(v_val_3205_);
lean_inc(v_key_3204_);
v___x_3206_ = lean_apply_3(v_f_3192_, v_b_3196_, v_key_3204_, v_val_3205_);
v___y_3198_ = v___x_3206_;
goto v___jp_3197_;
}
case 1:
{
lean_object* v_node_3207_; lean_object* v___x_3208_; 
v_node_3207_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_f_3192_);
v___x_3208_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3192_, v_node_3207_, v_b_3196_);
v___y_3198_ = v___x_3208_;
goto v___jp_3197_;
}
default: 
{
v___y_3198_ = v_b_3196_;
goto v___jp_3197_;
}
}
}
else
{
lean_dec(v_f_3192_);
return v_b_3196_;
}
v___jp_3197_:
{
size_t v___x_3199_; size_t v___x_3200_; 
v___x_3199_ = ((size_t)1ULL);
v___x_3200_ = lean_usize_add(v_i_3194_, v___x_3199_);
v_i_3194_ = v___x_3200_;
v_b_3196_ = v___y_3198_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3209_, lean_object* v_x_3210_, lean_object* v_x_3211_){
_start:
{
if (lean_obj_tag(v_x_3210_) == 0)
{
lean_object* v_es_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; 
v_es_3212_ = lean_ctor_get(v_x_3210_, 0);
v___x_3213_ = lean_unsigned_to_nat(0u);
v___x_3214_ = lean_array_get_size(v_es_3212_);
v___x_3215_ = lean_nat_dec_lt(v___x_3213_, v___x_3214_);
if (v___x_3215_ == 0)
{
lean_dec(v_f_3209_);
return v_x_3211_;
}
else
{
size_t v___x_3216_; size_t v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = ((size_t)0ULL);
v___x_3217_ = lean_usize_of_nat(v___x_3214_);
v___x_3218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3209_, v_es_3212_, v___x_3216_, v___x_3217_, v_x_3211_);
return v___x_3218_;
}
}
else
{
lean_object* v_ks_3219_; lean_object* v_vs_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_ks_3219_ = lean_ctor_get(v_x_3210_, 0);
v_vs_3220_ = lean_ctor_get(v_x_3210_, 1);
v___x_3221_ = lean_unsigned_to_nat(0u);
v___x_3222_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3209_, v_ks_3219_, v_vs_3220_, v___x_3221_, v_x_3211_);
return v___x_3222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3223_, lean_object* v_x_3224_, lean_object* v_x_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3223_, v_x_3224_, v_x_3225_);
lean_dec_ref(v_x_3224_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3227_, lean_object* v_as_3228_, lean_object* v_i_3229_, lean_object* v_stop_3230_, lean_object* v_b_3231_){
_start:
{
size_t v_i_boxed_3232_; size_t v_stop_boxed_3233_; lean_object* v_res_3234_; 
v_i_boxed_3232_ = lean_unbox_usize(v_i_3229_);
lean_dec(v_i_3229_);
v_stop_boxed_3233_ = lean_unbox_usize(v_stop_3230_);
lean_dec(v_stop_3230_);
v_res_3234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3227_, v_as_3228_, v_i_boxed_3232_, v_stop_boxed_3233_, v_b_3231_);
lean_dec_ref(v_as_3228_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object* v_f_3235_, lean_object* v_x1_3236_, lean_object* v_x2_3237_, lean_object* v_x3_3238_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_apply_3(v_f_3235_, v_x1_3236_, v_x2_3237_, v_x3_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object* v_map_3240_, lean_object* v_f_3241_, lean_object* v_init_3242_){
_start:
{
lean_object* v___f_3243_; lean_object* v___x_3244_; 
v___f_3243_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3243_, 0, v_f_3241_);
v___x_3244_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v___f_3243_, v_map_3240_, v_init_3242_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object* v_map_3245_, lean_object* v_f_3246_, lean_object* v_init_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3245_, v_f_3246_, v_init_3247_);
lean_dec_ref(v_map_3245_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* v_env_3250_){
_start:
{
lean_object* v___x_3251_; lean_object* v_ext_3252_; lean_object* v_toEnvExtension_3253_; lean_object* v_asyncMode_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; lean_object* v___x_3257_; lean_object* v_kinds_3258_; lean_object* v___f_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3251_ = l_Lean_Parser_parserExtension;
v_ext_3252_ = lean_ctor_get(v___x_3251_, 1);
v_toEnvExtension_3253_ = lean_ctor_get(v_ext_3252_, 0);
v_asyncMode_3254_ = lean_ctor_get(v_toEnvExtension_3253_, 2);
v___x_3255_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3256_ = 0;
v___x_3257_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3255_, v___x_3251_, v_env_3250_, v_asyncMode_3254_, v___x_3256_);
v_kinds_3258_ = lean_ctor_get(v___x_3257_, 1);
lean_inc_ref(v_kinds_3258_);
lean_dec(v___x_3257_);
v___f_3259_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKinds___closed__0));
v___x_3260_ = lean_box(0);
v___x_3261_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_kinds_3258_, v___f_3259_, v___x_3260_);
lean_dec_ref(v_kinds_3258_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object* v_00_u03c3_3262_, lean_object* v_00_u03b2_3263_, lean_object* v_map_3264_, lean_object* v_f_3265_, lean_object* v_init_3266_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3264_, v_f_3265_, v_init_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object* v_00_u03c3_3268_, lean_object* v_00_u03b2_3269_, lean_object* v_map_3270_, lean_object* v_f_3271_, lean_object* v_init_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(v_00_u03c3_3268_, v_00_u03b2_3269_, v_map_3270_, v_f_3271_, v_init_3272_);
lean_dec_ref(v_map_3270_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object* v_map_3274_, lean_object* v_f_3275_, lean_object* v_init_3276_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3275_, v_map_3274_, v_init_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object* v_map_3278_, lean_object* v_f_3279_, lean_object* v_init_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(v_map_3278_, v_f_3279_, v_init_3280_);
lean_dec_ref(v_map_3278_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object* v_00_u03c3_3282_, lean_object* v_00_u03b2_3283_, lean_object* v_map_3284_, lean_object* v_f_3285_, lean_object* v_init_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3285_, v_map_3284_, v_init_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3288_, lean_object* v_00_u03b2_3289_, lean_object* v_map_3290_, lean_object* v_f_3291_, lean_object* v_init_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(v_00_u03c3_3288_, v_00_u03b2_3289_, v_map_3290_, v_f_3291_, v_init_3292_);
lean_dec_ref(v_map_3290_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3294_, lean_object* v_00_u03b1_3295_, lean_object* v_00_u03b2_3296_, lean_object* v_f_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3297_, v_x_3298_, v_x_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3301_, lean_object* v_00_u03b1_3302_, lean_object* v_00_u03b2_3303_, lean_object* v_f_3304_, lean_object* v_x_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(v_00_u03c3_3301_, v_00_u03b1_3302_, v_00_u03b2_3303_, v_f_3304_, v_x_3305_, v_x_3306_);
lean_dec_ref(v_x_3305_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3308_, lean_object* v_00_u03b2_3309_, lean_object* v_00_u03c3_3310_, lean_object* v_f_3311_, lean_object* v_as_3312_, size_t v_i_3313_, size_t v_stop_3314_, lean_object* v_b_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3311_, v_as_3312_, v_i_3313_, v_stop_3314_, v_b_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3317_, lean_object* v_00_u03b2_3318_, lean_object* v_00_u03c3_3319_, lean_object* v_f_3320_, lean_object* v_as_3321_, lean_object* v_i_3322_, lean_object* v_stop_3323_, lean_object* v_b_3324_){
_start:
{
size_t v_i_boxed_3325_; size_t v_stop_boxed_3326_; lean_object* v_res_3327_; 
v_i_boxed_3325_ = lean_unbox_usize(v_i_3322_);
lean_dec(v_i_3322_);
v_stop_boxed_3326_ = lean_unbox_usize(v_stop_3323_);
lean_dec(v_stop_3323_);
v_res_3327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3317_, v_00_u03b2_3318_, v_00_u03c3_3319_, v_f_3320_, v_as_3321_, v_i_boxed_3325_, v_stop_boxed_3326_, v_b_3324_);
lean_dec_ref(v_as_3321_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3328_, lean_object* v_00_u03b1_3329_, lean_object* v_00_u03b2_3330_, lean_object* v_f_3331_, lean_object* v_keys_3332_, lean_object* v_vals_3333_, lean_object* v_heq_3334_, lean_object* v_i_3335_, lean_object* v_acc_3336_){
_start:
{
lean_object* v___x_3337_; 
v___x_3337_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3331_, v_keys_3332_, v_vals_3333_, v_i_3335_, v_acc_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3338_, lean_object* v_00_u03b1_3339_, lean_object* v_00_u03b2_3340_, lean_object* v_f_3341_, lean_object* v_keys_3342_, lean_object* v_vals_3343_, lean_object* v_heq_3344_, lean_object* v_i_3345_, lean_object* v_acc_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3338_, v_00_u03b1_3339_, v_00_u03b2_3340_, v_f_3341_, v_keys_3342_, v_vals_3343_, v_heq_3344_, v_i_3345_, v_acc_3346_);
lean_dec_ref(v_vals_3343_);
lean_dec_ref(v_keys_3342_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* v_env_3348_){
_start:
{
lean_object* v___x_3349_; lean_object* v_ext_3350_; lean_object* v_toEnvExtension_3351_; lean_object* v_asyncMode_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; lean_object* v___x_3355_; lean_object* v_tokens_3356_; 
v___x_3349_ = l_Lean_Parser_parserExtension;
v_ext_3350_ = lean_ctor_get(v___x_3349_, 1);
v_toEnvExtension_3351_ = lean_ctor_get(v_ext_3350_, 0);
v_asyncMode_3352_ = lean_ctor_get(v_toEnvExtension_3351_, 2);
v___x_3353_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3354_ = 0;
v___x_3355_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3353_, v___x_3349_, v_env_3348_, v_asyncMode_3352_, v___x_3354_);
v_tokens_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc_ref(v_tokens_3356_);
lean_dec(v___x_3355_);
return v_tokens_3356_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__8));
v___x_3382_ = l_Lean_mkAtom(v___x_3381_);
return v___x_3382_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__10, &l_Lean_Parser_mkInputContext___auto__1___closed__10_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__10);
v___x_3384_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3385_ = lean_array_push(v___x_3384_, v___x_3383_);
return v___x_3385_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3397_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3398_ = lean_array_push(v___x_3397_, v___x_3396_);
return v___x_3398_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3399_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__15, &l_Lean_Parser_mkInputContext___auto__1___closed__15_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__15);
v___x_3400_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__13));
v___x_3401_ = lean_box(2);
v___x_3402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v___x_3400_);
lean_ctor_set(v___x_3402_, 2, v___x_3399_);
return v___x_3402_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3403_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__16, &l_Lean_Parser_mkInputContext___auto__1___closed__16_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__16);
v___x_3404_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__11, &l_Lean_Parser_mkInputContext___auto__1___closed__11_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__11);
v___x_3405_ = lean_array_push(v___x_3404_, v___x_3403_);
return v___x_3405_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3406_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3407_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__17, &l_Lean_Parser_mkInputContext___auto__1___closed__17_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__17);
v___x_3408_ = lean_array_push(v___x_3407_, v___x_3406_);
return v___x_3408_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3409_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3410_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__18, &l_Lean_Parser_mkInputContext___auto__1___closed__18_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__18);
v___x_3411_ = lean_array_push(v___x_3410_, v___x_3409_);
return v___x_3411_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3412_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3413_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__19, &l_Lean_Parser_mkInputContext___auto__1___closed__19_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__19);
v___x_3414_ = lean_array_push(v___x_3413_, v___x_3412_);
return v___x_3414_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3415_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3416_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__20, &l_Lean_Parser_mkInputContext___auto__1___closed__20_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__20);
v___x_3417_ = lean_array_push(v___x_3416_, v___x_3415_);
return v___x_3417_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3418_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__21, &l_Lean_Parser_mkInputContext___auto__1___closed__21_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__21);
v___x_3419_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__9));
v___x_3420_ = lean_box(2);
v___x_3421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
lean_ctor_set(v___x_3421_, 1, v___x_3419_);
lean_ctor_set(v___x_3421_, 2, v___x_3418_);
return v___x_3421_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__22, &l_Lean_Parser_mkInputContext___auto__1___closed__22_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__22);
v___x_3423_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3424_ = lean_array_push(v___x_3423_, v___x_3422_);
return v___x_3424_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3425_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__23, &l_Lean_Parser_mkInputContext___auto__1___closed__23_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__23);
v___x_3426_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3427_ = lean_box(2);
v___x_3428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
lean_ctor_set(v___x_3428_, 1, v___x_3426_);
lean_ctor_set(v___x_3428_, 2, v___x_3425_);
return v___x_3428_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__24, &l_Lean_Parser_mkInputContext___auto__1___closed__24_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__24);
v___x_3430_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3431_ = lean_array_push(v___x_3430_, v___x_3429_);
return v___x_3431_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3432_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__25, &l_Lean_Parser_mkInputContext___auto__1___closed__25_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__25);
v___x_3433_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3434_ = lean_box(2);
v___x_3435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
lean_ctor_set(v___x_3435_, 1, v___x_3433_);
lean_ctor_set(v___x_3435_, 2, v___x_3432_);
return v___x_3435_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__26, &l_Lean_Parser_mkInputContext___auto__1___closed__26_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__26);
v___x_3437_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3438_ = lean_array_push(v___x_3437_, v___x_3436_);
return v___x_3438_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3439_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__27, &l_Lean_Parser_mkInputContext___auto__1___closed__27_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__27);
v___x_3440_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3441_ = lean_box(2);
v___x_3442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
lean_ctor_set(v___x_3442_, 1, v___x_3440_);
lean_ctor_set(v___x_3442_, 2, v___x_3439_);
return v___x_3442_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1(void){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__28, &l_Lean_Parser_mkInputContext___auto__1___closed__28_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__28);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object* v_input_3444_, lean_object* v_fileName_3445_, uint8_t v_normalizeLineEndings_3446_, lean_object* v_endPos_3447_){
_start:
{
lean_object* v_fst_3449_; lean_object* v_snd_3450_; lean_object* v_text_3456_; 
v_text_3456_ = l_Lean_FileMap_ofString(v_input_3444_);
if (v_normalizeLineEndings_3446_ == 0)
{
v_fst_3449_ = v_text_3456_;
v_snd_3450_ = v_endPos_3447_;
goto v___jp_3448_;
}
else
{
lean_object* v_source_3457_; lean_object* v_endPos_x27_3458_; lean_object* v___x_3459_; lean_object* v_text_3460_; lean_object* v___x_3461_; 
v_source_3457_ = lean_ctor_get(v_text_3456_, 0);
lean_inc_ref(v_source_3457_);
v_endPos_x27_3458_ = l_Lean_FileMap_toPosition(v_text_3456_, v_endPos_3447_);
lean_dec(v_endPos_3447_);
v___x_3459_ = l_String_crlfToLf(v_source_3457_);
lean_dec_ref(v_source_3457_);
v_text_3460_ = l_Lean_FileMap_ofString(v___x_3459_);
v___x_3461_ = l_Lean_FileMap_ofPosition(v_text_3460_, v_endPos_x27_3458_);
v_fst_3449_ = v_text_3460_;
v_snd_3450_ = v___x_3461_;
goto v___jp_3448_;
}
v___jp_3448_:
{
lean_object* v_source_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v_source_3451_ = lean_ctor_get(v_fst_3449_, 0);
lean_inc_ref(v_source_3451_);
v___x_3452_ = lean_string_utf8_byte_size(v_source_3451_);
v___x_3453_ = lean_nat_dec_le(v_snd_3450_, v___x_3452_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3454_; 
lean_dec(v_snd_3450_);
v___x_3454_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3454_, 0, v_source_3451_);
lean_ctor_set(v___x_3454_, 1, v_fileName_3445_);
lean_ctor_set(v___x_3454_, 2, v_fst_3449_);
lean_ctor_set(v___x_3454_, 3, v___x_3452_);
return v___x_3454_;
}
else
{
lean_object* v___x_3455_; 
v___x_3455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3455_, 0, v_source_3451_);
lean_ctor_set(v___x_3455_, 1, v_fileName_3445_);
lean_ctor_set(v___x_3455_, 2, v_fst_3449_);
lean_ctor_set(v___x_3455_, 3, v_snd_3450_);
return v___x_3455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object* v_input_3462_, lean_object* v_fileName_3463_, lean_object* v_normalizeLineEndings_3464_, lean_object* v_endPos_3465_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3466_; lean_object* v_res_3467_; 
v_normalizeLineEndings_boxed_3466_ = lean_unbox(v_normalizeLineEndings_3464_);
v_res_3467_ = l_Lean_Parser_mkInputContext___redArg(v_input_3462_, v_fileName_3463_, v_normalizeLineEndings_boxed_3466_, v_endPos_3465_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object* v_input_3468_, lean_object* v_fileName_3469_, uint8_t v_normalizeLineEndings_3470_, lean_object* v_endPos_3471_, lean_object* v_endPos__valid_3472_){
_start:
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_Parser_mkInputContext___redArg(v_input_3468_, v_fileName_3469_, v_normalizeLineEndings_3470_, v_endPos_3471_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object* v_input_3474_, lean_object* v_fileName_3475_, lean_object* v_normalizeLineEndings_3476_, lean_object* v_endPos_3477_, lean_object* v_endPos__valid_3478_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3479_; lean_object* v_res_3480_; 
v_normalizeLineEndings_boxed_3479_ = lean_unbox(v_normalizeLineEndings_3476_);
v_res_3480_ = l_Lean_Parser_mkInputContext(v_input_3474_, v_fileName_3475_, v_normalizeLineEndings_boxed_3479_, v_endPos_3477_, v_endPos__valid_3478_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* v_input_3483_){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3484_ = l_Lean_Parser_SyntaxStack_empty;
v___x_3485_ = lean_unsigned_to_nat(0u);
v___x_3486_ = l_Lean_Parser_initCacheForInput(v_input_3483_);
v___x_3487_ = lean_box(0);
v___x_3488_ = ((lean_object*)(l_Lean_Parser_mkParserState___closed__0));
v___x_3489_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3484_);
lean_ctor_set(v___x_3489_, 1, v___x_3485_);
lean_ctor_set(v___x_3489_, 2, v___x_3485_);
lean_ctor_set(v___x_3489_, 3, v___x_3486_);
lean_ctor_set(v___x_3489_, 4, v___x_3487_);
lean_ctor_set(v___x_3489_, 5, v___x_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* v_input_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_Parser_mkParserState(v_input_3490_);
lean_dec_ref(v_input_3490_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* v_env_3494_, lean_object* v_catName_3495_, lean_object* v_input_3496_, lean_object* v_fileName_3497_){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v_p_3500_; uint8_t v___x_3501_; lean_object* v___x_3502_; lean_object* v_ictx_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v_s_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
v___x_3498_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__0));
v___x_3499_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 1);
lean_closure_set(v___x_3499_, 0, v_catName_3495_);
v_p_3500_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_3500_, 0, v___x_3498_);
lean_closure_set(v_p_3500_, 1, v___x_3499_);
v___x_3501_ = 1;
v___x_3502_ = lean_string_utf8_byte_size(v_input_3496_);
lean_inc_ref(v_input_3496_);
v_ictx_3503_ = l_Lean_Parser_mkInputContext___redArg(v_input_3496_, v_fileName_3497_, v___x_3501_, v___x_3502_);
v___x_3504_ = l_Lean_Options_empty;
v___x_3505_ = lean_box(0);
v___x_3506_ = lean_box(0);
lean_inc_ref(v_env_3494_);
v___x_3507_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3507_, 0, v_env_3494_);
lean_ctor_set(v___x_3507_, 1, v___x_3504_);
lean_ctor_set(v___x_3507_, 2, v___x_3505_);
lean_ctor_set(v___x_3507_, 3, v___x_3506_);
v___x_3508_ = l_Lean_Parser_getTokenTable(v_env_3494_);
v___x_3509_ = l_Lean_Parser_mkParserState(v_input_3496_);
lean_dec_ref(v_input_3496_);
lean_inc_ref(v_ictx_3503_);
v_s_3510_ = l_Lean_Parser_ParserFn_run(v_p_3500_, v_ictx_3503_, v___x_3507_, v___x_3508_, v___x_3509_);
lean_inc_ref(v_s_3510_);
v___x_3511_ = l_Lean_Parser_ParserState_allErrors(v_s_3510_);
v___x_3512_ = lean_array_get_size(v___x_3511_);
lean_dec_ref(v___x_3511_);
v___x_3513_ = lean_unsigned_to_nat(0u);
v___x_3514_ = lean_nat_dec_eq(v___x_3512_, v___x_3513_);
if (v___x_3514_ == 0)
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3503_, v_s_3510_);
v___x_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
return v___x_3516_;
}
else
{
lean_object* v_stxStack_3517_; lean_object* v_pos_3518_; uint8_t v___x_3519_; 
v_stxStack_3517_ = lean_ctor_get(v_s_3510_, 0);
v_pos_3518_ = lean_ctor_get(v_s_3510_, 2);
v___x_3519_ = l_Lean_Parser_InputContext_atEnd(v_ictx_3503_, v_pos_3518_);
if (v___x_3519_ == 0)
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3520_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__1));
v___x_3521_ = l_Lean_Parser_ParserState_mkError(v_s_3510_, v___x_3520_);
v___x_3522_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3503_, v___x_3521_);
v___x_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
return v___x_3523_;
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_inc_ref(v_stxStack_3517_);
lean_dec_ref(v_s_3510_);
lean_dec_ref(v_ictx_3503_);
v___x_3524_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3517_);
lean_dec_ref(v_stxStack_3517_);
v___x_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
return v___x_3525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* v_addFnName_3526_, lean_object* v_catName_3527_, lean_object* v_declName_3528_, lean_object* v_prio_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v_val_3545_; lean_object* v___x_3546_; 
v___x_3533_ = lean_box(0);
v___x_3534_ = l_Lean_mkConst(v_addFnName_3526_, v___x_3533_);
v___x_3535_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_catName_3527_);
lean_inc_n(v_declName_3528_, 2);
v___x_3536_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3528_);
v___x_3537_ = l_Lean_mkConst(v_declName_3528_, v___x_3533_);
v___x_3538_ = l_Lean_mkRawNatLit(v_prio_3529_);
v___x_3539_ = lean_unsigned_to_nat(4u);
v___x_3540_ = lean_mk_empty_array_with_capacity(v___x_3539_);
v___x_3541_ = lean_array_push(v___x_3540_, v___x_3535_);
v___x_3542_ = lean_array_push(v___x_3541_, v___x_3536_);
v___x_3543_ = lean_array_push(v___x_3542_, v___x_3537_);
v___x_3544_ = lean_array_push(v___x_3543_, v___x_3538_);
v_val_3545_ = l_Lean_mkAppN(v___x_3534_, v___x_3544_);
lean_dec_ref(v___x_3544_);
v___x_3546_ = l_Lean_declareBuiltin(v_declName_3528_, v_val_3545_, v_a_3530_, v_a_3531_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object* v_addFnName_3547_, lean_object* v_catName_3548_, lean_object* v_declName_3549_, lean_object* v_prio_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3547_, v_catName_3548_, v_declName_3549_, v_prio_3550_, v_a_3551_, v_a_3552_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* v_catName_3560_, lean_object* v_declName_3561_, lean_object* v_prio_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_Parser_declareLeadingBuiltinParser___closed__1));
v___x_3567_ = l_Lean_Parser_declareBuiltinParser(v___x_3566_, v_catName_3560_, v_declName_3561_, v_prio_3562_, v_a_3563_, v_a_3564_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object* v_catName_3568_, lean_object* v_declName_3569_, lean_object* v_prio_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3568_, v_declName_3569_, v_prio_3570_, v_a_3571_, v_a_3572_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* v_catName_3580_, lean_object* v_declName_3581_, lean_object* v_prio_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = ((lean_object*)(l_Lean_Parser_declareTrailingBuiltinParser___closed__1));
v___x_3587_ = l_Lean_Parser_declareBuiltinParser(v___x_3586_, v_catName_3580_, v_declName_3581_, v_prio_3582_, v_a_3583_, v_a_3584_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object* v_catName_3588_, lean_object* v_declName_3589_, lean_object* v_prio_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3588_, v_declName_3589_, v_prio_3590_, v_a_3591_, v_a_3592_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* v_args_3601_){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v___x_3602_ = l_Lean_Syntax_getNumArgs(v_args_3601_);
v___x_3603_ = lean_unsigned_to_nat(0u);
v___x_3604_ = lean_nat_dec_eq(v___x_3602_, v___x_3603_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = lean_unsigned_to_nat(1u);
v___x_3606_ = lean_nat_dec_eq(v___x_3602_, v___x_3605_);
lean_dec(v___x_3602_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; 
v___x_3607_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__1));
return v___x_3607_;
}
else
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = l_Lean_Syntax_getArg(v_args_3601_, v___x_3603_);
v___x_3609_ = l_Lean_Syntax_isNatLit_x3f(v___x_3608_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3610_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__2));
v___x_3611_ = l_Lean_Syntax_formatStx(v___x_3608_, v___x_3609_, v___x_3604_);
v___x_3612_ = l_Std_Format_defWidth;
v___x_3613_ = l_Std_Format_pretty(v___x_3611_, v___x_3612_, v___x_3603_, v___x_3603_);
v___x_3614_ = lean_string_append(v___x_3610_, v___x_3613_);
lean_dec_ref(v___x_3613_);
v___x_3615_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3616_ = lean_string_append(v___x_3614_, v___x_3615_);
v___x_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
return v___x_3617_;
}
else
{
lean_object* v_val_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec(v___x_3608_);
v_val_3618_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3609_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_val_3618_);
lean_dec(v___x_3609_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_val_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
else
{
lean_object* v___x_3626_; 
lean_dec(v___x_3602_);
v___x_3626_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__3));
return v___x_3626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* v_args_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Parser_getParserPriority(v_args_3627_);
lean_dec(v_args_3627_);
return v_res_3628_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0));
v___x_3631_ = l_Lean_stringToMessageData(v___x_3630_);
return v___x_3631_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2));
v___x_3634_ = l_Lean_stringToMessageData(v___x_3633_);
return v___x_3634_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3636_ = l_Lean_stringToMessageData(v___x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object* v_name_3640_, uint8_t v_kind_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___y_3651_; 
v___x_3645_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1);
v___x_3646_ = l_Lean_MessageData_ofName(v_name_3640_);
v___x_3647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3645_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
switch(v_kind_3641_)
{
case 0:
{
lean_object* v___x_3658_; 
v___x_3658_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5));
v___y_3651_ = v___x_3658_;
goto v___jp_3650_;
}
case 1:
{
lean_object* v___x_3659_; 
v___x_3659_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6));
v___y_3651_ = v___x_3659_;
goto v___jp_3650_;
}
default: 
{
lean_object* v___x_3660_; 
v___x_3660_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7));
v___y_3651_ = v___x_3660_;
goto v___jp_3650_;
}
}
v___jp_3650_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
lean_inc_ref(v___y_3651_);
v___x_3652_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3652_, 0, v___y_3651_);
v___x_3653_ = l_Lean_MessageData_ofFormat(v___x_3652_);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3649_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3654_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3656_, v___y_3642_, v___y_3643_);
return v___x_3657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object* v_name_3661_, lean_object* v_kind_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
uint8_t v_kind_boxed_3666_; lean_object* v_res_3667_; 
v_kind_boxed_3666_ = lean_unbox(v_kind_3662_);
v_res_3667_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3661_, v_kind_boxed_3666_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3668_, lean_object* v_msg_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_toCold_3673_; lean_object* v_currRecDepth_3674_; lean_object* v_ref_3675_; uint16_t v_optionFlags_3676_; uint8_t v_suppressElabErrors_3677_; uint8_t v_isRecordingDeps_3678_; lean_object* v_ref_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v_toCold_3673_ = lean_ctor_get(v___y_3670_, 0);
v_currRecDepth_3674_ = lean_ctor_get(v___y_3670_, 1);
v_ref_3675_ = lean_ctor_get(v___y_3670_, 2);
v_optionFlags_3676_ = lean_ctor_get_uint16(v___y_3670_, sizeof(void*)*3);
v_suppressElabErrors_3677_ = lean_ctor_get_uint8(v___y_3670_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3678_ = lean_ctor_get_uint8(v___y_3670_, sizeof(void*)*3 + 3);
v_ref_3679_ = l_Lean_replaceRef(v_ref_3668_, v_ref_3675_);
lean_inc(v_currRecDepth_3674_);
lean_inc_ref(v_toCold_3673_);
v___x_3680_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3680_, 0, v_toCold_3673_);
lean_ctor_set(v___x_3680_, 1, v_currRecDepth_3674_);
lean_ctor_set(v___x_3680_, 2, v_ref_3679_);
lean_ctor_set_uint16(v___x_3680_, sizeof(void*)*3, v_optionFlags_3676_);
lean_ctor_set_uint8(v___x_3680_, sizeof(void*)*3 + 2, v_suppressElabErrors_3677_);
lean_ctor_set_uint8(v___x_3680_, sizeof(void*)*3 + 3, v_isRecordingDeps_3678_);
v___x_3681_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_3669_, v___x_3680_, v___y_3671_);
lean_dec_ref_known(v___x_3680_, 3);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3682_, lean_object* v_msg_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3682_, v_msg_3683_, v___y_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v_ref_3682_);
return v_res_3687_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_3690_ = l_Lean_stringToMessageData(v___x_3689_);
return v___x_3690_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_3693_ = l_Lean_stringToMessageData(v___x_3692_);
return v___x_3693_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3695_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_3696_ = l_Lean_stringToMessageData(v___x_3695_);
return v___x_3696_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_3699_ = l_Lean_stringToMessageData(v___x_3698_);
return v___x_3699_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_3702_ = l_Lean_stringToMessageData(v___x_3701_);
return v___x_3702_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3704_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_3705_ = l_Lean_stringToMessageData(v___x_3704_);
return v___x_3705_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_3708_ = l_Lean_stringToMessageData(v___x_3707_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_3709_, lean_object* v_declHint_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v_env_3715_; uint8_t v___x_3716_; 
v___x_3713_ = lean_box(0);
v___x_3714_ = lean_st_ref_get(v___y_3711_);
v_env_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc_ref(v_env_3715_);
lean_dec(v___x_3714_);
v___x_3716_ = l_Lean_Name_isAnonymous(v_declHint_3710_);
if (v___x_3716_ == 0)
{
uint8_t v_isExporting_3717_; 
v_isExporting_3717_ = lean_ctor_get_uint8(v_env_3715_, sizeof(void*)*13);
if (v_isExporting_3717_ == 0)
{
lean_object* v___x_3718_; 
lean_dec_ref(v_env_3715_);
lean_dec(v_declHint_3710_);
v___x_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3718_, 0, v_msg_3709_);
return v___x_3718_;
}
else
{
lean_object* v___x_3719_; uint8_t v___x_3720_; 
lean_inc_ref(v_env_3715_);
v___x_3719_ = l_Lean_Environment_setExporting(v_env_3715_, v___x_3716_);
lean_inc(v_declHint_3710_);
lean_inc_ref(v___x_3719_);
v___x_3720_ = l_Lean_Environment_contains(v___x_3719_, v_declHint_3710_, v_isExporting_3717_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; 
lean_dec_ref(v___x_3719_);
lean_dec_ref(v_env_3715_);
lean_dec(v_declHint_3710_);
v___x_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3721_, 0, v_msg_3709_);
return v___x_3721_;
}
else
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v_c_3727_; lean_object* v___x_3728_; 
v___x_3722_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_3723_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_3724_ = l_Lean_Options_empty;
v___x_3725_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3719_);
lean_ctor_set(v___x_3725_, 1, v___x_3722_);
lean_ctor_set(v___x_3725_, 2, v___x_3723_);
lean_ctor_set(v___x_3725_, 3, v___x_3724_);
lean_inc(v_declHint_3710_);
v___x_3726_ = l_Lean_MessageData_ofConstName(v_declHint_3710_, v___x_3716_);
v_c_3727_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3727_, 0, v___x_3725_);
lean_ctor_set(v_c_3727_, 1, v___x_3726_);
v___x_3728_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3715_, v_declHint_3710_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
lean_dec_ref(v_env_3715_);
lean_dec(v_declHint_3710_);
v___x_3729_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
lean_ctor_set(v___x_3730_, 1, v_c_3727_);
v___x_3731_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_3732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = l_Lean_MessageData_note(v___x_3732_);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v_msg_3709_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
return v___x_3735_;
}
else
{
lean_object* v_val_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3770_; 
v_val_3736_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3738_ = v___x_3728_;
v_isShared_3739_ = v_isSharedCheck_3770_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_val_3736_);
lean_dec(v___x_3728_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3770_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3740_; lean_object* v_moduleNames_3741_; lean_object* v_mod_3742_; uint8_t v___x_3743_; 
v___x_3740_ = l_Lean_Environment_header(v_env_3715_);
lean_dec_ref(v_env_3715_);
v_moduleNames_3741_ = lean_ctor_get(v___x_3740_, 4);
lean_inc_ref(v_moduleNames_3741_);
lean_dec_ref(v___x_3740_);
v_mod_3742_ = lean_array_get(v___x_3713_, v_moduleNames_3741_, v_val_3736_);
lean_dec(v_val_3736_);
lean_dec_ref(v_moduleNames_3741_);
v___x_3743_ = l_Lean_isPrivateName(v_declHint_3710_);
lean_dec(v_declHint_3710_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3744_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_3745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
lean_ctor_set(v___x_3745_, 1, v_c_3727_);
v___x_3746_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3745_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = l_Lean_MessageData_ofName(v_mod_3742_);
v___x_3749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_3751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3749_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = l_Lean_MessageData_note(v___x_3751_);
v___x_3753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3753_, 0, v_msg_3709_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set_tag(v___x_3738_, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3753_);
v___x_3755_ = v___x_3738_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3753_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3757_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3757_);
lean_ctor_set(v___x_3758_, 1, v_c_3727_);
v___x_3759_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_3760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3758_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = l_Lean_MessageData_ofName(v_mod_3742_);
v___x_3762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = l_Lean_MessageData_note(v___x_3764_);
v___x_3766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3766_, 0, v_msg_3709_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set_tag(v___x_3738_, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3766_);
v___x_3768_ = v___x_3738_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
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
}
}
else
{
lean_object* v___x_3771_; 
lean_dec_ref(v_env_3715_);
lean_dec(v_declHint_3710_);
v___x_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3771_, 0, v_msg_3709_);
return v___x_3771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_3772_, lean_object* v_declHint_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3772_, v_declHint_3773_, v___y_3774_);
lean_dec(v___y_3774_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_3777_, lean_object* v_declHint_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3792_; 
v___x_3782_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3777_, v_declHint_3778_, v___y_3780_);
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3785_ = v___x_3782_;
v_isShared_3786_ = v_isSharedCheck_3792_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3792_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3790_; 
v___x_3787_ = l_Lean_unknownIdentifierMessageTag;
v___x_3788_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3787_);
lean_ctor_set(v___x_3788_, 1, v_a_3783_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v___x_3788_);
v___x_3790_ = v___x_3785_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3788_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_3793_, lean_object* v_declHint_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3793_, v_declHint_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3799_, lean_object* v_msg_3800_, lean_object* v_declHint_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v___x_3805_; lean_object* v_a_3806_; lean_object* v___x_3807_; 
v___x_3805_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3800_, v_declHint_3801_, v___y_3802_, v___y_3803_);
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3806_);
lean_dec_ref(v___x_3805_);
v___x_3807_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3799_, v_a_3806_, v___y_3802_, v___y_3803_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3808_, lean_object* v_msg_3809_, lean_object* v_declHint_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3808_, v_msg_3809_, v_declHint_3810_, v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v_ref_3808_);
return v_res_3814_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3815_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_3816_ = l_Lean_stringToMessageData(v___x_3815_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3817_, lean_object* v_constName_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v___x_3822_; uint8_t v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3822_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3823_ = 0;
lean_inc(v_constName_3818_);
v___x_3824_ = l_Lean_MessageData_ofConstName(v_constName_3818_, v___x_3823_);
v___x_3825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3822_);
lean_ctor_set(v___x_3825_, 1, v___x_3824_);
v___x_3826_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3825_);
lean_ctor_set(v___x_3827_, 1, v___x_3826_);
v___x_3828_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3817_, v___x_3827_, v_constName_3818_, v___y_3819_, v___y_3820_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3829_, lean_object* v_constName_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3829_, v_constName_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v_ref_3829_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object* v_constName_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_ref_3839_; lean_object* v___x_3840_; 
v_ref_3839_ = lean_ctor_get(v___y_3836_, 2);
v___x_3840_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3839_, v_constName_3835_, v___y_3836_, v___y_3837_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3841_, v___y_3842_, v___y_3843_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object* v_constName_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v___x_3850_; lean_object* v_env_3851_; uint8_t v___x_3852_; lean_object* v___x_3853_; 
v___x_3850_ = lean_st_ref_get(v___y_3848_);
v_env_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc_ref(v_env_3851_);
lean_dec(v___x_3850_);
v___x_3852_ = 0;
lean_inc(v_constName_3846_);
v___x_3853_ = l_Lean_Environment_find_x3f(v_env_3851_, v_constName_3846_, v___x_3852_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3846_, v___y_3847_, v___y_3848_);
return v___x_3854_;
}
else
{
lean_object* v_val_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec(v_constName_3846_);
v_val_3855_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3853_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_val_3855_);
lean_dec(v___x_3853_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
lean_ctor_set_tag(v___x_3857_, 0);
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_val_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object* v_constName_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3863_, v___y_3864_, v___y_3865_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
return v_res_3867_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1(void){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0));
v___x_3870_ = l_Lean_stringToMessageData(v___x_3869_);
return v___x_3870_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3(void){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2));
v___x_3873_ = l_Lean_stringToMessageData(v___x_3872_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* v_attrName_3874_, lean_object* v_catName_3875_, lean_object* v_declName_3876_, lean_object* v_stx_3877_, uint8_t v_kind_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_Attribute_Builtin_getPrio(v_stx_3877_, v_a_3879_, v_a_3880_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___y_3905_; lean_object* v___y_3906_; uint8_t v___x_3934_; uint8_t v___x_3935_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref_known(v___x_3902_, 1);
v___x_3934_ = 0;
v___x_3935_ = l_Lean_instBEqAttributeKind_beq(v_kind_3878_, v___x_3934_);
if (v___x_3935_ == 0)
{
lean_object* v___x_3936_; 
lean_dec(v_a_3903_);
lean_dec(v_declName_3876_);
lean_dec(v_catName_3875_);
v___x_3936_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_attrName_3874_, v_kind_3878_, v_a_3879_, v_a_3880_);
return v___x_3936_;
}
else
{
lean_dec(v_attrName_3874_);
v___y_3905_ = v_a_3879_;
v___y_3906_ = v_a_3880_;
goto v___jp_3904_;
}
v___jp_3904_:
{
lean_object* v___x_3907_; 
lean_inc(v_declName_3876_);
v___x_3907_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_declName_3876_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v___x_3909_ = l_Lean_ConstantInfo_type(v_a_3908_);
if (lean_obj_tag(v___x_3909_) == 4)
{
lean_object* v_declName_3910_; 
v_declName_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_declName_3910_);
lean_dec_ref_known(v___x_3909_, 2);
if (lean_obj_tag(v_declName_3910_) == 1)
{
lean_object* v_pre_3911_; 
v_pre_3911_ = lean_ctor_get(v_declName_3910_, 0);
lean_inc(v_pre_3911_);
if (lean_obj_tag(v_pre_3911_) == 1)
{
lean_object* v_pre_3912_; 
v_pre_3912_ = lean_ctor_get(v_pre_3911_, 0);
lean_inc(v_pre_3912_);
if (lean_obj_tag(v_pre_3912_) == 1)
{
lean_object* v_pre_3913_; 
v_pre_3913_ = lean_ctor_get(v_pre_3912_, 0);
if (lean_obj_tag(v_pre_3913_) == 0)
{
lean_object* v_str_3914_; lean_object* v_str_3915_; lean_object* v_str_3916_; lean_object* v___x_3917_; uint8_t v___x_3918_; 
v_str_3914_ = lean_ctor_get(v_declName_3910_, 1);
lean_inc_ref(v_str_3914_);
lean_dec_ref_known(v_declName_3910_, 2);
v_str_3915_ = lean_ctor_get(v_pre_3911_, 1);
lean_inc_ref(v_str_3915_);
lean_dec_ref_known(v_pre_3911_, 2);
v_str_3916_ = lean_ctor_get(v_pre_3912_, 1);
lean_inc_ref(v_str_3916_);
lean_dec_ref_known(v_pre_3912_, 2);
v___x_3917_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3918_ = lean_string_dec_eq(v_str_3916_, v___x_3917_);
lean_dec_ref(v_str_3916_);
if (v___x_3918_ == 0)
{
lean_dec_ref(v_str_3915_);
lean_dec_ref(v_str_3914_);
lean_dec(v_a_3903_);
lean_dec(v_catName_3875_);
v___y_3889_ = v_a_3908_;
v___y_3890_ = v___y_3905_;
v___y_3891_ = v___y_3906_;
goto v___jp_3888_;
}
else
{
lean_object* v___x_3919_; uint8_t v___x_3920_; 
v___x_3919_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3920_ = lean_string_dec_eq(v_str_3915_, v___x_3919_);
lean_dec_ref(v_str_3915_);
if (v___x_3920_ == 0)
{
lean_dec_ref(v_str_3914_);
lean_dec(v_a_3903_);
lean_dec(v_catName_3875_);
v___y_3889_ = v_a_3908_;
v___y_3890_ = v___y_3905_;
v___y_3891_ = v___y_3906_;
goto v___jp_3888_;
}
else
{
lean_object* v___x_3921_; uint8_t v___x_3922_; 
v___x_3921_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_3922_ = lean_string_dec_eq(v_str_3914_, v___x_3921_);
if (v___x_3922_ == 0)
{
uint8_t v___x_3923_; 
v___x_3923_ = lean_string_dec_eq(v_str_3914_, v___x_3919_);
lean_dec_ref(v_str_3914_);
if (v___x_3923_ == 0)
{
lean_dec(v_a_3903_);
lean_dec(v_catName_3875_);
v___y_3889_ = v_a_3908_;
v___y_3890_ = v___y_3905_;
v___y_3891_ = v___y_3906_;
goto v___jp_3888_;
}
else
{
lean_object* v___x_3924_; 
lean_dec(v_a_3908_);
lean_inc(v_declName_3876_);
lean_inc(v_catName_3875_);
v___x_3924_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3875_, v_declName_3876_, v_a_3903_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_dec_ref_known(v___x_3924_, 1);
v___y_3883_ = v___y_3905_;
v___y_3884_ = v___y_3906_;
goto v___jp_3882_;
}
else
{
lean_dec(v_declName_3876_);
lean_dec(v_catName_3875_);
return v___x_3924_;
}
}
}
else
{
lean_object* v___x_3925_; 
lean_dec_ref(v_str_3914_);
lean_dec(v_a_3908_);
lean_inc(v_declName_3876_);
lean_inc(v_catName_3875_);
v___x_3925_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3875_, v_declName_3876_, v_a_3903_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_dec_ref_known(v___x_3925_, 1);
v___y_3883_ = v___y_3905_;
v___y_3884_ = v___y_3906_;
goto v___jp_3882_;
}
else
{
lean_dec(v_declName_3876_);
lean_dec(v_catName_3875_);
return v___x_3925_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3912_, 2);
lean_dec_ref_known(v_pre_3911_, 2);
lean_dec_ref_known(v_declName_3910_, 2);
lean_dec(v_a_3903_);
lean_dec(v_catName_3875_);
v___y_3889_ = v_a_3908_;
v___y_3890_ = v___y_3905_;
v___y_3891_ = v___y_3906_;
goto v___jp_3888_;
}
}
else
{
lean_dec_ref_known(v_pre_3911_, 2);
lean_dec(v_pre_3912_);
lean_dec_ref_known(v_declName_3910_, 2);
lean_dec(v_a_3903_);
lean_dec(v_catName_3875_);
v___y_3889_ = v_a_3908_;
v___y_3890_ = v___y_3905_;
v___y_3891_ = v___y_3906_;
goto v___jp_3888_;
}
}
else
{
lean_dec_ref_known(v_declName_3910_, 2);
lean_dec(v_pre_3911_);
lean_dec(v_a_3903_);
lean_dec(v_catName_3875_);
v___y_3889_ = v_a_3908_;
v___y_3890_ = v___y_3905_;
v___y_3891_ = v___y_3906_;
goto v___jp_3888_;
}
}
else
{
lean_dec(v_declName_3910_);
lean_dec(v_a_3903_);
lean_dec(v_catName_3875_);
v___y_3889_ = v_a_3908_;
v___y_3890_ = v___y_3905_;
v___y_3891_ = v___y_3906_;
goto v___jp_3888_;
}
}
else
{
lean_dec_ref(v___x_3909_);
lean_dec(v_a_3903_);
lean_dec(v_catName_3875_);
v___y_3889_ = v_a_3908_;
v___y_3890_ = v___y_3905_;
v___y_3891_ = v___y_3906_;
goto v___jp_3888_;
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec(v_a_3903_);
lean_dec(v_declName_3876_);
lean_dec(v_catName_3875_);
v_a_3926_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3907_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3907_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec(v_declName_3876_);
lean_dec(v_catName_3875_);
lean_dec(v_attrName_3874_);
v_a_3937_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3902_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3902_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
v___jp_3882_:
{
lean_object* v___x_3885_; 
lean_inc(v_declName_3876_);
v___x_3885_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_3876_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3885_) == 0)
{
uint8_t v___x_3886_; lean_object* v___x_3887_; 
lean_dec_ref_known(v___x_3885_, 1);
v___x_3886_ = 1;
v___x_3887_ = l_Lean_Parser_runParserAttributeHooks(v_catName_3875_, v_declName_3876_, v___x_3886_, v___y_3883_, v___y_3884_);
return v___x_3887_;
}
else
{
lean_dec(v_declName_3876_);
lean_dec(v_catName_3875_);
return v___x_3885_;
}
}
v___jp_3888_:
{
lean_object* v___x_3892_; uint8_t v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3892_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
v___x_3893_ = 0;
v___x_3894_ = l_Lean_MessageData_ofConstName(v_declName_3876_, v___x_3893_);
v___x_3895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3892_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
v___x_3896_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
v___x_3897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3895_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___x_3898_ = l_Lean_ConstantInfo_type(v___y_3889_);
lean_dec_ref(v___y_3889_);
v___x_3899_ = l_Lean_indentExpr(v___x_3898_);
v___x_3900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3897_);
lean_ctor_set(v___x_3900_, 1, v___x_3899_);
v___x_3901_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3900_, v___y_3890_, v___y_3891_);
return v___x_3901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* v_attrName_3945_, lean_object* v_catName_3946_, lean_object* v_declName_3947_, lean_object* v_stx_3948_, lean_object* v_kind_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_){
_start:
{
uint8_t v_kind_boxed_3953_; lean_object* v_res_3954_; 
v_kind_boxed_3953_ = lean_unbox(v_kind_3949_);
v_res_3954_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3945_, v_catName_3946_, v_declName_3947_, v_stx_3948_, v_kind_boxed_3953_, v_a_3950_, v_a_3951_);
lean_dec(v_a_3951_);
lean_dec_ref(v_a_3950_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object* v_00_u03b1_3955_, lean_object* v_name_3956_, uint8_t v_kind_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v___x_3961_; 
v___x_3961_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3956_, v_kind_3957_, v___y_3958_, v___y_3959_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b1_3962_, lean_object* v_name_3963_, lean_object* v_kind_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
uint8_t v_kind_boxed_3968_; lean_object* v_res_3969_; 
v_kind_boxed_3968_ = lean_unbox(v_kind_3964_);
v_res_3969_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(v_00_u03b1_3962_, v_name_3963_, v_kind_boxed_3968_, v___y_3965_, v___y_3966_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object* v_00_u03b1_3970_, lean_object* v_constName_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v___x_3975_; 
v___x_3975_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3971_, v___y_3972_, v___y_3973_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3976_, lean_object* v_constName_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(v_00_u03b1_3976_, v_constName_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3982_, lean_object* v_ref_3983_, lean_object* v_constName_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3983_, v_constName_3984_, v___y_3985_, v___y_3986_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3989_, lean_object* v_ref_3990_, lean_object* v_constName_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(v_00_u03b1_3989_, v_ref_3990_, v_constName_3991_, v___y_3992_, v___y_3993_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v_ref_3990_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3996_, lean_object* v_ref_3997_, lean_object* v_msg_3998_, lean_object* v_declHint_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3997_, v_msg_3998_, v_declHint_3999_, v___y_4000_, v___y_4001_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4004_, lean_object* v_ref_4005_, lean_object* v_msg_4006_, lean_object* v_declHint_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4004_, v_ref_4005_, v_msg_4006_, v_declHint_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v_ref_4005_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_4012_, lean_object* v_declHint_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v___x_4017_; 
v___x_4017_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_4012_, v_declHint_4013_, v___y_4015_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_4018_, lean_object* v_declHint_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_4018_, v_declHint_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_4024_, lean_object* v_ref_4025_, lean_object* v_msg_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4025_, v_msg_4026_, v___y_4027_, v___y_4028_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_4031_, lean_object* v_ref_4032_, lean_object* v_msg_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_4031_, v_ref_4032_, v_msg_4033_, v___y_4034_, v___y_4035_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v_ref_4032_);
return v_res_4037_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2(void){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0));
v___x_4045_ = l_Lean_mkAtom(v___x_4044_);
return v___x_4045_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3(void){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4046_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2);
v___x_4047_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4048_ = lean_array_push(v___x_4047_, v___x_4046_);
return v___x_4048_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8(void){
_start:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7));
v___x_4058_ = l_Lean_mkAtom(v___x_4057_);
return v___x_4058_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9(void){
_start:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4059_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8);
v___x_4060_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4061_ = lean_array_push(v___x_4060_, v___x_4059_);
return v___x_4061_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4062_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9);
v___x_4063_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6));
v___x_4064_ = lean_box(2);
v___x_4065_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
lean_ctor_set(v___x_4065_, 1, v___x_4063_);
lean_ctor_set(v___x_4065_, 2, v___x_4062_);
return v___x_4065_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4066_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10);
v___x_4067_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3);
v___x_4068_ = lean_array_push(v___x_4067_, v___x_4066_);
return v___x_4068_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4069_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11);
v___x_4070_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1));
v___x_4071_ = lean_box(2);
v___x_4072_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
lean_ctor_set(v___x_4072_, 1, v___x_4070_);
lean_ctor_set(v___x_4072_, 2, v___x_4069_);
return v___x_4072_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4073_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12);
v___x_4074_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4075_ = lean_array_push(v___x_4074_, v___x_4073_);
return v___x_4075_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14(void){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4076_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13);
v___x_4077_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_4078_ = lean_box(2);
v___x_4079_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
lean_ctor_set(v___x_4079_, 1, v___x_4077_);
lean_ctor_set(v___x_4079_, 2, v___x_4076_);
return v___x_4079_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15(void){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4080_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14);
v___x_4081_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4082_ = lean_array_push(v___x_4081_, v___x_4080_);
return v___x_4082_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4083_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15);
v___x_4084_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_4085_ = lean_box(2);
v___x_4086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
lean_ctor_set(v___x_4086_, 1, v___x_4084_);
lean_ctor_set(v___x_4086_, 2, v___x_4083_);
return v___x_4086_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4087_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16);
v___x_4088_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4089_ = lean_array_push(v___x_4088_, v___x_4087_);
return v___x_4089_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4090_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17);
v___x_4091_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_4092_ = lean_box(2);
v___x_4093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4092_);
lean_ctor_set(v___x_4093_, 1, v___x_4091_);
lean_ctor_set(v___x_4093_, 2, v___x_4090_);
return v___x_4093_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4094_; 
v___x_4094_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object* v_attrName_4095_, lean_object* v_decl_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4100_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_4101_ = l_Lean_MessageData_ofName(v_attrName_4095_);
v___x_4102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4100_);
lean_ctor_set(v___x_4102_, 1, v___x_4101_);
v___x_4103_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_4104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4102_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4104_, v___y_4097_, v___y_4098_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object* v_attrName_4106_, lean_object* v_decl_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_4106_, v_decl_4107_, v___y_4108_, v___y_4109_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v_decl_4107_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object* v_attrName_4112_, lean_object* v_catName_4113_, lean_object* v_declName_4114_, lean_object* v_stx_4115_, uint8_t v_kind_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_4112_, v_catName_4113_, v_declName_4114_, v_stx_4115_, v_kind_4116_, v___y_4117_, v___y_4118_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object* v_attrName_4121_, lean_object* v_catName_4122_, lean_object* v_declName_4123_, lean_object* v_stx_4124_, lean_object* v_kind_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
uint8_t v_kind_boxed_4129_; lean_object* v_res_4130_; 
v_kind_boxed_4129_ = lean_unbox(v_kind_4125_);
v_res_4130_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_4121_, v_catName_4122_, v_declName_4123_, v_stx_4124_, v_kind_boxed_4129_, v___y_4126_, v___y_4127_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
return v_res_4130_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1(void){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__0));
v___x_4133_ = lean_mk_io_user_error(v___x_4132_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* v_attrName_4136_, lean_object* v_declName_4137_, uint8_t v_behavior_4138_, lean_object* v_ref_4139_){
_start:
{
if (lean_obj_tag(v_declName_4137_) == 1)
{
lean_object* v_pre_4144_; 
v_pre_4144_ = lean_ctor_get(v_declName_4137_, 0);
if (lean_obj_tag(v_pre_4144_) == 1)
{
lean_object* v_pre_4145_; 
v_pre_4145_ = lean_ctor_get(v_pre_4144_, 0);
if (lean_obj_tag(v_pre_4145_) == 1)
{
lean_object* v_pre_4146_; 
v_pre_4146_ = lean_ctor_get(v_pre_4145_, 0);
if (lean_obj_tag(v_pre_4146_) == 1)
{
lean_object* v_pre_4147_; 
v_pre_4147_ = lean_ctor_get(v_pre_4146_, 0);
if (lean_obj_tag(v_pre_4147_) == 0)
{
lean_object* v_str_4148_; lean_object* v_str_4149_; lean_object* v_str_4150_; lean_object* v_str_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; 
v_str_4148_ = lean_ctor_get(v_declName_4137_, 1);
v_str_4149_ = lean_ctor_get(v_pre_4144_, 1);
v_str_4150_ = lean_ctor_get(v_pre_4145_, 1);
v_str_4151_ = lean_ctor_get(v_pre_4146_, 1);
v___x_4152_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_4153_ = lean_string_dec_eq(v_str_4151_, v___x_4152_);
if (v___x_4153_ == 0)
{
lean_dec_ref_known(v_declName_4137_, 2);
lean_dec(v_ref_4139_);
lean_dec(v_attrName_4136_);
goto v___jp_4141_;
}
else
{
lean_object* v___x_4154_; uint8_t v___x_4155_; 
v___x_4154_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_4155_ = lean_string_dec_eq(v_str_4150_, v___x_4154_);
if (v___x_4155_ == 0)
{
lean_dec_ref_known(v_declName_4137_, 2);
lean_dec(v_ref_4139_);
lean_dec(v_attrName_4136_);
goto v___jp_4141_;
}
else
{
lean_object* v___x_4156_; uint8_t v___x_4157_; 
v___x_4156_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__2));
v___x_4157_ = lean_string_dec_eq(v_str_4149_, v___x_4156_);
if (v___x_4157_ == 0)
{
lean_dec_ref_known(v_declName_4137_, 2);
lean_dec(v_ref_4139_);
lean_dec(v_attrName_4136_);
goto v___jp_4141_;
}
else
{
lean_object* v___f_4158_; lean_object* v___x_4159_; lean_object* v_catName_4160_; lean_object* v___f_4161_; lean_object* v___x_4162_; 
lean_inc_n(v_attrName_4136_, 2);
v___f_4158_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4158_, 0, v_attrName_4136_);
v___x_4159_ = lean_box(0);
lean_inc_ref(v_str_4148_);
v_catName_4160_ = l_Lean_Name_str___override(v___x_4159_, v_str_4148_);
lean_inc(v_catName_4160_);
v___f_4161_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed), 8, 2);
lean_closure_set(v___f_4161_, 0, v_attrName_4136_);
lean_closure_set(v___f_4161_, 1, v_catName_4160_);
v___x_4162_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_4160_, v_declName_4137_, v_behavior_4138_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v___x_4163_; uint8_t v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
lean_dec_ref_known(v___x_4162_, 1);
v___x_4163_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__3));
v___x_4164_ = 1;
v___x_4165_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4165_, 0, v_ref_4139_);
lean_ctor_set(v___x_4165_, 1, v_attrName_4136_);
lean_ctor_set(v___x_4165_, 2, v___x_4163_);
lean_ctor_set_uint8(v___x_4165_, sizeof(void*)*3, v___x_4164_);
v___x_4166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
lean_ctor_set(v___x_4166_, 1, v___f_4161_);
lean_ctor_set(v___x_4166_, 2, v___f_4158_);
v___x_4167_ = l_Lean_registerBuiltinAttribute(v___x_4166_);
return v___x_4167_;
}
else
{
lean_dec_ref(v___f_4161_);
lean_dec_ref(v___f_4158_);
lean_dec(v_ref_4139_);
lean_dec(v_attrName_4136_);
return v___x_4162_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_declName_4137_, 2);
lean_dec(v_ref_4139_);
lean_dec(v_attrName_4136_);
goto v___jp_4141_;
}
}
else
{
lean_dec_ref_known(v_declName_4137_, 2);
lean_dec(v_ref_4139_);
lean_dec(v_attrName_4136_);
goto v___jp_4141_;
}
}
else
{
lean_dec_ref_known(v_declName_4137_, 2);
lean_dec(v_ref_4139_);
lean_dec(v_attrName_4136_);
goto v___jp_4141_;
}
}
else
{
lean_dec_ref_known(v_declName_4137_, 2);
lean_dec(v_ref_4139_);
lean_dec(v_attrName_4136_);
goto v___jp_4141_;
}
}
else
{
lean_dec(v_ref_4139_);
lean_dec(v_declName_4137_);
lean_dec(v_attrName_4136_);
goto v___jp_4141_;
}
v___jp_4141_:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___closed__1, &l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
v___x_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
return v___x_4143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* v_attrName_4168_, lean_object* v_declName_4169_, lean_object* v_behavior_4170_, lean_object* v_ref_4171_, lean_object* v_a_4172_){
_start:
{
uint8_t v_behavior_boxed_4173_; lean_object* v_res_4174_; 
v_behavior_boxed_4173_ = lean_unbox(v_behavior_4170_);
v_res_4174_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_4168_, v_declName_4169_, v_behavior_boxed_4173_, v_ref_4171_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object* v_kind_4175_, lean_object* v_x_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v___x_4180_; lean_object* v_env_4181_; lean_object* v_nextMacroScope_4182_; lean_object* v_ngen_4183_; lean_object* v_auxDeclNGen_4184_; lean_object* v_traceState_4185_; lean_object* v_recordedDeps_4186_; lean_object* v_messages_4187_; lean_object* v_infoState_4188_; lean_object* v_snapshotTasks_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4201_; 
v___x_4180_ = lean_st_ref_take(v___y_4178_);
v_env_4181_ = lean_ctor_get(v___x_4180_, 0);
v_nextMacroScope_4182_ = lean_ctor_get(v___x_4180_, 1);
v_ngen_4183_ = lean_ctor_get(v___x_4180_, 2);
v_auxDeclNGen_4184_ = lean_ctor_get(v___x_4180_, 3);
v_traceState_4185_ = lean_ctor_get(v___x_4180_, 4);
v_recordedDeps_4186_ = lean_ctor_get(v___x_4180_, 6);
v_messages_4187_ = lean_ctor_get(v___x_4180_, 7);
v_infoState_4188_ = lean_ctor_get(v___x_4180_, 8);
v_snapshotTasks_4189_ = lean_ctor_get(v___x_4180_, 9);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4201_ == 0)
{
lean_object* v_unused_4202_; 
v_unused_4202_ = lean_ctor_get(v___x_4180_, 5);
lean_dec(v_unused_4202_);
v___x_4191_ = v___x_4180_;
v_isShared_4192_ = v_isSharedCheck_4201_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_snapshotTasks_4189_);
lean_inc(v_infoState_4188_);
lean_inc(v_messages_4187_);
lean_inc(v_recordedDeps_4186_);
lean_inc(v_traceState_4185_);
lean_inc(v_auxDeclNGen_4184_);
lean_inc(v_ngen_4183_);
lean_inc(v_nextMacroScope_4182_);
lean_inc(v_env_4181_);
lean_dec(v___x_4180_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4201_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4197_; 
v___x_4193_ = lean_box(0);
v___x_4194_ = l_Lean_Parser_addSyntaxNodeKind(v_env_4181_, v_kind_4175_);
v___x_4195_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 5, v___x_4195_);
lean_ctor_set(v___x_4191_, 0, v___x_4194_);
v___x_4197_ = v___x_4191_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4194_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v_nextMacroScope_4182_);
lean_ctor_set(v_reuseFailAlloc_4200_, 2, v_ngen_4183_);
lean_ctor_set(v_reuseFailAlloc_4200_, 3, v_auxDeclNGen_4184_);
lean_ctor_set(v_reuseFailAlloc_4200_, 4, v_traceState_4185_);
lean_ctor_set(v_reuseFailAlloc_4200_, 5, v___x_4195_);
lean_ctor_set(v_reuseFailAlloc_4200_, 6, v_recordedDeps_4186_);
lean_ctor_set(v_reuseFailAlloc_4200_, 7, v_messages_4187_);
lean_ctor_set(v_reuseFailAlloc_4200_, 8, v_infoState_4188_);
lean_ctor_set(v_reuseFailAlloc_4200_, 9, v_snapshotTasks_4189_);
v___x_4197_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = lean_st_ref_put(v___y_4178_, v___x_4197_);
v___x_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4193_);
return v___x_4199_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object* v_kind_4203_, lean_object* v_x_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_4203_, v_x_4204_, v___y_4205_, v___y_4206_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_4209_, lean_object* v_keys_4210_, lean_object* v_vals_4211_, lean_object* v_i_4212_, lean_object* v_acc_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; uint8_t v___x_4218_; 
v___x_4217_ = lean_array_get_size(v_keys_4210_);
v___x_4218_ = lean_nat_dec_lt(v_i_4212_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4219_; 
lean_dec(v_i_4212_);
lean_dec_ref(v_f_4209_);
v___x_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4219_, 0, v_acc_4213_);
return v___x_4219_;
}
else
{
lean_object* v_k_4220_; lean_object* v_v_4221_; lean_object* v___x_4222_; 
v_k_4220_ = lean_array_fget_borrowed(v_keys_4210_, v_i_4212_);
v_v_4221_ = lean_array_fget_borrowed(v_vals_4211_, v_i_4212_);
lean_inc_ref(v_f_4209_);
lean_inc(v___y_4215_);
lean_inc_ref(v___y_4214_);
lean_inc(v_v_4221_);
lean_inc(v_k_4220_);
v___x_4222_ = lean_apply_6(v_f_4209_, v_acc_4213_, v_k_4220_, v_v_4221_, v___y_4214_, v___y_4215_, lean_box(0));
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref_known(v___x_4222_, 1);
v___x_4224_ = lean_unsigned_to_nat(1u);
v___x_4225_ = lean_nat_add(v_i_4212_, v___x_4224_);
lean_dec(v_i_4212_);
v_i_4212_ = v___x_4225_;
v_acc_4213_ = v_a_4223_;
goto _start;
}
else
{
lean_dec(v_i_4212_);
lean_dec_ref(v_f_4209_);
return v___x_4222_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_4227_, lean_object* v_keys_4228_, lean_object* v_vals_4229_, lean_object* v_i_4230_, lean_object* v_acc_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4227_, v_keys_4228_, v_vals_4229_, v_i_4230_, v_acc_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec_ref(v_vals_4229_);
lean_dec_ref(v_keys_4228_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_4236_, lean_object* v_as_4237_, size_t v_i_4238_, size_t v_stop_4239_, lean_object* v_b_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v_a_4245_; lean_object* v___y_4250_; uint8_t v___x_4252_; 
v___x_4252_ = lean_usize_dec_eq(v_i_4238_, v_stop_4239_);
if (v___x_4252_ == 0)
{
lean_object* v___x_4253_; 
v___x_4253_ = lean_array_uget_borrowed(v_as_4237_, v_i_4238_);
switch(lean_obj_tag(v___x_4253_))
{
case 0:
{
lean_object* v_key_4254_; lean_object* v_val_4255_; lean_object* v___x_4256_; 
v_key_4254_ = lean_ctor_get(v___x_4253_, 0);
v_val_4255_ = lean_ctor_get(v___x_4253_, 1);
lean_inc_ref(v_f_4236_);
lean_inc(v___y_4242_);
lean_inc_ref(v___y_4241_);
lean_inc(v_val_4255_);
lean_inc(v_key_4254_);
v___x_4256_ = lean_apply_6(v_f_4236_, v_b_4240_, v_key_4254_, v_val_4255_, v___y_4241_, v___y_4242_, lean_box(0));
v___y_4250_ = v___x_4256_;
goto v___jp_4249_;
}
case 1:
{
lean_object* v_node_4257_; lean_object* v___x_4258_; 
v_node_4257_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_node_4257_);
lean_inc_ref(v_f_4236_);
v___x_4258_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4236_, v_node_4257_, v_b_4240_, v___y_4241_, v___y_4242_);
v___y_4250_ = v___x_4258_;
goto v___jp_4249_;
}
default: 
{
v_a_4245_ = v_b_4240_;
goto v___jp_4244_;
}
}
}
else
{
lean_object* v___x_4259_; 
lean_dec_ref(v_f_4236_);
v___x_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4259_, 0, v_b_4240_);
return v___x_4259_;
}
v___jp_4244_:
{
size_t v___x_4246_; size_t v___x_4247_; 
v___x_4246_ = ((size_t)1ULL);
v___x_4247_ = lean_usize_add(v_i_4238_, v___x_4246_);
v_i_4238_ = v___x_4247_;
v_b_4240_ = v_a_4245_;
goto _start;
}
v___jp_4249_:
{
if (lean_obj_tag(v___y_4250_) == 0)
{
lean_object* v_a_4251_; 
v_a_4251_ = lean_ctor_get(v___y_4250_, 0);
lean_inc(v_a_4251_);
lean_dec_ref_known(v___y_4250_, 1);
v_a_4245_ = v_a_4251_;
goto v___jp_4244_;
}
else
{
lean_dec_ref(v_f_4236_);
return v___y_4250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object* v_f_4260_, lean_object* v_x_4261_, lean_object* v_x_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_){
_start:
{
if (lean_obj_tag(v_x_4261_) == 0)
{
lean_object* v_es_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4279_; 
v_es_4266_ = lean_ctor_get(v_x_4261_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v_x_4261_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4268_ = v_x_4261_;
v_isShared_4269_ = v_isSharedCheck_4279_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_es_4266_);
lean_dec(v_x_4261_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4279_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; uint8_t v___x_4272_; 
v___x_4270_ = lean_unsigned_to_nat(0u);
v___x_4271_ = lean_array_get_size(v_es_4266_);
v___x_4272_ = lean_nat_dec_lt(v___x_4270_, v___x_4271_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4274_; 
lean_dec_ref(v_es_4266_);
lean_dec_ref(v_f_4260_);
if (v_isShared_4269_ == 0)
{
lean_ctor_set(v___x_4268_, 0, v_x_4262_);
v___x_4274_ = v___x_4268_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_x_4262_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
else
{
size_t v___x_4276_; size_t v___x_4277_; lean_object* v___x_4278_; 
lean_del_object(v___x_4268_);
v___x_4276_ = ((size_t)0ULL);
v___x_4277_ = lean_usize_of_nat(v___x_4271_);
v___x_4278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4260_, v_es_4266_, v___x_4276_, v___x_4277_, v_x_4262_, v___y_4263_, v___y_4264_);
lean_dec_ref(v_es_4266_);
return v___x_4278_;
}
}
}
else
{
lean_object* v_ks_4280_; lean_object* v_vs_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v_ks_4280_ = lean_ctor_get(v_x_4261_, 0);
lean_inc_ref(v_ks_4280_);
v_vs_4281_ = lean_ctor_get(v_x_4261_, 1);
lean_inc_ref(v_vs_4281_);
lean_dec_ref_known(v_x_4261_, 2);
v___x_4282_ = lean_unsigned_to_nat(0u);
v___x_4283_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4260_, v_ks_4280_, v_vs_4281_, v___x_4282_, v_x_4262_, v___y_4263_, v___y_4264_);
lean_dec_ref(v_vs_4281_);
lean_dec_ref(v_ks_4280_);
return v___x_4283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_4284_, lean_object* v_x_4285_, lean_object* v_x_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4284_, v_x_4285_, v_x_4286_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_4291_, lean_object* v_as_4292_, lean_object* v_i_4293_, lean_object* v_stop_4294_, lean_object* v_b_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
size_t v_i_boxed_4299_; size_t v_stop_boxed_4300_; lean_object* v_res_4301_; 
v_i_boxed_4299_ = lean_unbox_usize(v_i_4293_);
lean_dec(v_i_4293_);
v_stop_boxed_4300_ = lean_unbox_usize(v_stop_4294_);
lean_dec(v_stop_4294_);
v_res_4301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4291_, v_as_4292_, v_i_boxed_4299_, v_stop_boxed_4300_, v_b_4295_, v___y_4296_, v___y_4297_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec_ref(v_as_4292_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object* v_f_4302_, lean_object* v_x_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v___x_4309_; 
lean_inc(v___y_4307_);
lean_inc_ref(v___y_4306_);
v___x_4309_ = lean_apply_5(v_f_4302_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, lean_box(0));
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object* v_f_4310_, lean_object* v_x_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4310_, v_x_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object* v_map_4318_, lean_object* v_f_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v___f_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___f_4323_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4323_, 0, v_f_4319_);
v___x_4324_ = lean_box(0);
v___x_4325_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v___f_4323_, v_map_4318_, v___x_4324_, v___y_4320_, v___y_4321_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object* v_map_4326_, lean_object* v_f_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4326_, v_f_4327_, v___y_4328_, v___y_4329_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
return v_res_4331_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0));
v___x_4334_ = l_Lean_stringToMessageData(v___x_4333_);
return v___x_4334_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_4336_ = l_Lean_stringToMessageData(v___x_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t v_attrKind_4337_, lean_object* v_declName_4338_, lean_object* v_as_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
if (lean_obj_tag(v_as_4339_) == 0)
{
lean_object* v___x_4343_; lean_object* v___x_4344_; 
lean_dec(v_declName_4338_);
v___x_4343_ = lean_box(0);
v___x_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4343_);
return v___x_4344_;
}
else
{
lean_object* v_head_4345_; lean_object* v_tail_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4373_; 
v_head_4345_ = lean_ctor_get(v_as_4339_, 0);
v_tail_4346_ = lean_ctor_get(v_as_4339_, 1);
v_isSharedCheck_4373_ = !lean_is_exclusive(v_as_4339_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4348_ = v_as_4339_;
v_isShared_4349_ = v_isSharedCheck_4373_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_tail_4346_);
lean_inc(v_head_4345_);
lean_dec(v_as_4339_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4373_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
uint8_t v___x_4350_; lean_object* v___x_4351_; 
v___x_4350_ = 0;
v___x_4351_ = l_Lean_Parser_addToken(v_head_4345_, v_attrKind_4337_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_dec_ref_known(v___x_4351_, 1);
lean_del_object(v___x_4348_);
v_as_4339_ = v_tail_4346_;
goto _start;
}
else
{
lean_object* v_a_4353_; uint8_t v___x_4354_; 
lean_dec(v_tail_4346_);
v_a_4353_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4353_);
v___x_4354_ = l_Lean_Exception_isInterrupt(v_a_4353_);
if (v___x_4354_ == 0)
{
uint8_t v___x_4355_; 
lean_inc(v_a_4353_);
v___x_4355_ = l_Lean_Exception_isRuntime(v_a_4353_);
if (v___x_4355_ == 0)
{
if (lean_obj_tag(v_a_4353_) == 0)
{
lean_object* v_msg_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4371_; 
lean_dec_ref_known(v___x_4351_, 1);
v_msg_4356_ = lean_ctor_get(v_a_4353_, 1);
v_isSharedCheck_4371_ = !lean_is_exclusive(v_a_4353_);
if (v_isSharedCheck_4371_ == 0)
{
lean_object* v_unused_4372_; 
v_unused_4372_ = lean_ctor_get(v_a_4353_, 0);
lean_dec(v_unused_4372_);
v___x_4358_ = v_a_4353_;
v_isShared_4359_ = v_isSharedCheck_4371_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_msg_4356_);
lean_dec(v_a_4353_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4371_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4363_; 
v___x_4360_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1);
v___x_4361_ = l_Lean_MessageData_ofConstName(v_declName_4338_, v___x_4350_);
if (v_isShared_4359_ == 0)
{
lean_ctor_set_tag(v___x_4358_, 7);
lean_ctor_set(v___x_4358_, 1, v___x_4361_);
lean_ctor_set(v___x_4358_, 0, v___x_4360_);
v___x_4363_ = v___x_4358_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4360_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v___x_4361_);
v___x_4363_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4364_; lean_object* v___x_4366_; 
v___x_4364_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2);
if (v_isShared_4349_ == 0)
{
lean_ctor_set_tag(v___x_4348_, 7);
lean_ctor_set(v___x_4348_, 1, v___x_4364_);
lean_ctor_set(v___x_4348_, 0, v___x_4363_);
v___x_4366_ = v___x_4348_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4363_);
lean_ctor_set(v_reuseFailAlloc_4369_, 1, v___x_4364_);
v___x_4366_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4366_);
lean_ctor_set(v___x_4367_, 1, v_msg_4356_);
v___x_4368_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4367_, v___y_4340_, v___y_4341_);
return v___x_4368_;
}
}
}
}
else
{
lean_dec(v_a_4353_);
lean_del_object(v___x_4348_);
lean_dec(v_declName_4338_);
return v___x_4351_;
}
}
else
{
lean_dec(v_a_4353_);
lean_del_object(v___x_4348_);
lean_dec(v_declName_4338_);
return v___x_4351_;
}
}
else
{
lean_dec(v_a_4353_);
lean_del_object(v___x_4348_);
lean_dec(v_declName_4338_);
return v___x_4351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object* v_attrKind_4374_, lean_object* v_declName_4375_, lean_object* v_as_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_){
_start:
{
uint8_t v_attrKind_boxed_4380_; lean_object* v_res_4381_; 
v_attrKind_boxed_4380_ = lean_unbox(v_attrKind_4374_);
v_res_4381_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_boxed_4380_, v_declName_4375_, v_as_4376_, v___y_4377_, v___y_4378_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object* v_catName_4383_, lean_object* v_declName_4384_, lean_object* v_stx_4385_, uint8_t v_attrKind_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_){
_start:
{
lean_object* v___f_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___f_4390_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0));
v___x_4391_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4392_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4385_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; lean_object* v___x_4394_; lean_object* v_env_4395_; lean_object* v___x_4396_; lean_object* v_ext_4397_; lean_object* v_toEnvExtension_4398_; lean_object* v_asyncMode_4399_; uint8_t v___x_4400_; lean_object* v___x_4401_; lean_object* v_categories_4402_; lean_object* v___x_4403_; lean_object* v_env_4404_; lean_object* v_ref_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_a_4393_);
lean_dec_ref_known(v___x_4392_, 1);
v___x_4394_ = lean_st_ref_get(v_a_4388_);
v_env_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc_ref(v_env_4395_);
lean_dec(v___x_4394_);
v___x_4396_ = l_Lean_Parser_parserExtension;
v_ext_4397_ = lean_ctor_get(v___x_4396_, 1);
v_toEnvExtension_4398_ = lean_ctor_get(v_ext_4397_, 0);
v_asyncMode_4399_ = lean_ctor_get(v_toEnvExtension_4398_, 2);
v___x_4400_ = 0;
v___x_4401_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4391_, v___x_4396_, v_env_4395_, v_asyncMode_4399_, v___x_4400_);
v_categories_4402_ = lean_ctor_get(v___x_4401_, 2);
lean_inc_ref_n(v_categories_4402_, 2);
lean_dec(v___x_4401_);
v___x_4403_ = lean_st_ref_get(v_a_4388_);
v_env_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc_ref(v_env_4404_);
lean_dec(v___x_4403_);
v_ref_4405_ = lean_ctor_get(v_a_4387_, 2);
v___x_4406_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4387_);
v___x_4407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4407_, 0, v_env_4404_);
lean_ctor_set(v___x_4407_, 1, v___x_4406_);
lean_inc(v_declName_4384_);
v___x_4408_ = l_Lean_Parser_mkParserOfConstant(v_categories_4402_, v_declName_4384_, v___x_4407_);
lean_dec_ref_known(v___x_4407_, 2);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v_snd_4410_; lean_object* v_info_4411_; lean_object* v_fst_4412_; lean_object* v_collectTokens_4413_; lean_object* v_collectKinds_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref_known(v___x_4408_, 1);
v_snd_4410_ = lean_ctor_get(v_a_4409_, 1);
lean_inc(v_snd_4410_);
v_info_4411_ = lean_ctor_get(v_snd_4410_, 0);
v_fst_4412_ = lean_ctor_get(v_a_4409_, 0);
lean_inc(v_fst_4412_);
lean_dec(v_a_4409_);
v_collectTokens_4413_ = lean_ctor_get(v_info_4411_, 0);
v_collectKinds_4414_ = lean_ctor_get(v_info_4411_, 1);
v___x_4415_ = lean_box(0);
lean_inc_ref(v_collectTokens_4413_);
v___x_4416_ = lean_apply_1(v_collectTokens_4413_, v___x_4415_);
lean_inc(v_declName_4384_);
v___x_4417_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4386_, v_declName_4384_, v___x_4416_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
lean_dec_ref_known(v___x_4417_, 1);
v___x_4418_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
lean_inc_ref(v_collectKinds_4414_);
v___x_4419_ = lean_apply_1(v_collectKinds_4414_, v___x_4418_);
v___x_4420_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v___x_4419_, v___f_4390_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v___x_4421_; uint8_t v___x_4422_; uint8_t v___x_4423_; lean_object* v___x_4424_; 
lean_dec_ref_known(v___x_4420_, 1);
lean_inc(v_a_4393_);
lean_inc(v_snd_4410_);
lean_inc_n(v_declName_4384_, 2);
lean_inc_n(v_catName_4383_, 2);
v___x_4421_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_4421_, 0, v_catName_4383_);
lean_ctor_set(v___x_4421_, 1, v_declName_4384_);
lean_ctor_set(v___x_4421_, 2, v_snd_4410_);
lean_ctor_set(v___x_4421_, 3, v_a_4393_);
v___x_4422_ = lean_unbox(v_fst_4412_);
lean_ctor_set_uint8(v___x_4421_, sizeof(void*)*4, v___x_4422_);
v___x_4423_ = lean_unbox(v_fst_4412_);
lean_dec(v_fst_4412_);
v___x_4424_ = l_Lean_Parser_addParser(v_categories_4402_, v_catName_4383_, v_declName_4384_, v___x_4423_, v_snd_4410_, v_a_4393_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4434_; 
lean_dec_ref_known(v___x_4421_, 4);
lean_dec(v_declName_4384_);
lean_dec(v_catName_4383_);
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4427_ = v___x_4424_;
v_isShared_4428_ = v_isSharedCheck_4434_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4424_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4434_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
lean_ctor_set_tag(v___x_4427_, 3);
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = l_Lean_MessageData_ofFormat(v___x_4430_);
v___x_4432_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4431_, v_a_4387_, v_a_4388_);
return v___x_4432_;
}
}
}
else
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
lean_dec_ref_known(v___x_4424_, 1);
v___x_4435_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_4396_, v___x_4421_, v_attrKind_4386_, v_a_4387_, v_a_4388_);
lean_dec_ref(v___x_4435_);
v___x_4436_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4383_, v_declName_4384_, v___x_4400_, v_a_4387_, v_a_4388_);
return v___x_4436_;
}
}
else
{
lean_dec(v_fst_4412_);
lean_dec(v_snd_4410_);
lean_dec_ref(v_categories_4402_);
lean_dec(v_a_4393_);
lean_dec(v_declName_4384_);
lean_dec(v_catName_4383_);
return v___x_4420_;
}
}
else
{
lean_dec(v_fst_4412_);
lean_dec(v_snd_4410_);
lean_dec_ref(v_categories_4402_);
lean_dec(v_a_4393_);
lean_dec(v_declName_4384_);
lean_dec(v_catName_4383_);
return v___x_4417_;
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4448_; 
lean_dec_ref(v_categories_4402_);
lean_dec(v_a_4393_);
lean_dec(v_declName_4384_);
lean_dec(v_catName_4383_);
v_a_4437_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4439_ = v___x_4408_;
v_isShared_4440_ = v_isSharedCheck_4448_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4408_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4448_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4446_; 
v___x_4441_ = lean_io_error_to_string(v_a_4437_);
v___x_4442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
v___x_4443_ = l_Lean_MessageData_ofFormat(v___x_4442_);
lean_inc(v_ref_4405_);
v___x_4444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4444_, 0, v_ref_4405_);
lean_ctor_set(v___x_4444_, 1, v___x_4443_);
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 0, v___x_4444_);
v___x_4446_ = v___x_4439_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4444_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_dec(v_declName_4384_);
lean_dec(v_catName_4383_);
v_a_4449_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4392_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4392_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object* v_catName_4457_, lean_object* v_declName_4458_, lean_object* v_stx_4459_, lean_object* v_attrKind_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_){
_start:
{
uint8_t v_attrKind_boxed_4464_; lean_object* v_res_4465_; 
v_attrKind_boxed_4464_ = lean_unbox(v_attrKind_4460_);
v_res_4465_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4457_, v_declName_4458_, v_stx_4459_, v_attrKind_boxed_4464_, v_a_4461_, v_a_4462_);
lean_dec(v_a_4462_);
lean_dec_ref(v_a_4461_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* v___attrName_4466_, lean_object* v_catName_4467_, lean_object* v_declName_4468_, lean_object* v_stx_4469_, uint8_t v_attrKind_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v___x_4474_; 
v___x_4474_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4467_, v_declName_4468_, v_stx_4469_, v_attrKind_4470_, v_a_4471_, v_a_4472_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* v___attrName_4475_, lean_object* v_catName_4476_, lean_object* v_declName_4477_, lean_object* v_stx_4478_, lean_object* v_attrKind_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_){
_start:
{
uint8_t v_attrKind_boxed_4483_; lean_object* v_res_4484_; 
v_attrKind_boxed_4483_ = lean_unbox(v_attrKind_4479_);
v_res_4484_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4475_, v_catName_4476_, v_declName_4477_, v_stx_4478_, v_attrKind_boxed_4483_, v_a_4480_, v_a_4481_);
lean_dec(v_a_4481_);
lean_dec_ref(v_a_4480_);
lean_dec(v___attrName_4475_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object* v_00_u03b2_4485_, lean_object* v_map_4486_, lean_object* v_f_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v___x_4491_; 
v___x_4491_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4486_, v_f_4487_, v___y_4488_, v___y_4489_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b2_4492_, lean_object* v_map_4493_, lean_object* v_f_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(v_00_u03b2_4492_, v_map_4493_, v_f_4494_, v___y_4495_, v___y_4496_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object* v_map_4499_, lean_object* v_f_4500_, lean_object* v_init_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
lean_object* v___x_4505_; 
v___x_4505_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4500_, v_map_4499_, v_init_4501_, v___y_4502_, v___y_4503_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object* v_map_4506_, lean_object* v_f_4507_, lean_object* v_init_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4506_, v_f_4507_, v_init_4508_, v___y_4509_, v___y_4510_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object* v_00_u03c3_4513_, lean_object* v_00_u03b2_4514_, lean_object* v_map_4515_, lean_object* v_f_4516_, lean_object* v_init_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v___x_4521_; 
v___x_4521_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4516_, v_map_4515_, v_init_4517_, v___y_4518_, v___y_4519_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object* v_00_u03c3_4522_, lean_object* v_00_u03b2_4523_, lean_object* v_map_4524_, lean_object* v_f_4525_, lean_object* v_init_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(v_00_u03c3_4522_, v_00_u03b2_4523_, v_map_4524_, v_f_4525_, v_init_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_4531_, lean_object* v_00_u03b1_4532_, lean_object* v_00_u03b2_4533_, lean_object* v_f_4534_, lean_object* v_x_4535_, lean_object* v_x_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4534_, v_x_4535_, v_x_4536_, v___y_4537_, v___y_4538_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03c3_4541_, lean_object* v_00_u03b1_4542_, lean_object* v_00_u03b2_4543_, lean_object* v_f_4544_, lean_object* v_x_4545_, lean_object* v_x_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(v_00_u03c3_4541_, v_00_u03b1_4542_, v_00_u03b2_4543_, v_f_4544_, v_x_4545_, v_x_4546_, v___y_4547_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4551_, lean_object* v_00_u03b2_4552_, lean_object* v_00_u03c3_4553_, lean_object* v_f_4554_, lean_object* v_as_4555_, size_t v_i_4556_, size_t v_stop_4557_, lean_object* v_b_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v___x_4562_; 
v___x_4562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4554_, v_as_4555_, v_i_4556_, v_stop_4557_, v_b_4558_, v___y_4559_, v___y_4560_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4563_, lean_object* v_00_u03b2_4564_, lean_object* v_00_u03c3_4565_, lean_object* v_f_4566_, lean_object* v_as_4567_, lean_object* v_i_4568_, lean_object* v_stop_4569_, lean_object* v_b_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
size_t v_i_boxed_4574_; size_t v_stop_boxed_4575_; lean_object* v_res_4576_; 
v_i_boxed_4574_ = lean_unbox_usize(v_i_4568_);
lean_dec(v_i_4568_);
v_stop_boxed_4575_ = lean_unbox_usize(v_stop_4569_);
lean_dec(v_stop_4569_);
v_res_4576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4563_, v_00_u03b2_4564_, v_00_u03c3_4565_, v_f_4566_, v_as_4567_, v_i_boxed_4574_, v_stop_boxed_4575_, v_b_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec_ref(v_as_4567_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_4577_, lean_object* v_00_u03b1_4578_, lean_object* v_00_u03b2_4579_, lean_object* v_f_4580_, lean_object* v_keys_4581_, lean_object* v_vals_4582_, lean_object* v_heq_4583_, lean_object* v_i_4584_, lean_object* v_acc_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
lean_object* v___x_4589_; 
v___x_4589_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4580_, v_keys_4581_, v_vals_4582_, v_i_4584_, v_acc_4585_, v___y_4586_, v___y_4587_);
return v___x_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_4590_, lean_object* v_00_u03b1_4591_, lean_object* v_00_u03b2_4592_, lean_object* v_f_4593_, lean_object* v_keys_4594_, lean_object* v_vals_4595_, lean_object* v_heq_4596_, lean_object* v_i_4597_, lean_object* v_acc_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4590_, v_00_u03b1_4591_, v_00_u03b2_4592_, v_f_4593_, v_keys_4594_, v_vals_4595_, v_heq_4596_, v_i_4597_, v_acc_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec_ref(v_vals_4595_);
lean_dec_ref(v_keys_4594_);
return v_res_4602_;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___auto__1(void){
_start:
{
lean_object* v___x_4603_; 
v___x_4603_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object* v_catName_4604_, lean_object* v_declName_4605_, lean_object* v_stx_4606_, uint8_t v_attrKind_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v___x_4611_; 
v___x_4611_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4604_, v_declName_4605_, v_stx_4606_, v_attrKind_4607_, v___y_4608_, v___y_4609_);
return v___x_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object* v_catName_4612_, lean_object* v_declName_4613_, lean_object* v_stx_4614_, lean_object* v_attrKind_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
uint8_t v_attrKind_boxed_4619_; lean_object* v_res_4620_; 
v_attrKind_boxed_4619_ = lean_unbox(v_attrKind_4615_);
v_res_4620_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4612_, v_declName_4613_, v_stx_4614_, v_attrKind_boxed_4619_, v___y_4616_, v___y_4617_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* v_attrName_4622_, lean_object* v_catName_4623_, lean_object* v_ref_4624_){
_start:
{
lean_object* v___f_4625_; lean_object* v___f_4626_; lean_object* v___x_4627_; uint8_t v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___f_4625_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4625_, 0, v_catName_4623_);
lean_inc(v_attrName_4622_);
v___f_4626_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4626_, 0, v_attrName_4622_);
v___x_4627_ = ((lean_object*)(l_Lean_Parser_mkParserAttributeImpl___closed__0));
v___x_4628_ = 1;
v___x_4629_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4629_, 0, v_ref_4624_);
lean_ctor_set(v___x_4629_, 1, v_attrName_4622_);
lean_ctor_set(v___x_4629_, 2, v___x_4627_);
lean_ctor_set_uint8(v___x_4629_, sizeof(void*)*3, v___x_4628_);
v___x_4630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4629_);
lean_ctor_set(v___x_4630_, 1, v___f_4625_);
lean_ctor_set(v___x_4630_, 2, v___f_4626_);
return v___x_4630_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4631_; 
v___x_4631_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* v_attrName_4632_, lean_object* v_catName_4633_, lean_object* v_ref_4634_){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = l_Lean_Parser_mkParserAttributeImpl(v_attrName_4632_, v_catName_4633_, v_ref_4634_);
v___x_4637_ = l_Lean_registerBuiltinAttribute(v___x_4636_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object* v_attrName_4638_, lean_object* v_catName_4639_, lean_object* v_ref_4640_, lean_object* v_a_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4638_, v_catName_4639_, v_ref_4640_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object* v_ref_4646_, lean_object* v_args_4647_){
_start:
{
if (lean_obj_tag(v_args_4647_) == 1)
{
lean_object* v_head_4650_; 
v_head_4650_ = lean_ctor_get(v_args_4647_, 0);
lean_inc(v_head_4650_);
if (lean_obj_tag(v_head_4650_) == 2)
{
lean_object* v_tail_4651_; 
v_tail_4651_ = lean_ctor_get(v_args_4647_, 1);
lean_inc(v_tail_4651_);
lean_dec_ref_known(v_args_4647_, 2);
if (lean_obj_tag(v_tail_4651_) == 1)
{
lean_object* v_head_4652_; 
v_head_4652_ = lean_ctor_get(v_tail_4651_, 0);
lean_inc(v_head_4652_);
if (lean_obj_tag(v_head_4652_) == 2)
{
lean_object* v_tail_4653_; 
v_tail_4653_ = lean_ctor_get(v_tail_4651_, 1);
lean_inc(v_tail_4653_);
lean_dec_ref_known(v_tail_4651_, 2);
if (lean_obj_tag(v_tail_4653_) == 0)
{
lean_object* v_v_4654_; lean_object* v_v_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4663_; 
v_v_4654_ = lean_ctor_get(v_head_4650_, 0);
lean_inc(v_v_4654_);
lean_dec_ref_known(v_head_4650_, 1);
v_v_4655_ = lean_ctor_get(v_head_4652_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v_head_4652_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4657_ = v_head_4652_;
v_isShared_4658_ = v_isSharedCheck_4663_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_v_4655_);
lean_dec(v_head_4652_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4663_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4659_; lean_object* v___x_4661_; 
v___x_4659_ = l_Lean_Parser_mkParserAttributeImpl(v_v_4654_, v_v_4655_, v_ref_4646_);
if (v_isShared_4658_ == 0)
{
lean_ctor_set_tag(v___x_4657_, 1);
lean_ctor_set(v___x_4657_, 0, v___x_4659_);
v___x_4661_ = v___x_4657_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v___x_4659_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
else
{
lean_dec(v_tail_4653_);
lean_dec_ref_known(v_head_4652_, 1);
lean_dec_ref_known(v_head_4650_, 1);
lean_dec(v_ref_4646_);
goto v___jp_4648_;
}
}
else
{
lean_dec(v_head_4652_);
lean_dec_ref_known(v_tail_4651_, 2);
lean_dec_ref_known(v_head_4650_, 1);
lean_dec(v_ref_4646_);
goto v___jp_4648_;
}
}
else
{
lean_dec_ref_known(v_head_4650_, 1);
lean_dec(v_tail_4651_);
lean_dec(v_ref_4646_);
goto v___jp_4648_;
}
}
else
{
lean_dec_ref_known(v_args_4647_, 2);
lean_dec(v_head_4650_);
lean_dec(v_ref_4646_);
goto v___jp_4648_;
}
}
else
{
lean_dec(v_args_4647_);
lean_dec(v_ref_4646_);
goto v___jp_4648_;
}
v___jp_4648_:
{
lean_object* v___x_4649_; 
v___x_4649_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
return v___x_4649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___f_4669_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4670_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4671_ = l_Lean_registerAttributeImplBuilder(v___x_4670_, v___f_4669_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object* v_a_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
return v_res_4673_;
}
}
static lean_object* _init_l_Lean_Parser_registerParserCategory___auto__1(void){
_start:
{
lean_object* v___x_4674_; 
v___x_4674_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object* v_env_4675_, lean_object* v_attrName_4676_, lean_object* v_catName_4677_, uint8_t v_behavior_4678_, lean_object* v_ref_4679_){
_start:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; 
lean_inc(v_ref_4679_);
lean_inc(v_catName_4677_);
v___x_4681_ = l_Lean_Parser_addParserCategory(v_env_4675_, v_catName_4677_, v_ref_4679_, v_behavior_4678_);
v___x_4682_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_4681_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4696_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4685_ = v___x_4682_;
v_isShared_4686_ = v_isSharedCheck_4696_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4682_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4696_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4687_; lean_object* v___x_4689_; 
v___x_4687_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
if (v_isShared_4686_ == 0)
{
lean_ctor_set_tag(v___x_4685_, 2);
lean_ctor_set(v___x_4685_, 0, v_attrName_4676_);
v___x_4689_ = v___x_4685_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_attrName_4676_);
v___x_4689_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; 
v___x_4690_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4690_, 0, v_catName_4677_);
v___x_4691_ = lean_box(0);
v___x_4692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4690_);
lean_ctor_set(v___x_4692_, 1, v___x_4691_);
v___x_4693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4689_);
lean_ctor_set(v___x_4693_, 1, v___x_4692_);
v___x_4694_ = l_Lean_registerAttributeOfBuilder(v_a_4683_, v___x_4687_, v_ref_4679_, v___x_4693_);
return v___x_4694_;
}
}
}
else
{
lean_dec(v_ref_4679_);
lean_dec(v_catName_4677_);
lean_dec(v_attrName_4676_);
return v___x_4682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* v_env_4697_, lean_object* v_attrName_4698_, lean_object* v_catName_4699_, lean_object* v_behavior_4700_, lean_object* v_ref_4701_, lean_object* v_a_4702_){
_start:
{
uint8_t v_behavior_boxed_4703_; lean_object* v_res_4704_; 
v_behavior_boxed_4703_ = lean_unbox(v_behavior_4700_);
v_res_4704_ = l_Lean_Parser_registerParserCategory(v_env_4697_, v_attrName_4698_, v_catName_4699_, v_behavior_boxed_4703_, v_ref_4701_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4727_; lean_object* v___x_4728_; uint8_t v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4727_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4728_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4729_ = 0;
v___x_4730_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4731_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4727_, v___x_4728_, v___x_4729_, v___x_4730_);
return v___x_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object* v_a_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
return v_res_4733_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4739_ = lean_unsigned_to_nat(3431364690u);
v___x_4740_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4741_ = l_Lean_Name_num___override(v___x_4740_, v___x_4739_);
return v___x_4741_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4742_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4743_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4744_ = l_Lean_Name_str___override(v___x_4743_, v___x_4742_);
return v___x_4744_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; 
v___x_4745_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4746_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4747_ = l_Lean_Name_str___override(v___x_4746_, v___x_4745_);
return v___x_4747_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4748_ = lean_unsigned_to_nat(2u);
v___x_4749_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4750_ = l_Lean_Name_num___override(v___x_4749_, v___x_4748_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; 
v___x_4752_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4753_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4754_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4755_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4752_, v___x_4753_, v___x_4754_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object* v_a_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
return v_res_4757_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
v___x_4767_ = lean_unsigned_to_nat(2342493449u);
v___x_4768_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4769_ = l_Lean_Name_num___override(v___x_4768_, v___x_4767_);
return v___x_4769_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4770_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4771_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4772_ = l_Lean_Name_str___override(v___x_4771_, v___x_4770_);
return v___x_4772_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4773_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4774_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4775_ = l_Lean_Name_str___override(v___x_4774_, v___x_4773_);
return v___x_4775_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4776_ = lean_unsigned_to_nat(2u);
v___x_4777_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4778_ = l_Lean_Name_num___override(v___x_4777_, v___x_4776_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4780_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4781_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4782_ = 0;
v___x_4783_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4784_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4780_, v___x_4781_, v___x_4782_, v___x_4783_);
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object* v_a_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
return v_res_4786_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4792_ = lean_unsigned_to_nat(3226070615u);
v___x_4793_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4794_ = l_Lean_Name_num___override(v___x_4793_, v___x_4792_);
return v___x_4794_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4795_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4796_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4797_ = l_Lean_Name_str___override(v___x_4796_, v___x_4795_);
return v___x_4797_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4798_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4799_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4800_ = l_Lean_Name_str___override(v___x_4799_, v___x_4798_);
return v___x_4800_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4801_ = lean_unsigned_to_nat(2u);
v___x_4802_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4803_ = l_Lean_Name_num___override(v___x_4802_, v___x_4801_);
return v___x_4803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4805_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4806_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4807_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4808_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4805_, v___x_4806_, v___x_4807_);
return v___x_4808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object* v_a_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* v_rbp_4811_){
_start:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4812_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4813_ = l_Lean_Parser_categoryParser(v___x_4812_, v_rbp_4811_);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t v_addOpenSimple_4814_, lean_object* v_x_4815_, lean_object* v_x_4816_){
_start:
{
if (lean_obj_tag(v_x_4816_) == 0)
{
return v_x_4815_;
}
else
{
lean_object* v_head_4817_; lean_object* v_tail_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4841_; 
v_head_4817_ = lean_ctor_get(v_x_4816_, 0);
v_tail_4818_ = lean_ctor_get(v_x_4816_, 1);
v_isSharedCheck_4841_ = !lean_is_exclusive(v_x_4816_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4820_ = v_x_4816_;
v_isShared_4821_ = v_isSharedCheck_4841_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_tail_4818_);
lean_inc(v_head_4817_);
lean_dec(v_x_4816_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4841_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v_fst_4822_; lean_object* v_snd_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4840_; 
v_fst_4822_ = lean_ctor_get(v_x_4815_, 0);
v_snd_4823_ = lean_ctor_get(v_x_4815_, 1);
v_isSharedCheck_4840_ = !lean_is_exclusive(v_x_4815_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4825_ = v_x_4815_;
v_isShared_4826_ = v_isSharedCheck_4840_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_snd_4823_);
lean_inc(v_fst_4822_);
lean_dec(v_x_4815_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4840_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___y_4828_; 
if (v_addOpenSimple_4814_ == 0)
{
lean_del_object(v___x_4820_);
v___y_4828_ = v_snd_4823_;
goto v___jp_4827_;
}
else
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4838_; 
v___x_4835_ = lean_box(0);
lean_inc(v_head_4817_);
v___x_4836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4836_, 0, v_head_4817_);
lean_ctor_set(v___x_4836_, 1, v___x_4835_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 1, v_snd_4823_);
lean_ctor_set(v___x_4820_, 0, v___x_4836_);
v___x_4838_ = v___x_4820_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v___x_4836_);
lean_ctor_set(v_reuseFailAlloc_4839_, 1, v_snd_4823_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
v___y_4828_ = v___x_4838_;
goto v___jp_4827_;
}
}
v___jp_4827_:
{
lean_object* v___x_4829_; lean_object* v_env_4830_; lean_object* v___x_4832_; 
v___x_4829_ = l_Lean_Parser_parserExtension;
v_env_4830_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v___x_4829_, v_fst_4822_, v_head_4817_);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 1, v___y_4828_);
lean_ctor_set(v___x_4825_, 0, v_env_4830_);
v___x_4832_ = v___x_4825_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_env_4830_);
lean_ctor_set(v_reuseFailAlloc_4834_, 1, v___y_4828_);
v___x_4832_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
v_x_4815_ = v___x_4832_;
v_x_4816_ = v_tail_4818_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object* v_addOpenSimple_4842_, lean_object* v_x_4843_, lean_object* v_x_4844_){
_start:
{
uint8_t v_addOpenSimple_boxed_4845_; lean_object* v_res_4846_; 
v_addOpenSimple_boxed_4845_ = lean_unbox(v_addOpenSimple_4842_);
v_res_4846_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_boxed_4845_, v_x_4843_, v_x_4844_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t v_addOpenSimple_4847_, lean_object* v_as_4848_, size_t v_i_4849_, size_t v_stop_4850_, lean_object* v_b_4851_){
_start:
{
uint8_t v___x_4852_; 
v___x_4852_ = lean_usize_dec_eq(v_i_4849_, v_stop_4850_);
if (v___x_4852_ == 0)
{
lean_object* v_toParserModuleContext_4853_; lean_object* v_toInputContext_4854_; lean_object* v_toCacheableParserContext_4855_; lean_object* v_tokens_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4883_; 
v_toParserModuleContext_4853_ = lean_ctor_get(v_b_4851_, 1);
v_toInputContext_4854_ = lean_ctor_get(v_b_4851_, 0);
v_toCacheableParserContext_4855_ = lean_ctor_get(v_b_4851_, 2);
v_tokens_4856_ = lean_ctor_get(v_b_4851_, 3);
v_isSharedCheck_4883_ = !lean_is_exclusive(v_b_4851_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4858_ = v_b_4851_;
v_isShared_4859_ = v_isSharedCheck_4883_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_tokens_4856_);
lean_inc(v_toCacheableParserContext_4855_);
lean_inc(v_toParserModuleContext_4853_);
lean_inc(v_toInputContext_4854_);
lean_dec(v_b_4851_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4883_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v_env_4860_; lean_object* v_options_4861_; lean_object* v_currNamespace_4862_; lean_object* v_openDecls_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4882_; 
v_env_4860_ = lean_ctor_get(v_toParserModuleContext_4853_, 0);
v_options_4861_ = lean_ctor_get(v_toParserModuleContext_4853_, 1);
v_currNamespace_4862_ = lean_ctor_get(v_toParserModuleContext_4853_, 2);
v_openDecls_4863_ = lean_ctor_get(v_toParserModuleContext_4853_, 3);
v_isSharedCheck_4882_ = !lean_is_exclusive(v_toParserModuleContext_4853_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4865_ = v_toParserModuleContext_4853_;
v_isShared_4866_ = v_isSharedCheck_4882_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_openDecls_4863_);
lean_inc(v_currNamespace_4862_);
lean_inc(v_options_4861_);
lean_inc(v_env_4860_);
lean_dec(v_toParserModuleContext_4853_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4882_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4867_; lean_object* v_nss_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v_fst_4871_; lean_object* v_snd_4872_; lean_object* v___x_4874_; 
v___x_4867_ = lean_array_uget_borrowed(v_as_4848_, v_i_4849_);
lean_inc(v___x_4867_);
lean_inc(v_openDecls_4863_);
lean_inc(v_currNamespace_4862_);
lean_inc_ref(v_env_4860_);
v_nss_4868_ = l_Lean_ResolveName_resolveNamespace(v_env_4860_, v_currNamespace_4862_, v_openDecls_4863_, v___x_4867_);
v___x_4869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4869_, 0, v_env_4860_);
lean_ctor_set(v___x_4869_, 1, v_openDecls_4863_);
v___x_4870_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4847_, v___x_4869_, v_nss_4868_);
v_fst_4871_ = lean_ctor_get(v___x_4870_, 0);
lean_inc(v_fst_4871_);
v_snd_4872_ = lean_ctor_get(v___x_4870_, 1);
lean_inc(v_snd_4872_);
lean_dec_ref(v___x_4870_);
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 3, v_snd_4872_);
lean_ctor_set(v___x_4865_, 0, v_fst_4871_);
v___x_4874_ = v___x_4865_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_fst_4871_);
lean_ctor_set(v_reuseFailAlloc_4881_, 1, v_options_4861_);
lean_ctor_set(v_reuseFailAlloc_4881_, 2, v_currNamespace_4862_);
lean_ctor_set(v_reuseFailAlloc_4881_, 3, v_snd_4872_);
v___x_4874_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
lean_object* v___x_4876_; 
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 1, v___x_4874_);
v___x_4876_ = v___x_4858_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_toInputContext_4854_);
lean_ctor_set(v_reuseFailAlloc_4880_, 1, v___x_4874_);
lean_ctor_set(v_reuseFailAlloc_4880_, 2, v_toCacheableParserContext_4855_);
lean_ctor_set(v_reuseFailAlloc_4880_, 3, v_tokens_4856_);
v___x_4876_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
size_t v___x_4877_; size_t v___x_4878_; 
v___x_4877_ = ((size_t)1ULL);
v___x_4878_ = lean_usize_add(v_i_4849_, v___x_4877_);
v_i_4849_ = v___x_4878_;
v_b_4851_ = v___x_4876_;
goto _start;
}
}
}
}
}
else
{
return v_b_4851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object* v_addOpenSimple_4884_, lean_object* v_as_4885_, lean_object* v_i_4886_, lean_object* v_stop_4887_, lean_object* v_b_4888_){
_start:
{
uint8_t v_addOpenSimple_boxed_4889_; size_t v_i_boxed_4890_; size_t v_stop_boxed_4891_; lean_object* v_res_4892_; 
v_addOpenSimple_boxed_4889_ = lean_unbox(v_addOpenSimple_4884_);
v_i_boxed_4890_ = lean_unbox_usize(v_i_4886_);
lean_dec(v_i_4886_);
v_stop_boxed_4891_ = lean_unbox_usize(v_stop_4887_);
lean_dec(v_stop_4887_);
v_res_4892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_boxed_4889_, v_as_4885_, v_i_boxed_4890_, v_stop_boxed_4891_, v_b_4888_);
lean_dec_ref(v_as_4885_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object* v___x_4893_, lean_object* v_ids_4894_, uint8_t v_addOpenSimple_4895_, lean_object* v_c_4896_){
_start:
{
lean_object* v___y_4898_; lean_object* v___x_4918_; lean_object* v___x_4919_; uint8_t v___x_4920_; 
v___x_4918_ = lean_unsigned_to_nat(0u);
v___x_4919_ = lean_array_get_size(v_ids_4894_);
v___x_4920_ = lean_nat_dec_lt(v___x_4918_, v___x_4919_);
if (v___x_4920_ == 0)
{
v___y_4898_ = v_c_4896_;
goto v___jp_4897_;
}
else
{
size_t v___x_4921_; size_t v___x_4922_; lean_object* v___x_4923_; 
v___x_4921_ = ((size_t)0ULL);
v___x_4922_ = lean_usize_of_nat(v___x_4919_);
v___x_4923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4895_, v_ids_4894_, v___x_4921_, v___x_4922_, v_c_4896_);
v___y_4898_ = v___x_4923_;
goto v___jp_4897_;
}
v___jp_4897_:
{
lean_object* v_toParserModuleContext_4899_; lean_object* v_toInputContext_4900_; lean_object* v_toCacheableParserContext_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4916_; 
v_toParserModuleContext_4899_ = lean_ctor_get(v___y_4898_, 1);
v_toInputContext_4900_ = lean_ctor_get(v___y_4898_, 0);
v_toCacheableParserContext_4901_ = lean_ctor_get(v___y_4898_, 2);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___y_4898_);
if (v_isSharedCheck_4916_ == 0)
{
lean_object* v_unused_4917_; 
v_unused_4917_ = lean_ctor_get(v___y_4898_, 3);
lean_dec(v_unused_4917_);
v___x_4903_ = v___y_4898_;
v_isShared_4904_ = v_isSharedCheck_4916_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_toCacheableParserContext_4901_);
lean_inc(v_toParserModuleContext_4899_);
lean_inc(v_toInputContext_4900_);
lean_dec(v___y_4898_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4916_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v_env_4905_; lean_object* v___x_4906_; lean_object* v_ext_4907_; lean_object* v_toEnvExtension_4908_; lean_object* v_asyncMode_4909_; uint8_t v___x_4910_; lean_object* v___x_4911_; lean_object* v_tokens_4912_; lean_object* v___x_4914_; 
v_env_4905_ = lean_ctor_get(v_toParserModuleContext_4899_, 0);
v___x_4906_ = l_Lean_Parser_parserExtension;
v_ext_4907_ = lean_ctor_get(v___x_4906_, 1);
v_toEnvExtension_4908_ = lean_ctor_get(v_ext_4907_, 0);
v_asyncMode_4909_ = lean_ctor_get(v_toEnvExtension_4908_, 2);
v___x_4910_ = 0;
lean_inc_ref(v_env_4905_);
v___x_4911_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4893_, v___x_4906_, v_env_4905_, v_asyncMode_4909_, v___x_4910_);
v_tokens_4912_ = lean_ctor_get(v___x_4911_, 0);
lean_inc_ref(v_tokens_4912_);
lean_dec(v___x_4911_);
if (v_isShared_4904_ == 0)
{
lean_ctor_set(v___x_4903_, 3, v_tokens_4912_);
v___x_4914_ = v___x_4903_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_toInputContext_4900_);
lean_ctor_set(v_reuseFailAlloc_4915_, 1, v_toParserModuleContext_4899_);
lean_ctor_set(v_reuseFailAlloc_4915_, 2, v_toCacheableParserContext_4901_);
lean_ctor_set(v_reuseFailAlloc_4915_, 3, v_tokens_4912_);
v___x_4914_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
return v___x_4914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object* v___x_4924_, lean_object* v_ids_4925_, lean_object* v_addOpenSimple_4926_, lean_object* v_c_4927_){
_start:
{
uint8_t v_addOpenSimple_boxed_4928_; lean_object* v_res_4929_; 
v_addOpenSimple_boxed_4928_ = lean_unbox(v_addOpenSimple_4926_);
v_res_4929_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_4924_, v_ids_4925_, v_addOpenSimple_boxed_4928_, v_c_4927_);
lean_dec_ref(v_ids_4925_);
lean_dec_ref(v___x_4924_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* v_ids_4930_, uint8_t v_addOpenSimple_4931_, lean_object* v_p_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___f_4937_; lean_object* v___x_4938_; 
v___x_4935_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4936_ = lean_box(v_addOpenSimple_4931_);
v___f_4937_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4937_, 0, v___x_4935_);
lean_closure_set(v___f_4937_, 1, v_ids_4930_);
lean_closure_set(v___f_4937_, 2, v___x_4936_);
v___x_4938_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_4937_, v_p_4932_, v_a_4933_, v_a_4934_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* v_ids_4939_, lean_object* v_addOpenSimple_4940_, lean_object* v_p_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_){
_start:
{
uint8_t v_addOpenSimple_boxed_4944_; lean_object* v_res_4945_; 
v_addOpenSimple_boxed_4944_ = lean_unbox(v_addOpenSimple_4940_);
v_res_4945_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_4939_, v_addOpenSimple_boxed_4944_, v_p_4941_, v_a_4942_, v_a_4943_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t v_sz_4946_, size_t v_i_4947_, lean_object* v_bs_4948_){
_start:
{
uint8_t v___x_4949_; 
v___x_4949_ = lean_usize_dec_lt(v_i_4947_, v_sz_4946_);
if (v___x_4949_ == 0)
{
return v_bs_4948_;
}
else
{
lean_object* v_v_4950_; lean_object* v___x_4951_; lean_object* v_bs_x27_4952_; lean_object* v___x_4953_; size_t v___x_4954_; size_t v___x_4955_; lean_object* v___x_4956_; 
v_v_4950_ = lean_array_uget(v_bs_4948_, v_i_4947_);
v___x_4951_ = lean_unsigned_to_nat(0u);
v_bs_x27_4952_ = lean_array_uset(v_bs_4948_, v_i_4947_, v___x_4951_);
v___x_4953_ = l_Lean_Syntax_getId(v_v_4950_);
lean_dec(v_v_4950_);
v___x_4954_ = ((size_t)1ULL);
v___x_4955_ = lean_usize_add(v_i_4947_, v___x_4954_);
v___x_4956_ = lean_array_uset(v_bs_x27_4952_, v_i_4947_, v___x_4953_);
v_i_4947_ = v___x_4955_;
v_bs_4948_ = v___x_4956_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object* v_sz_4958_, lean_object* v_i_4959_, lean_object* v_bs_4960_){
_start:
{
size_t v_sz_boxed_4961_; size_t v_i_boxed_4962_; lean_object* v_res_4963_; 
v_sz_boxed_4961_ = lean_unbox_usize(v_sz_4958_);
lean_dec(v_sz_4958_);
v_i_boxed_4962_ = lean_unbox_usize(v_i_4959_);
lean_dec(v_i_4959_);
v_res_4963_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_boxed_4961_, v_i_boxed_4962_, v_bs_4960_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* v_openDeclStx_4977_, lean_object* v_p_4978_, lean_object* v_c_4979_, lean_object* v_s_4980_){
_start:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; uint8_t v___x_4983_; 
lean_inc(v_openDeclStx_4977_);
v___x_4981_ = l_Lean_Syntax_getKind(v_openDeclStx_4977_);
v___x_4982_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__2));
v___x_4983_ = lean_name_eq(v___x_4981_, v___x_4982_);
if (v___x_4983_ == 0)
{
lean_object* v___x_4984_; uint8_t v___x_4985_; 
v___x_4984_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__4));
v___x_4985_ = lean_name_eq(v___x_4981_, v___x_4984_);
lean_dec(v___x_4981_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; 
lean_dec(v_openDeclStx_4977_);
v___x_4986_ = lean_apply_2(v_p_4978_, v_c_4979_, v_s_4980_);
return v___x_4986_;
}
else
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; size_t v_sz_4990_; size_t v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4987_ = lean_unsigned_to_nat(1u);
v___x_4988_ = l_Lean_Syntax_getArg(v_openDeclStx_4977_, v___x_4987_);
lean_dec(v_openDeclStx_4977_);
v___x_4989_ = l_Lean_Syntax_getArgs(v___x_4988_);
lean_dec(v___x_4988_);
v_sz_4990_ = lean_array_size(v___x_4989_);
v___x_4991_ = ((size_t)0ULL);
v___x_4992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4990_, v___x_4991_, v___x_4989_);
v___x_4993_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4992_, v___x_4983_, v_p_4978_, v_c_4979_, v_s_4980_);
return v___x_4993_;
}
}
else
{
lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; size_t v_sz_4997_; size_t v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; 
lean_dec(v___x_4981_);
v___x_4994_ = lean_unsigned_to_nat(0u);
v___x_4995_ = l_Lean_Syntax_getArg(v_openDeclStx_4977_, v___x_4994_);
lean_dec(v_openDeclStx_4977_);
v___x_4996_ = l_Lean_Syntax_getArgs(v___x_4995_);
lean_dec(v___x_4995_);
v_sz_4997_ = lean_array_size(v___x_4996_);
v___x_4998_ = ((size_t)0ULL);
v___x_4999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4997_, v___x_4998_, v___x_4996_);
v___x_5000_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4999_, v___x_4983_, v_p_4978_, v_c_4979_, v_s_4980_);
return v___x_5000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* v_p_5007_, lean_object* v_c_5008_, lean_object* v_s_5009_){
_start:
{
lean_object* v_stxStack_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; uint8_t v___x_5013_; 
v_stxStack_5010_ = lean_ctor_get(v_s_5009_, 0);
v___x_5011_ = lean_unsigned_to_nat(0u);
v___x_5012_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5010_);
v___x_5013_ = lean_nat_dec_lt(v___x_5011_, v___x_5012_);
lean_dec(v___x_5012_);
if (v___x_5013_ == 0)
{
lean_object* v___x_5014_; 
v___x_5014_ = lean_apply_2(v_p_5007_, v_c_5008_, v_s_5009_);
return v___x_5014_;
}
else
{
lean_object* v_stx_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; uint8_t v___x_5018_; 
v_stx_5015_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5010_);
lean_inc(v_stx_5015_);
v___x_5016_ = l_Lean_Syntax_getKind(v_stx_5015_);
v___x_5017_ = ((lean_object*)(l_Lean_Parser_withOpenFn___closed__1));
v___x_5018_ = lean_name_eq(v___x_5016_, v___x_5017_);
lean_dec(v___x_5016_);
if (v___x_5018_ == 0)
{
lean_object* v___x_5019_; 
lean_dec(v_stx_5015_);
v___x_5019_ = lean_apply_2(v_p_5007_, v_c_5008_, v_s_5009_);
return v___x_5019_;
}
else
{
lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5020_ = lean_unsigned_to_nat(1u);
v___x_5021_ = l_Lean_Syntax_getArg(v_stx_5015_, v___x_5020_);
lean_dec(v_stx_5015_);
v___x_5022_ = l_Lean_Parser_withOpenDeclFnCore(v___x_5021_, v_p_5007_, v_c_5008_, v_s_5009_);
return v___x_5022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* v_p_5023_){
_start:
{
lean_object* v_info_5024_; lean_object* v_fn_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5033_; 
v_info_5024_ = lean_ctor_get(v_p_5023_, 0);
v_fn_5025_ = lean_ctor_get(v_p_5023_, 1);
v_isSharedCheck_5033_ = !lean_is_exclusive(v_p_5023_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5027_ = v_p_5023_;
v_isShared_5028_ = v_isSharedCheck_5033_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_fn_5025_);
lean_inc(v_info_5024_);
lean_dec(v_p_5023_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5033_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5029_; lean_object* v___x_5031_; 
v___x_5029_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(v___x_5029_, 0, v_fn_5025_);
if (v_isShared_5028_ == 0)
{
lean_ctor_set(v___x_5027_, 1, v___x_5029_);
v___x_5031_ = v___x_5027_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_info_5024_);
lean_ctor_set(v_reuseFailAlloc_5032_, 1, v___x_5029_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
return v___x_5031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* v_p_5034_, lean_object* v_c_5035_, lean_object* v_s_5036_){
_start:
{
lean_object* v_stxStack_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; uint8_t v___x_5040_; 
v_stxStack_5037_ = lean_ctor_get(v_s_5036_, 0);
v___x_5038_ = lean_unsigned_to_nat(0u);
v___x_5039_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5037_);
v___x_5040_ = lean_nat_dec_lt(v___x_5038_, v___x_5039_);
lean_dec(v___x_5039_);
if (v___x_5040_ == 0)
{
lean_object* v___x_5041_; 
v___x_5041_ = lean_apply_2(v_p_5034_, v_c_5035_, v_s_5036_);
return v___x_5041_;
}
else
{
lean_object* v_stx_5042_; lean_object* v___x_5043_; 
v_stx_5042_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5037_);
v___x_5043_ = l_Lean_Parser_withOpenDeclFnCore(v_stx_5042_, v_p_5034_, v_c_5035_, v_s_5036_);
return v___x_5043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* v_p_5044_){
_start:
{
lean_object* v_info_5045_; lean_object* v_fn_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5054_; 
v_info_5045_ = lean_ctor_get(v_p_5044_, 0);
v_fn_5046_ = lean_ctor_get(v_p_5044_, 1);
v_isSharedCheck_5054_ = !lean_is_exclusive(v_p_5044_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5048_ = v_p_5044_;
v_isShared_5049_ = v_isSharedCheck_5054_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_fn_5046_);
lean_inc(v_info_5045_);
lean_dec(v_p_5044_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5054_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v___x_5050_; lean_object* v___x_5052_; 
v___x_5050_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(v___x_5050_, 0, v_fn_5046_);
if (v_isShared_5049_ == 0)
{
lean_ctor_set(v___x_5048_, 1, v___x_5050_);
v___x_5052_ = v___x_5048_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_info_5045_);
lean_ctor_set(v_reuseFailAlloc_5053_, 1, v___x_5050_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object* v_val_5061_){
_start:
{
lean_object* v___x_5069_; 
v___x_5069_ = l_Lean_Syntax_isStrLit_x3f(v_val_5061_);
if (lean_obj_tag(v___x_5069_) == 1)
{
lean_object* v_val_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5078_; 
v_val_5070_ = lean_ctor_get(v___x_5069_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5069_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5072_ = v___x_5069_;
v_isShared_5073_ = v_isSharedCheck_5078_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_val_5070_);
lean_dec(v___x_5069_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5078_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___x_5074_; lean_object* v___x_5076_; 
v___x_5074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5074_, 0, v_val_5070_);
if (v_isShared_5073_ == 0)
{
lean_ctor_set(v___x_5072_, 0, v___x_5074_);
v___x_5076_ = v___x_5072_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v___x_5074_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
else
{
lean_object* v___x_5079_; 
lean_dec(v___x_5069_);
v___x_5079_ = l_Lean_Syntax_isNatLit_x3f(v_val_5061_);
if (lean_obj_tag(v___x_5079_) == 1)
{
lean_object* v_val_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5088_; 
v_val_5080_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5082_ = v___x_5079_;
v_isShared_5083_ = v_isSharedCheck_5088_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_val_5080_);
lean_dec(v___x_5079_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5088_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5084_; lean_object* v___x_5086_; 
v___x_5084_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5084_, 0, v_val_5080_);
if (v_isShared_5083_ == 0)
{
lean_ctor_set(v___x_5082_, 0, v___x_5084_);
v___x_5086_ = v___x_5082_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v___x_5084_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
else
{
lean_dec(v___x_5079_);
if (lean_obj_tag(v_val_5061_) == 2)
{
lean_object* v_val_5089_; lean_object* v___x_5090_; uint8_t v___x_5091_; 
v_val_5089_ = lean_ctor_get(v_val_5061_, 1);
v___x_5090_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3));
v___x_5091_ = lean_string_dec_eq(v_val_5089_, v___x_5090_);
if (v___x_5091_ == 0)
{
goto v___jp_5062_;
}
else
{
lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5092_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5092_, 0, v___x_5091_);
v___x_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5093_, 0, v___x_5092_);
return v___x_5093_;
}
}
else
{
goto v___jp_5062_;
}
}
}
v___jp_5062_:
{
if (lean_obj_tag(v_val_5061_) == 2)
{
lean_object* v_val_5063_; lean_object* v___x_5064_; uint8_t v___x_5065_; 
v_val_5063_ = lean_ctor_get(v_val_5061_, 1);
v___x_5064_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0));
v___x_5065_ = lean_string_dec_eq(v_val_5063_, v___x_5064_);
if (v___x_5065_ == 0)
{
lean_object* v___x_5066_; 
v___x_5066_ = lean_box(0);
return v___x_5066_;
}
else
{
lean_object* v___x_5067_; 
v___x_5067_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2));
return v___x_5067_;
}
}
else
{
lean_object* v___x_5068_; 
v___x_5068_ = lean_box(0);
return v___x_5068_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object* v_val_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_val_5094_);
lean_dec(v_val_5094_);
return v_res_5095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object* v_nameStx_5096_, lean_object* v_v_5097_, lean_object* v_c_5098_){
_start:
{
lean_object* v_toParserModuleContext_5099_; lean_object* v_toInputContext_5100_; lean_object* v_toCacheableParserContext_5101_; lean_object* v_tokens_5102_; lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5139_; 
v_toParserModuleContext_5099_ = lean_ctor_get(v_c_5098_, 1);
v_toInputContext_5100_ = lean_ctor_get(v_c_5098_, 0);
v_toCacheableParserContext_5101_ = lean_ctor_get(v_c_5098_, 2);
v_tokens_5102_ = lean_ctor_get(v_c_5098_, 3);
v_isSharedCheck_5139_ = !lean_is_exclusive(v_c_5098_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5104_ = v_c_5098_;
v_isShared_5105_ = v_isSharedCheck_5139_;
goto v_resetjp_5103_;
}
else
{
lean_inc(v_tokens_5102_);
lean_inc(v_toCacheableParserContext_5101_);
lean_inc(v_toParserModuleContext_5099_);
lean_inc(v_toInputContext_5100_);
lean_dec(v_c_5098_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5139_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v_env_5106_; lean_object* v_options_5107_; lean_object* v_currNamespace_5108_; lean_object* v_openDecls_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5138_; 
v_env_5106_ = lean_ctor_get(v_toParserModuleContext_5099_, 0);
v_options_5107_ = lean_ctor_get(v_toParserModuleContext_5099_, 1);
v_currNamespace_5108_ = lean_ctor_get(v_toParserModuleContext_5099_, 2);
v_openDecls_5109_ = lean_ctor_get(v_toParserModuleContext_5099_, 3);
v_isSharedCheck_5138_ = !lean_is_exclusive(v_toParserModuleContext_5099_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_5111_ = v_toParserModuleContext_5099_;
v_isShared_5112_ = v_isSharedCheck_5138_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_openDecls_5109_);
lean_inc(v_currNamespace_5108_);
lean_inc(v_options_5107_);
lean_inc(v_env_5106_);
lean_dec(v_toParserModuleContext_5099_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5138_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___y_5114_; lean_object* v_map_5121_; uint8_t v_hasTrace_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5137_; 
v_map_5121_ = lean_ctor_get(v_options_5107_, 0);
v_hasTrace_5122_ = lean_ctor_get_uint8(v_options_5107_, sizeof(void*)*1);
v_isSharedCheck_5137_ = !lean_is_exclusive(v_options_5107_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5124_ = v_options_5107_;
v_isShared_5125_ = v_isSharedCheck_5137_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_map_5121_);
lean_dec(v_options_5107_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5137_;
goto v_resetjp_5123_;
}
v___jp_5113_:
{
lean_object* v___x_5116_; 
if (v_isShared_5112_ == 0)
{
lean_ctor_set(v___x_5111_, 1, v___y_5114_);
v___x_5116_ = v___x_5111_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_env_5106_);
lean_ctor_set(v_reuseFailAlloc_5120_, 1, v___y_5114_);
lean_ctor_set(v_reuseFailAlloc_5120_, 2, v_currNamespace_5108_);
lean_ctor_set(v_reuseFailAlloc_5120_, 3, v_openDecls_5109_);
v___x_5116_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
lean_object* v___x_5118_; 
if (v_isShared_5105_ == 0)
{
lean_ctor_set(v___x_5104_, 1, v___x_5116_);
v___x_5118_ = v___x_5104_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_toInputContext_5100_);
lean_ctor_set(v_reuseFailAlloc_5119_, 1, v___x_5116_);
lean_ctor_set(v_reuseFailAlloc_5119_, 2, v_toCacheableParserContext_5101_);
lean_ctor_set(v_reuseFailAlloc_5119_, 3, v_tokens_5102_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
}
v_resetjp_5123_:
{
lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v___x_5126_ = l_Lean_Syntax_getId(v_nameStx_5096_);
v___x_5127_ = l_Lean_Name_eraseMacroScopes(v___x_5126_);
lean_dec(v___x_5126_);
lean_inc(v___x_5127_);
v___x_5128_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_5127_, v_v_5097_, v_map_5121_);
if (v_hasTrace_5122_ == 0)
{
lean_object* v___x_5129_; uint8_t v___x_5130_; lean_object* v___x_5132_; 
v___x_5129_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_5130_ = l_Lean_Name_isPrefixOf(v___x_5129_, v___x_5127_);
lean_dec(v___x_5127_);
if (v_isShared_5125_ == 0)
{
lean_ctor_set(v___x_5124_, 0, v___x_5128_);
v___x_5132_ = v___x_5124_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v___x_5128_);
v___x_5132_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
lean_ctor_set_uint8(v___x_5132_, sizeof(void*)*1, v___x_5130_);
v___y_5114_ = v___x_5132_;
goto v___jp_5113_;
}
}
else
{
lean_object* v___x_5135_; 
lean_dec(v___x_5127_);
if (v_isShared_5125_ == 0)
{
lean_ctor_set(v___x_5124_, 0, v___x_5128_);
v___x_5135_ = v___x_5124_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v___x_5128_);
lean_ctor_set_uint8(v_reuseFailAlloc_5136_, sizeof(void*)*1, v_hasTrace_5122_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
v___y_5114_ = v___x_5135_;
goto v___jp_5113_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object* v_nameStx_5140_, lean_object* v_v_5141_, lean_object* v_c_5142_){
_start:
{
lean_object* v_res_5143_; 
v_res_5143_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(v_nameStx_5140_, v_v_5141_, v_c_5142_);
lean_dec(v_nameStx_5140_);
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object* v_nameStx_5144_, lean_object* v_valStx_5145_, lean_object* v_p_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_){
_start:
{
lean_object* v___x_5149_; 
v___x_5149_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_valStx_5145_);
if (lean_obj_tag(v___x_5149_) == 0)
{
lean_object* v___x_5150_; 
lean_dec(v_nameStx_5144_);
v___x_5150_ = lean_apply_2(v_p_5146_, v_a_5147_, v_a_5148_);
return v___x_5150_;
}
else
{
lean_object* v_val_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; 
v_val_5151_ = lean_ctor_get(v___x_5149_, 0);
lean_inc(v_val_5151_);
lean_dec_ref_known(v___x_5149_, 1);
v___x_5152_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed), 3, 2);
lean_closure_set(v___x_5152_, 0, v_nameStx_5144_);
lean_closure_set(v___x_5152_, 1, v_val_5151_);
v___x_5153_ = l_Lean_Parser_adaptUncacheableContextFn(v___x_5152_, v_p_5146_, v_a_5147_, v_a_5148_);
return v___x_5153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object* v_nameStx_5154_, lean_object* v_valStx_5155_, lean_object* v_p_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_){
_start:
{
lean_object* v_res_5159_; 
v_res_5159_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v_nameStx_5154_, v_valStx_5155_, v_p_5156_, v_a_5157_, v_a_5158_);
lean_dec(v_valStx_5155_);
return v_res_5159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object* v_p_5166_, lean_object* v_c_5167_, lean_object* v_s_5168_){
_start:
{
lean_object* v_stxStack_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; uint8_t v___x_5172_; 
v_stxStack_5169_ = lean_ctor_get(v_s_5168_, 0);
v___x_5170_ = lean_unsigned_to_nat(0u);
v___x_5171_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5169_);
v___x_5172_ = lean_nat_dec_lt(v___x_5170_, v___x_5171_);
lean_dec(v___x_5171_);
if (v___x_5172_ == 0)
{
lean_object* v___x_5173_; 
v___x_5173_ = lean_apply_2(v_p_5166_, v_c_5167_, v_s_5168_);
return v___x_5173_;
}
else
{
lean_object* v_stx_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; uint8_t v___x_5177_; 
v_stx_5174_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5169_);
lean_inc(v_stx_5174_);
v___x_5175_ = l_Lean_Syntax_getKind(v_stx_5174_);
v___x_5176_ = ((lean_object*)(l_Lean_Parser_withSetOptionFn___closed__1));
v___x_5177_ = lean_name_eq(v___x_5175_, v___x_5176_);
lean_dec(v___x_5175_);
if (v___x_5177_ == 0)
{
lean_object* v___x_5178_; 
lean_dec(v_stx_5174_);
v___x_5178_ = lean_apply_2(v_p_5166_, v_c_5167_, v_s_5168_);
return v___x_5178_;
}
else
{
lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; 
v___x_5179_ = lean_unsigned_to_nat(1u);
v___x_5180_ = l_Lean_Syntax_getArg(v_stx_5174_, v___x_5179_);
v___x_5181_ = lean_unsigned_to_nat(3u);
v___x_5182_ = l_Lean_Syntax_getArg(v_stx_5174_, v___x_5181_);
lean_dec(v_stx_5174_);
v___x_5183_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5180_, v___x_5182_, v_p_5166_, v_c_5167_, v_s_5168_);
lean_dec(v___x_5182_);
return v___x_5183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object* v_p_5184_){
_start:
{
lean_object* v_info_5185_; lean_object* v_fn_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5194_; 
v_info_5185_ = lean_ctor_get(v_p_5184_, 0);
v_fn_5186_ = lean_ctor_get(v_p_5184_, 1);
v_isSharedCheck_5194_ = !lean_is_exclusive(v_p_5184_);
if (v_isSharedCheck_5194_ == 0)
{
v___x_5188_ = v_p_5184_;
v_isShared_5189_ = v_isSharedCheck_5194_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_fn_5186_);
lean_inc(v_info_5185_);
lean_dec(v_p_5184_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5194_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v___x_5190_; lean_object* v___x_5192_; 
v___x_5190_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionFn), 3, 1);
lean_closure_set(v___x_5190_, 0, v_fn_5186_);
if (v_isShared_5189_ == 0)
{
lean_ctor_set(v___x_5188_, 1, v___x_5190_);
v___x_5192_ = v___x_5188_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_info_5185_);
lean_ctor_set(v_reuseFailAlloc_5193_, 1, v___x_5190_);
v___x_5192_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
return v___x_5192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object* v_p_5195_, lean_object* v_c_5196_, lean_object* v_s_5197_){
_start:
{
lean_object* v_stxStack_5198_; lean_object* v_sz_5199_; lean_object* v___x_5200_; uint8_t v___x_5201_; 
v_stxStack_5198_ = lean_ctor_get(v_s_5197_, 0);
v_sz_5199_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5198_);
v___x_5200_ = lean_unsigned_to_nat(3u);
v___x_5201_ = lean_nat_dec_le(v___x_5200_, v_sz_5199_);
if (v___x_5201_ == 0)
{
lean_object* v___x_5202_; 
lean_dec(v_sz_5199_);
v___x_5202_ = lean_apply_2(v_p_5195_, v_c_5196_, v_s_5197_);
return v___x_5202_;
}
else
{
lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; 
v___x_5203_ = lean_nat_sub(v_sz_5199_, v___x_5200_);
lean_dec(v_sz_5199_);
v___x_5204_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5198_, v___x_5203_);
lean_dec(v___x_5203_);
v___x_5205_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5198_);
v___x_5206_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5204_, v___x_5205_, v_p_5195_, v_c_5196_, v_s_5197_);
lean_dec(v___x_5205_);
return v___x_5206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object* v_p_5207_){
_start:
{
lean_object* v_info_5208_; lean_object* v_fn_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5217_; 
v_info_5208_ = lean_ctor_get(v_p_5207_, 0);
v_fn_5209_ = lean_ctor_get(v_p_5207_, 1);
v_isSharedCheck_5217_ = !lean_is_exclusive(v_p_5207_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5211_ = v_p_5207_;
v_isShared_5212_ = v_isSharedCheck_5217_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_fn_5209_);
lean_inc(v_info_5208_);
lean_dec(v_p_5207_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5217_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___x_5213_; lean_object* v___x_5215_; 
v___x_5213_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionValueFn), 3, 1);
lean_closure_set(v___x_5213_, 0, v_fn_5209_);
if (v_isShared_5212_ == 0)
{
lean_ctor_set(v___x_5211_, 1, v___x_5213_);
v___x_5215_ = v___x_5211_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_info_5208_);
lean_ctor_set(v_reuseFailAlloc_5216_, 1, v___x_5213_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object* v___x_5218_){
_start:
{
lean_object* v___x_5220_; lean_object* v___x_5221_; 
v___x_5220_ = lean_st_ref_get(v___x_5218_);
v___x_5221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5221_, 0, v___x_5220_);
return v___x_5221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v___x_5222_, lean_object* v___y_5223_){
_start:
{
lean_object* v_res_5224_; 
v_res_5224_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_5222_);
lean_dec(v___x_5222_);
return v_res_5224_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5225_; lean_object* v___f_5226_; 
v___x_5225_ = l_Lean_Parser_parserAliasesRef;
v___f_5226_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5226_, 0, v___x_5225_);
return v___f_5226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; uint8_t v___x_5237_; lean_object* v___x_5238_; 
v___f_5233_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_);
v___x_5234_ = lean_box(0);
v___x_5235_ = lean_box(2);
v___x_5236_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_));
v___x_5237_ = 0;
v___x_5238_ = l_Lean_registerEnvExtension___redArg(v___f_5233_, v___x_5234_, v___x_5235_, v___x_5236_, v___x_5237_, v___x_5237_);
return v___x_5238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v_a_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___impl(lean_object* v_x_5241_){
_start:
{
lean_object* v___x_5242_; 
v___x_5242_ = lean_obj_tag_nat(v_x_5241_);
return v___x_5242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___impl___boxed(lean_object* v_x_5243_){
_start:
{
lean_object* v_res_5244_; 
v_res_5244_ = l_Lean_Parser_ParserResolution_ctorIdx___impl(v_x_5243_);
lean_dec_ref(v_x_5243_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object* v_t_5245_, lean_object* v_k_5246_){
_start:
{
switch(lean_obj_tag(v_t_5245_))
{
case 0:
{
lean_object* v_cat_5247_; lean_object* v___x_5248_; 
v_cat_5247_ = lean_ctor_get(v_t_5245_, 0);
lean_inc(v_cat_5247_);
lean_dec_ref_known(v_t_5245_, 1);
v___x_5248_ = lean_apply_1(v_k_5246_, v_cat_5247_);
return v___x_5248_;
}
case 1:
{
lean_object* v_decl_5249_; uint8_t v_isDescr_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; 
v_decl_5249_ = lean_ctor_get(v_t_5245_, 0);
lean_inc(v_decl_5249_);
v_isDescr_5250_ = lean_ctor_get_uint8(v_t_5245_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5245_, 1);
v___x_5251_ = lean_box(v_isDescr_5250_);
v___x_5252_ = lean_apply_2(v_k_5246_, v_decl_5249_, v___x_5251_);
return v___x_5252_;
}
default: 
{
lean_object* v_p_5253_; lean_object* v___x_5254_; 
v_p_5253_ = lean_ctor_get(v_t_5245_, 0);
lean_inc_ref(v_p_5253_);
lean_dec_ref_known(v_t_5245_, 1);
v___x_5254_ = lean_apply_1(v_k_5246_, v_p_5253_);
return v___x_5254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object* v_motive_5255_, lean_object* v_ctorIdx_5256_, lean_object* v_t_5257_, lean_object* v_h_5258_, lean_object* v_k_5259_){
_start:
{
lean_object* v___x_5260_; 
v___x_5260_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5257_, v_k_5259_);
return v___x_5260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object* v_motive_5261_, lean_object* v_ctorIdx_5262_, lean_object* v_t_5263_, lean_object* v_h_5264_, lean_object* v_k_5265_){
_start:
{
lean_object* v_res_5266_; 
v_res_5266_ = l_Lean_Parser_ParserResolution_ctorElim(v_motive_5261_, v_ctorIdx_5262_, v_t_5263_, v_h_5264_, v_k_5265_);
lean_dec(v_ctorIdx_5262_);
return v_res_5266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object* v_t_5267_, lean_object* v_category_5268_){
_start:
{
lean_object* v___x_5269_; 
v___x_5269_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5267_, v_category_5268_);
return v___x_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object* v_motive_5270_, lean_object* v_t_5271_, lean_object* v_h_5272_, lean_object* v_category_5273_){
_start:
{
lean_object* v___x_5274_; 
v___x_5274_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5271_, v_category_5273_);
return v___x_5274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object* v_t_5275_, lean_object* v_parser_5276_){
_start:
{
lean_object* v___x_5277_; 
v___x_5277_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5275_, v_parser_5276_);
return v___x_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object* v_motive_5278_, lean_object* v_t_5279_, lean_object* v_h_5280_, lean_object* v_parser_5281_){
_start:
{
lean_object* v___x_5282_; 
v___x_5282_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5279_, v_parser_5281_);
return v___x_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object* v_t_5283_, lean_object* v_alias_5284_){
_start:
{
lean_object* v___x_5285_; 
v___x_5285_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5283_, v_alias_5284_);
return v___x_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object* v_motive_5286_, lean_object* v_t_5287_, lean_object* v_h_5288_, lean_object* v_alias_5289_){
_start:
{
lean_object* v___x_5290_; 
v___x_5290_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5287_, v_alias_5289_);
return v___x_5290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object* v_env_5294_, lean_object* v_name_5295_){
_start:
{
uint8_t v___x_5296_; lean_object* v___x_5297_; 
v___x_5296_ = 0;
v___x_5297_ = l_Lean_Environment_find_x3f(v_env_5294_, v_name_5295_, v___x_5296_);
if (lean_obj_tag(v___x_5297_) == 0)
{
lean_object* v___x_5298_; 
v___x_5298_ = lean_box(0);
return v___x_5298_;
}
else
{
lean_object* v_val_5299_; lean_object* v___x_5301_; uint8_t v_isShared_5302_; uint8_t v_isSharedCheck_5346_; 
v_val_5299_ = lean_ctor_get(v___x_5297_, 0);
v_isSharedCheck_5346_ = !lean_is_exclusive(v___x_5297_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5301_ = v___x_5297_;
v_isShared_5302_ = v_isSharedCheck_5346_;
goto v_resetjp_5300_;
}
else
{
lean_inc(v_val_5299_);
lean_dec(v___x_5297_);
v___x_5301_ = lean_box(0);
v_isShared_5302_ = v_isSharedCheck_5346_;
goto v_resetjp_5300_;
}
v_resetjp_5300_:
{
lean_object* v___x_5303_; 
v___x_5303_ = l_Lean_ConstantInfo_type(v_val_5299_);
lean_dec(v_val_5299_);
if (lean_obj_tag(v___x_5303_) == 4)
{
lean_object* v_declName_5304_; 
v_declName_5304_ = lean_ctor_get(v___x_5303_, 0);
lean_inc(v_declName_5304_);
lean_dec_ref_known(v___x_5303_, 2);
if (lean_obj_tag(v_declName_5304_) == 1)
{
lean_object* v_pre_5305_; 
v_pre_5305_ = lean_ctor_get(v_declName_5304_, 0);
lean_inc(v_pre_5305_);
if (lean_obj_tag(v_pre_5305_) == 1)
{
lean_object* v_pre_5306_; 
v_pre_5306_ = lean_ctor_get(v_pre_5305_, 0);
switch(lean_obj_tag(v_pre_5306_))
{
case 1:
{
lean_object* v_pre_5307_; 
lean_inc_ref(v_pre_5306_);
lean_del_object(v___x_5301_);
v_pre_5307_ = lean_ctor_get(v_pre_5306_, 0);
if (lean_obj_tag(v_pre_5307_) == 0)
{
lean_object* v_str_5308_; lean_object* v_str_5309_; lean_object* v_str_5310_; lean_object* v___x_5311_; uint8_t v___x_5312_; 
v_str_5308_ = lean_ctor_get(v_declName_5304_, 1);
lean_inc_ref(v_str_5308_);
lean_dec_ref_known(v_declName_5304_, 2);
v_str_5309_ = lean_ctor_get(v_pre_5305_, 1);
lean_inc_ref(v_str_5309_);
lean_dec_ref_known(v_pre_5305_, 2);
v_str_5310_ = lean_ctor_get(v_pre_5306_, 1);
lean_inc_ref(v_str_5310_);
lean_dec_ref_known(v_pre_5306_, 2);
v___x_5311_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5312_ = lean_string_dec_eq(v_str_5310_, v___x_5311_);
lean_dec_ref(v_str_5310_);
if (v___x_5312_ == 0)
{
lean_object* v___x_5313_; 
lean_dec_ref(v_str_5309_);
lean_dec_ref(v_str_5308_);
v___x_5313_ = lean_box(0);
return v___x_5313_;
}
else
{
lean_object* v___x_5314_; uint8_t v___x_5315_; 
v___x_5314_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_5315_ = lean_string_dec_eq(v_str_5309_, v___x_5314_);
lean_dec_ref(v_str_5309_);
if (v___x_5315_ == 0)
{
lean_object* v___x_5316_; 
lean_dec_ref(v_str_5308_);
v___x_5316_ = lean_box(0);
return v___x_5316_;
}
else
{
uint8_t v___x_5317_; 
v___x_5317_ = lean_string_dec_eq(v_str_5308_, v___x_5314_);
if (v___x_5317_ == 0)
{
lean_object* v___x_5318_; uint8_t v___x_5319_; 
v___x_5318_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_5319_ = lean_string_dec_eq(v_str_5308_, v___x_5318_);
lean_dec_ref(v_str_5308_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5320_; 
v___x_5320_ = lean_box(0);
return v___x_5320_;
}
else
{
lean_object* v___x_5321_; 
v___x_5321_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5321_;
}
}
else
{
lean_object* v___x_5322_; 
lean_dec_ref(v_str_5308_);
v___x_5322_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5322_;
}
}
}
}
else
{
lean_object* v___x_5323_; 
lean_dec_ref_known(v_pre_5306_, 2);
lean_dec_ref_known(v_pre_5305_, 2);
lean_dec_ref_known(v_declName_5304_, 2);
v___x_5323_ = lean_box(0);
return v___x_5323_;
}
}
case 0:
{
lean_object* v_str_5324_; lean_object* v_str_5325_; lean_object* v___x_5326_; uint8_t v___x_5327_; 
v_str_5324_ = lean_ctor_get(v_declName_5304_, 1);
lean_inc_ref(v_str_5324_);
lean_dec_ref_known(v_declName_5304_, 2);
v_str_5325_ = lean_ctor_get(v_pre_5305_, 1);
lean_inc_ref(v_str_5325_);
lean_dec_ref_known(v_pre_5305_, 2);
v___x_5326_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5327_ = lean_string_dec_eq(v_str_5325_, v___x_5326_);
lean_dec_ref(v_str_5325_);
if (v___x_5327_ == 0)
{
lean_object* v___x_5328_; 
lean_dec_ref(v_str_5324_);
lean_del_object(v___x_5301_);
v___x_5328_ = lean_box(0);
return v___x_5328_;
}
else
{
lean_object* v___x_5329_; uint8_t v___x_5330_; 
v___x_5329_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_5330_ = lean_string_dec_eq(v_str_5324_, v___x_5329_);
if (v___x_5330_ == 0)
{
lean_object* v___x_5331_; uint8_t v___x_5332_; 
v___x_5331_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_5332_ = lean_string_dec_eq(v_str_5324_, v___x_5331_);
lean_dec_ref(v_str_5324_);
if (v___x_5332_ == 0)
{
lean_object* v___x_5333_; 
lean_del_object(v___x_5301_);
v___x_5333_ = lean_box(0);
return v___x_5333_;
}
else
{
lean_object* v___x_5334_; lean_object* v___x_5336_; 
v___x_5334_ = lean_box(v___x_5327_);
if (v_isShared_5302_ == 0)
{
lean_ctor_set(v___x_5301_, 0, v___x_5334_);
v___x_5336_ = v___x_5301_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5337_; 
v_reuseFailAlloc_5337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5337_, 0, v___x_5334_);
v___x_5336_ = v_reuseFailAlloc_5337_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
return v___x_5336_;
}
}
}
else
{
lean_object* v___x_5338_; lean_object* v___x_5340_; 
lean_dec_ref(v_str_5324_);
v___x_5338_ = lean_box(v___x_5327_);
if (v_isShared_5302_ == 0)
{
lean_ctor_set(v___x_5301_, 0, v___x_5338_);
v___x_5340_ = v___x_5301_;
goto v_reusejp_5339_;
}
else
{
lean_object* v_reuseFailAlloc_5341_; 
v_reuseFailAlloc_5341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5341_, 0, v___x_5338_);
v___x_5340_ = v_reuseFailAlloc_5341_;
goto v_reusejp_5339_;
}
v_reusejp_5339_:
{
return v___x_5340_;
}
}
}
}
default: 
{
lean_object* v___x_5342_; 
lean_dec_ref_known(v_pre_5305_, 2);
lean_dec_ref_known(v_declName_5304_, 2);
lean_del_object(v___x_5301_);
v___x_5342_ = lean_box(0);
return v___x_5342_;
}
}
}
else
{
lean_object* v___x_5343_; 
lean_dec_ref_known(v_declName_5304_, 2);
lean_dec(v_pre_5305_);
lean_del_object(v___x_5301_);
v___x_5343_ = lean_box(0);
return v___x_5343_;
}
}
else
{
lean_object* v___x_5344_; 
lean_dec(v_declName_5304_);
lean_del_object(v___x_5301_);
v___x_5344_ = lean_box(0);
return v___x_5344_;
}
}
else
{
lean_object* v___x_5345_; 
lean_dec_ref(v___x_5303_);
lean_del_object(v___x_5301_);
v___x_5345_ = lean_box(0);
return v___x_5345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object* v_env_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_){
_start:
{
if (lean_obj_tag(v_a_5348_) == 0)
{
lean_object* v___x_5350_; 
lean_dec_ref(v_env_5347_);
v___x_5350_ = lean_array_to_list(v_a_5349_);
return v___x_5350_;
}
else
{
lean_object* v_head_5351_; lean_object* v_snd_5352_; 
v_head_5351_ = lean_ctor_get(v_a_5348_, 0);
v_snd_5352_ = lean_ctor_get(v_head_5351_, 1);
if (lean_obj_tag(v_snd_5352_) == 0)
{
lean_object* v_tail_5353_; lean_object* v_fst_5354_; lean_object* v___x_5355_; 
lean_inc(v_head_5351_);
v_tail_5353_ = lean_ctor_get(v_a_5348_, 1);
lean_inc(v_tail_5353_);
lean_dec_ref_known(v_a_5348_, 2);
v_fst_5354_ = lean_ctor_get(v_head_5351_, 0);
lean_inc_n(v_fst_5354_, 2);
lean_dec(v_head_5351_);
lean_inc_ref(v_env_5347_);
v___x_5355_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5347_, v_fst_5354_);
if (lean_obj_tag(v___x_5355_) == 0)
{
lean_dec(v_fst_5354_);
v_a_5348_ = v_tail_5353_;
goto _start;
}
else
{
lean_object* v_val_5357_; lean_object* v___x_5358_; uint8_t v___x_5359_; lean_object* v___x_5360_; 
v_val_5357_ = lean_ctor_get(v___x_5355_, 0);
lean_inc(v_val_5357_);
lean_dec_ref_known(v___x_5355_, 1);
v___x_5358_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5358_, 0, v_fst_5354_);
v___x_5359_ = lean_unbox(v_val_5357_);
lean_dec(v_val_5357_);
lean_ctor_set_uint8(v___x_5358_, sizeof(void*)*1, v___x_5359_);
v___x_5360_ = lean_array_push(v_a_5349_, v___x_5358_);
v_a_5348_ = v_tail_5353_;
v_a_5349_ = v___x_5360_;
goto _start;
}
}
else
{
lean_object* v_tail_5362_; 
v_tail_5362_ = lean_ctor_get(v_a_5348_, 1);
lean_inc(v_tail_5362_);
lean_dec_ref_known(v_a_5348_, 2);
v_a_5348_ = v_tail_5362_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object* v_env_5367_, lean_object* v_as_x27_5368_, lean_object* v_b_5369_){
_start:
{
if (lean_obj_tag(v_as_x27_5368_) == 0)
{
lean_dec_ref(v_env_5367_);
lean_inc_ref(v_b_5369_);
return v_b_5369_;
}
else
{
lean_object* v_head_5370_; lean_object* v_tail_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; 
v_head_5370_ = lean_ctor_get(v_as_x27_5368_, 0);
v_tail_5371_ = lean_ctor_get(v_as_x27_5368_, 1);
v___x_5372_ = lean_box(0);
v___x_5373_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_5370_) == 1)
{
lean_object* v_fields_5374_; 
v_fields_5374_ = lean_ctor_get(v_head_5370_, 1);
if (lean_obj_tag(v_fields_5374_) == 0)
{
lean_object* v_n_5375_; lean_object* v___x_5376_; 
v_n_5375_ = lean_ctor_get(v_head_5370_, 0);
lean_inc(v_n_5375_);
lean_inc_ref(v_env_5367_);
v___x_5376_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5367_, v_n_5375_);
if (lean_obj_tag(v___x_5376_) == 1)
{
lean_object* v_val_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5389_; 
lean_dec_ref(v_env_5367_);
v_val_5377_ = lean_ctor_get(v___x_5376_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5376_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5379_ = v___x_5376_;
v_isShared_5380_ = v_isSharedCheck_5389_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_val_5377_);
lean_dec(v___x_5376_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5389_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5381_; uint8_t v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5386_; 
lean_inc(v_n_5375_);
v___x_5381_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5381_, 0, v_n_5375_);
v___x_5382_ = lean_unbox(v_val_5377_);
lean_dec(v_val_5377_);
lean_ctor_set_uint8(v___x_5381_, sizeof(void*)*1, v___x_5382_);
v___x_5383_ = lean_box(0);
v___x_5384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5384_, 0, v___x_5381_);
lean_ctor_set(v___x_5384_, 1, v___x_5383_);
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 0, v___x_5384_);
v___x_5386_ = v___x_5379_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v___x_5384_);
v___x_5386_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
lean_object* v___x_5387_; 
v___x_5387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5386_);
lean_ctor_set(v___x_5387_, 1, v___x_5372_);
return v___x_5387_;
}
}
}
else
{
lean_dec(v___x_5376_);
v_as_x27_5368_ = v_tail_5371_;
v_b_5369_ = v___x_5373_;
goto _start;
}
}
else
{
v_as_x27_5368_ = v_tail_5371_;
v_b_5369_ = v___x_5373_;
goto _start;
}
}
else
{
v_as_x27_5368_ = v_tail_5371_;
v_b_5369_ = v___x_5373_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object* v_env_5393_, lean_object* v_as_x27_5394_, lean_object* v_b_5395_){
_start:
{
lean_object* v_res_5396_; 
v_res_5396_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5393_, v_as_x27_5394_, v_b_5395_);
lean_dec_ref(v_b_5395_);
lean_dec(v_as_x27_5394_);
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object* v_env_5399_, lean_object* v_opts_5400_, lean_object* v_currNamespace_5401_, lean_object* v_openDecls_5402_, lean_object* v_ident_5403_){
_start:
{
if (lean_obj_tag(v_ident_5403_) == 3)
{
lean_object* v_val_5404_; lean_object* v_preresolved_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v_fst_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5443_; 
v_val_5404_ = lean_ctor_get(v_ident_5403_, 2);
lean_inc(v_val_5404_);
v_preresolved_5405_ = lean_ctor_get(v_ident_5403_, 3);
lean_inc(v_preresolved_5405_);
lean_dec_ref_known(v_ident_5403_, 4);
v___x_5406_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
lean_inc_ref(v_env_5399_);
v___x_5407_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5399_, v_preresolved_5405_, v___x_5406_);
lean_dec(v_preresolved_5405_);
v_fst_5408_ = lean_ctor_get(v___x_5407_, 0);
v_isSharedCheck_5443_ = !lean_is_exclusive(v___x_5407_);
if (v_isSharedCheck_5443_ == 0)
{
lean_object* v_unused_5444_; 
v_unused_5444_ = lean_ctor_get(v___x_5407_, 1);
lean_dec(v_unused_5444_);
v___x_5410_ = v___x_5407_;
v_isShared_5411_ = v_isSharedCheck_5443_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_fst_5408_);
lean_dec(v___x_5407_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5443_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
if (lean_obj_tag(v_fst_5408_) == 0)
{
lean_object* v___x_5412_; uint8_t v___x_5413_; 
v___x_5412_ = l_Lean_Name_eraseMacroScopes(v_val_5404_);
lean_inc_ref(v_env_5399_);
v___x_5413_ = l_Lean_Parser_isParserCategory(v_env_5399_, v___x_5412_);
if (v___x_5413_ == 0)
{
lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; uint8_t v___x_5417_; 
lean_inc_ref_n(v_env_5399_, 2);
v___x_5414_ = l_Lean_ResolveName_resolveGlobalName(v_env_5399_, v_opts_5400_, v_currNamespace_5401_, v_openDecls_5402_, v_val_5404_);
v___x_5415_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0));
v___x_5416_ = l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(v_env_5399_, v___x_5414_, v___x_5415_);
v___x_5417_ = l_List_isEmpty___redArg(v___x_5416_);
if (v___x_5417_ == 0)
{
lean_dec(v___x_5412_);
lean_del_object(v___x_5410_);
lean_dec_ref(v_env_5399_);
return v___x_5416_;
}
else
{
lean_object* v___x_5418_; lean_object* v_asyncMode_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; 
lean_dec(v___x_5416_);
v___x_5418_ = l_Lean_Parser_aliasExtension;
v_asyncMode_5419_ = lean_ctor_get(v___x_5418_, 2);
v___x_5420_ = lean_box(1);
v___x_5421_ = lean_box(0);
v___x_5422_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5420_, v___x_5418_, v_env_5399_, v_asyncMode_5419_, v___x_5421_, v___x_5413_);
v___x_5423_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5422_, v___x_5412_);
lean_dec(v___x_5412_);
lean_dec(v___x_5422_);
if (lean_obj_tag(v___x_5423_) == 1)
{
lean_object* v_val_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5435_; 
v_val_5424_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5426_ = v___x_5423_;
v_isShared_5427_ = v_isSharedCheck_5435_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_val_5424_);
lean_dec(v___x_5423_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5435_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
lean_ctor_set_tag(v___x_5426_, 2);
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_val_5424_);
v___x_5429_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
lean_object* v___x_5430_; lean_object* v___x_5432_; 
v___x_5430_ = lean_box(0);
if (v_isShared_5411_ == 0)
{
lean_ctor_set_tag(v___x_5410_, 1);
lean_ctor_set(v___x_5410_, 1, v___x_5430_);
lean_ctor_set(v___x_5410_, 0, v___x_5429_);
v___x_5432_ = v___x_5410_;
goto v_reusejp_5431_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v___x_5429_);
lean_ctor_set(v_reuseFailAlloc_5433_, 1, v___x_5430_);
v___x_5432_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5431_;
}
v_reusejp_5431_:
{
return v___x_5432_;
}
}
}
}
else
{
lean_object* v___x_5436_; 
lean_dec(v___x_5423_);
lean_del_object(v___x_5410_);
v___x_5436_ = lean_box(0);
return v___x_5436_;
}
}
}
else
{
lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5440_; 
lean_dec(v_val_5404_);
lean_dec(v_openDecls_5402_);
lean_dec(v_currNamespace_5401_);
lean_dec_ref(v_env_5399_);
v___x_5437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5437_, 0, v___x_5412_);
v___x_5438_ = lean_box(0);
if (v_isShared_5411_ == 0)
{
lean_ctor_set_tag(v___x_5410_, 1);
lean_ctor_set(v___x_5410_, 1, v___x_5438_);
lean_ctor_set(v___x_5410_, 0, v___x_5437_);
v___x_5440_ = v___x_5410_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v___x_5437_);
lean_ctor_set(v_reuseFailAlloc_5441_, 1, v___x_5438_);
v___x_5440_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
return v___x_5440_;
}
}
}
else
{
lean_object* v_val_5442_; 
lean_del_object(v___x_5410_);
lean_dec(v_val_5404_);
lean_dec(v_openDecls_5402_);
lean_dec(v_currNamespace_5401_);
lean_dec_ref(v_env_5399_);
v_val_5442_ = lean_ctor_get(v_fst_5408_, 0);
lean_inc(v_val_5442_);
lean_dec_ref_known(v_fst_5408_, 1);
return v_val_5442_;
}
}
}
else
{
lean_object* v___x_5445_; 
lean_dec(v_ident_5403_);
lean_dec(v_openDecls_5402_);
lean_dec(v_currNamespace_5401_);
lean_dec_ref(v_env_5399_);
v___x_5445_ = lean_box(0);
return v___x_5445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object* v_env_5446_, lean_object* v_opts_5447_, lean_object* v_currNamespace_5448_, lean_object* v_openDecls_5449_, lean_object* v_ident_5450_){
_start:
{
lean_object* v_res_5451_; 
v_res_5451_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5446_, v_opts_5447_, v_currNamespace_5448_, v_openDecls_5449_, v_ident_5450_);
lean_dec_ref(v_opts_5447_);
return v_res_5451_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object* v_env_5452_, lean_object* v_as_5453_, lean_object* v_as_x27_5454_, lean_object* v_b_5455_, lean_object* v_a_5456_){
_start:
{
lean_object* v___x_5457_; 
v___x_5457_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5452_, v_as_x27_5454_, v_b_5455_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object* v_env_5458_, lean_object* v_as_5459_, lean_object* v_as_x27_5460_, lean_object* v_b_5461_, lean_object* v_a_5462_){
_start:
{
lean_object* v_res_5463_; 
v_res_5463_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(v_env_5458_, v_as_5459_, v_as_x27_5460_, v_b_5461_, v_a_5462_);
lean_dec_ref(v_b_5461_);
lean_dec(v_as_x27_5460_);
lean_dec(v_as_5459_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object* v_ctx_5464_, lean_object* v_id_5465_, uint8_t v_unsetExporting_5466_){
_start:
{
lean_object* v___y_5468_; 
if (v_unsetExporting_5466_ == 0)
{
lean_object* v_toParserModuleContext_5474_; lean_object* v_env_5475_; 
v_toParserModuleContext_5474_ = lean_ctor_get(v_ctx_5464_, 1);
v_env_5475_ = lean_ctor_get(v_toParserModuleContext_5474_, 0);
lean_inc_ref(v_env_5475_);
v___y_5468_ = v_env_5475_;
goto v___jp_5467_;
}
else
{
lean_object* v_toParserModuleContext_5476_; lean_object* v_env_5477_; uint8_t v___x_5478_; lean_object* v___x_5479_; 
v_toParserModuleContext_5476_ = lean_ctor_get(v_ctx_5464_, 1);
v_env_5477_ = lean_ctor_get(v_toParserModuleContext_5476_, 0);
v___x_5478_ = 0;
lean_inc_ref(v_env_5477_);
v___x_5479_ = l_Lean_Environment_setExporting(v_env_5477_, v___x_5478_);
v___y_5468_ = v___x_5479_;
goto v___jp_5467_;
}
v___jp_5467_:
{
lean_object* v_toParserModuleContext_5469_; lean_object* v_options_5470_; lean_object* v_currNamespace_5471_; lean_object* v_openDecls_5472_; lean_object* v___x_5473_; 
v_toParserModuleContext_5469_ = lean_ctor_get(v_ctx_5464_, 1);
lean_inc_ref(v_toParserModuleContext_5469_);
lean_dec_ref(v_ctx_5464_);
v_options_5470_ = lean_ctor_get(v_toParserModuleContext_5469_, 1);
lean_inc_ref(v_options_5470_);
v_currNamespace_5471_ = lean_ctor_get(v_toParserModuleContext_5469_, 2);
lean_inc(v_currNamespace_5471_);
v_openDecls_5472_ = lean_ctor_get(v_toParserModuleContext_5469_, 3);
lean_inc(v_openDecls_5472_);
lean_dec_ref(v_toParserModuleContext_5469_);
v___x_5473_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v___y_5468_, v_options_5470_, v_currNamespace_5471_, v_openDecls_5472_, v_id_5465_);
lean_dec_ref(v_options_5470_);
return v___x_5473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object* v_ctx_5480_, lean_object* v_id_5481_, lean_object* v_unsetExporting_5482_){
_start:
{
uint8_t v_unsetExporting_boxed_5483_; lean_object* v_res_5484_; 
v_unsetExporting_boxed_5483_ = lean_unbox(v_unsetExporting_5482_);
v_res_5484_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5480_, v_id_5481_, v_unsetExporting_boxed_5483_);
return v_res_5484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object* v_id_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_){
_start:
{
lean_object* v___x_5489_; lean_object* v_toCold_5490_; lean_object* v_env_5491_; lean_object* v_currNamespace_5492_; lean_object* v_openDecls_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; 
v___x_5489_ = lean_st_ref_get(v_a_5487_);
v_toCold_5490_ = lean_ctor_get(v_a_5486_, 0);
v_env_5491_ = lean_ctor_get(v___x_5489_, 0);
lean_inc_ref(v_env_5491_);
lean_dec(v___x_5489_);
v_currNamespace_5492_ = lean_ctor_get(v_toCold_5490_, 4);
v_openDecls_5493_ = lean_ctor_get(v_toCold_5490_, 5);
v___x_5494_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_5486_);
lean_inc(v_openDecls_5493_);
lean_inc(v_currNamespace_5492_);
v___x_5495_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5491_, v___x_5494_, v_currNamespace_5492_, v_openDecls_5493_, v_id_5485_);
lean_dec_ref(v___x_5494_);
v___x_5496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5496_, 0, v___x_5495_);
return v___x_5496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object* v_id_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_){
_start:
{
lean_object* v_res_5501_; 
v_res_5501_ = l_Lean_Parser_resolveParserName(v_id_5497_, v_a_5498_, v_a_5499_);
lean_dec(v_a_5499_);
lean_dec_ref(v_a_5498_);
return v_res_5501_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object* v_x_5502_, lean_object* v_x_5503_){
_start:
{
if (lean_obj_tag(v_x_5502_) == 0)
{
if (lean_obj_tag(v_x_5503_) == 0)
{
uint8_t v___x_5504_; 
v___x_5504_ = 1;
return v___x_5504_;
}
else
{
uint8_t v___x_5505_; 
v___x_5505_ = 0;
return v___x_5505_;
}
}
else
{
if (lean_obj_tag(v_x_5503_) == 0)
{
uint8_t v___x_5506_; 
v___x_5506_ = 0;
return v___x_5506_;
}
else
{
lean_object* v_val_5507_; lean_object* v_val_5508_; uint8_t v___x_5509_; 
v_val_5507_ = lean_ctor_get(v_x_5502_, 0);
v_val_5508_ = lean_ctor_get(v_x_5503_, 0);
v___x_5509_ = l_Lean_Parser_instBEqError_beq(v_val_5507_, v_val_5508_);
return v___x_5509_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object* v_x_5510_, lean_object* v_x_5511_){
_start:
{
uint8_t v_res_5512_; lean_object* v_r_5513_; 
v_res_5512_ = l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5510_, v_x_5511_);
lean_dec(v_x_5511_);
lean_dec(v_x_5510_);
v_r_5513_ = lean_box(v_res_5512_);
return v_r_5513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t v___x_5514_, lean_object* v_ctx_5515_){
_start:
{
lean_object* v_toParserModuleContext_5516_; lean_object* v_toInputContext_5517_; lean_object* v_toCacheableParserContext_5518_; lean_object* v_tokens_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5544_; 
v_toParserModuleContext_5516_ = lean_ctor_get(v_ctx_5515_, 1);
v_toInputContext_5517_ = lean_ctor_get(v_ctx_5515_, 0);
v_toCacheableParserContext_5518_ = lean_ctor_get(v_ctx_5515_, 2);
v_tokens_5519_ = lean_ctor_get(v_ctx_5515_, 3);
v_isSharedCheck_5544_ = !lean_is_exclusive(v_ctx_5515_);
if (v_isSharedCheck_5544_ == 0)
{
v___x_5521_ = v_ctx_5515_;
v_isShared_5522_ = v_isSharedCheck_5544_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_tokens_5519_);
lean_inc(v_toCacheableParserContext_5518_);
lean_inc(v_toParserModuleContext_5516_);
lean_inc(v_toInputContext_5517_);
lean_dec(v_ctx_5515_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5544_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v_env_5523_; lean_object* v_options_5524_; lean_object* v_currNamespace_5525_; lean_object* v_openDecls_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5543_; 
v_env_5523_ = lean_ctor_get(v_toParserModuleContext_5516_, 0);
v_options_5524_ = lean_ctor_get(v_toParserModuleContext_5516_, 1);
v_currNamespace_5525_ = lean_ctor_get(v_toParserModuleContext_5516_, 2);
v_openDecls_5526_ = lean_ctor_get(v_toParserModuleContext_5516_, 3);
v_isSharedCheck_5543_ = !lean_is_exclusive(v_toParserModuleContext_5516_);
if (v_isSharedCheck_5543_ == 0)
{
v___x_5528_ = v_toParserModuleContext_5516_;
v_isShared_5529_ = v_isSharedCheck_5543_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_openDecls_5526_);
lean_inc(v_currNamespace_5525_);
lean_inc(v_options_5524_);
lean_inc(v_env_5523_);
lean_dec(v_toParserModuleContext_5516_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5543_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5530_; uint8_t v___y_5532_; lean_object* v___x_5540_; uint8_t v___x_5541_; 
v___x_5530_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_5540_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_5541_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_5524_, v___x_5540_);
if (v___x_5541_ == 0)
{
uint8_t v___x_5542_; 
v___x_5542_ = 1;
v___y_5532_ = v___x_5542_;
goto v___jp_5531_;
}
else
{
v___y_5532_ = v___x_5514_;
goto v___jp_5531_;
}
v___jp_5531_:
{
lean_object* v___x_5533_; lean_object* v___x_5535_; 
v___x_5533_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_5524_, v___x_5530_, v___y_5532_);
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 1, v___x_5533_);
v___x_5535_ = v___x_5528_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_env_5523_);
lean_ctor_set(v_reuseFailAlloc_5539_, 1, v___x_5533_);
lean_ctor_set(v_reuseFailAlloc_5539_, 2, v_currNamespace_5525_);
lean_ctor_set(v_reuseFailAlloc_5539_, 3, v_openDecls_5526_);
v___x_5535_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
lean_object* v___x_5537_; 
if (v_isShared_5522_ == 0)
{
lean_ctor_set(v___x_5521_, 1, v___x_5535_);
v___x_5537_ = v___x_5521_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_toInputContext_5517_);
lean_ctor_set(v_reuseFailAlloc_5538_, 1, v___x_5535_);
lean_ctor_set(v_reuseFailAlloc_5538_, 2, v_toCacheableParserContext_5518_);
lean_ctor_set(v_reuseFailAlloc_5538_, 3, v_tokens_5519_);
v___x_5537_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
return v___x_5537_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object* v___x_5545_, lean_object* v_ctx_5546_){
_start:
{
uint8_t v___x_1069__boxed_5547_; lean_object* v_res_5548_; 
v___x_1069__boxed_5547_ = lean_unbox(v___x_5545_);
v_res_5548_ = l_Lean_Parser_parserOfStackFn___lam__0(v___x_1069__boxed_5547_, v_ctx_5546_);
return v_res_5548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* v_offset_5556_, lean_object* v_ctx_5557_, lean_object* v_s_5558_){
_start:
{
lean_object* v_stxStack_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; uint8_t v___x_5563_; 
v_stxStack_5559_ = lean_ctor_get(v_s_5558_, 0);
v___x_5560_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5559_);
v___x_5561_ = lean_unsigned_to_nat(1u);
v___x_5562_ = lean_nat_add(v_offset_5556_, v___x_5561_);
v___x_5563_ = lean_nat_dec_lt(v___x_5560_, v___x_5562_);
lean_dec(v___x_5562_);
if (v___x_5563_ == 0)
{
lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; 
v___x_5564_ = lean_nat_sub(v___x_5560_, v_offset_5556_);
lean_dec(v___x_5560_);
v___x_5565_ = lean_nat_sub(v___x_5564_, v___x_5561_);
lean_dec(v___x_5564_);
v___x_5566_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5559_, v___x_5565_);
lean_dec(v___x_5565_);
if (lean_obj_tag(v___x_5566_) == 3)
{
uint8_t v___x_5578_; lean_object* v___x_5579_; 
v___x_5578_ = 1;
lean_inc_ref(v___x_5566_);
lean_inc_ref(v_ctx_5557_);
v___x_5579_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5557_, v___x_5566_, v___x_5578_);
if (lean_obj_tag(v___x_5579_) == 0)
{
lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; 
lean_dec_ref(v_ctx_5557_);
v___x_5580_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__1));
v___x_5581_ = lean_box(0);
v___x_5582_ = l_Lean_Syntax_formatStx(v___x_5566_, v___x_5581_, v___x_5563_);
v___x_5583_ = l_Std_Format_defWidth;
v___x_5584_ = lean_unsigned_to_nat(0u);
v___x_5585_ = l_Std_Format_pretty(v___x_5582_, v___x_5583_, v___x_5584_, v___x_5584_);
v___x_5586_ = lean_string_append(v___x_5580_, v___x_5585_);
lean_dec_ref(v___x_5585_);
v___x_5587_ = lean_box(0);
v___x_5588_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5558_, v___x_5586_, v___x_5587_, v___x_5578_);
return v___x_5588_;
}
else
{
lean_object* v_head_5589_; lean_object* v_tail_5590_; lean_object* v_iniSz_5591_; lean_object* v_s_5593_; 
v_head_5589_ = lean_ctor_get(v___x_5579_, 0);
lean_inc(v_head_5589_);
v_tail_5590_ = lean_ctor_get(v___x_5579_, 1);
lean_inc(v_tail_5590_);
lean_dec_ref_known(v___x_5579_, 2);
v_iniSz_5591_ = l_Lean_Parser_ParserState_stackSize(v_s_5558_);
switch(lean_obj_tag(v_head_5589_))
{
case 0:
{
if (lean_obj_tag(v_tail_5590_) == 0)
{
lean_object* v_cat_5603_; lean_object* v___x_5604_; 
lean_dec_ref_known(v___x_5566_, 4);
v_cat_5603_ = lean_ctor_get(v_head_5589_, 0);
lean_inc(v_cat_5603_);
lean_dec_ref_known(v_head_5589_, 1);
v___x_5604_ = l_Lean_Parser_categoryParserFn(v_cat_5603_, v_ctx_5557_, v_s_5558_);
v_s_5593_ = v___x_5604_;
goto v___jp_5592_;
}
else
{
lean_dec_ref_known(v_tail_5590_, 2);
lean_dec_ref_known(v_head_5589_, 1);
lean_dec(v_iniSz_5591_);
lean_dec_ref(v_ctx_5557_);
goto v___jp_5567_;
}
}
case 1:
{
if (lean_obj_tag(v_tail_5590_) == 0)
{
lean_object* v_decl_5605_; lean_object* v___x_5606_; lean_object* v___f_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; 
lean_dec_ref_known(v___x_5566_, 4);
v_decl_5605_ = lean_ctor_get(v_head_5589_, 0);
lean_inc(v_decl_5605_);
lean_dec_ref_known(v_head_5589_, 1);
v___x_5606_ = lean_box(v___x_5563_);
v___f_5607_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5607_, 0, v___x_5606_);
v___x_5608_ = lean_box(0);
v___x_5609_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_5609_, 0, v_decl_5605_);
lean_closure_set(v___x_5609_, 1, v___x_5608_);
v___x_5610_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5607_, v___x_5609_, v_ctx_5557_, v_s_5558_);
v_s_5593_ = v___x_5610_;
goto v___jp_5592_;
}
else
{
lean_dec_ref_known(v_tail_5590_, 2);
lean_dec_ref_known(v_head_5589_, 1);
lean_dec(v_iniSz_5591_);
lean_dec_ref(v_ctx_5557_);
goto v___jp_5567_;
}
}
default: 
{
if (lean_obj_tag(v_tail_5590_) == 0)
{
lean_object* v_p_5611_; 
v_p_5611_ = lean_ctor_get(v_head_5589_, 0);
lean_inc_ref(v_p_5611_);
lean_dec_ref_known(v_head_5589_, 1);
if (lean_obj_tag(v_p_5611_) == 0)
{
lean_object* v_p_5612_; lean_object* v_fn_5613_; lean_object* v___x_5614_; 
lean_dec_ref_known(v___x_5566_, 4);
v_p_5612_ = lean_ctor_get(v_p_5611_, 0);
lean_inc(v_p_5612_);
lean_dec_ref_known(v_p_5611_, 1);
v_fn_5613_ = lean_ctor_get(v_p_5612_, 1);
lean_inc_ref(v_fn_5613_);
lean_dec(v_p_5612_);
v___x_5614_ = lean_apply_2(v_fn_5613_, v_ctx_5557_, v_s_5558_);
v_s_5593_ = v___x_5614_;
goto v___jp_5592_;
}
else
{
lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; 
lean_dec_ref(v_p_5611_);
lean_dec(v_iniSz_5591_);
lean_dec_ref(v_ctx_5557_);
v___x_5615_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__3));
v___x_5616_ = lean_box(0);
v___x_5617_ = l_Lean_Syntax_formatStx(v___x_5566_, v___x_5616_, v___x_5563_);
v___x_5618_ = l_Std_Format_defWidth;
v___x_5619_ = lean_unsigned_to_nat(0u);
v___x_5620_ = l_Std_Format_pretty(v___x_5617_, v___x_5618_, v___x_5619_, v___x_5619_);
v___x_5621_ = lean_string_append(v___x_5615_, v___x_5620_);
lean_dec_ref(v___x_5620_);
v___x_5622_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__4));
v___x_5623_ = lean_string_append(v___x_5621_, v___x_5622_);
v___x_5624_ = lean_box(0);
v___x_5625_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5558_, v___x_5623_, v___x_5624_, v___x_5578_);
return v___x_5625_;
}
}
else
{
lean_dec_ref_known(v_tail_5590_, 2);
lean_dec_ref_known(v_head_5589_, 1);
lean_dec(v_iniSz_5591_);
lean_dec_ref(v_ctx_5557_);
goto v___jp_5567_;
}
}
}
v___jp_5592_:
{
lean_object* v_errorMsg_5594_; lean_object* v___x_5595_; uint8_t v___x_5596_; 
v_errorMsg_5594_ = lean_ctor_get(v_s_5593_, 4);
v___x_5595_ = lean_box(0);
v___x_5596_ = l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_errorMsg_5594_, v___x_5595_);
if (v___x_5596_ == 0)
{
lean_dec(v_iniSz_5591_);
return v_s_5593_;
}
else
{
lean_object* v___x_5597_; lean_object* v___x_5598_; uint8_t v___x_5599_; 
v___x_5597_ = l_Lean_Parser_ParserState_stackSize(v_s_5593_);
v___x_5598_ = lean_nat_add(v_iniSz_5591_, v___x_5561_);
lean_dec(v_iniSz_5591_);
v___x_5599_ = lean_nat_dec_eq(v___x_5597_, v___x_5598_);
lean_dec(v___x_5598_);
lean_dec(v___x_5597_);
if (v___x_5599_ == 0)
{
lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; 
v___x_5600_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__2));
v___x_5601_ = lean_box(0);
v___x_5602_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5593_, v___x_5600_, v___x_5601_, v___x_5596_);
return v___x_5602_;
}
else
{
return v_s_5593_;
}
}
}
}
}
else
{
lean_object* v___x_5626_; lean_object* v___x_5627_; uint8_t v___x_5628_; lean_object* v___x_5629_; 
lean_dec(v___x_5566_);
lean_dec_ref(v_ctx_5557_);
v___x_5626_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__5));
v___x_5627_ = lean_box(0);
v___x_5628_ = 1;
v___x_5629_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5558_, v___x_5626_, v___x_5627_, v___x_5628_);
return v___x_5629_;
}
v___jp_5567_:
{
lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; uint8_t v___x_5576_; lean_object* v___x_5577_; 
v___x_5568_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__0));
v___x_5569_ = lean_box(0);
v___x_5570_ = l_Lean_Syntax_formatStx(v___x_5566_, v___x_5569_, v___x_5563_);
v___x_5571_ = l_Std_Format_defWidth;
v___x_5572_ = lean_unsigned_to_nat(0u);
v___x_5573_ = l_Std_Format_pretty(v___x_5570_, v___x_5571_, v___x_5572_, v___x_5572_);
v___x_5574_ = lean_string_append(v___x_5568_, v___x_5573_);
lean_dec_ref(v___x_5573_);
v___x_5575_ = lean_box(0);
v___x_5576_ = 1;
v___x_5577_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5558_, v___x_5574_, v___x_5575_, v___x_5576_);
return v___x_5577_;
}
}
else
{
lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; 
lean_dec(v___x_5560_);
lean_dec_ref(v_ctx_5557_);
v___x_5630_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__6));
v___x_5631_ = lean_box(0);
v___x_5632_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5558_, v___x_5630_, v___x_5631_, v___x_5563_);
return v___x_5632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* v_offset_5633_, lean_object* v_ctx_5634_, lean_object* v_s_5635_){
_start:
{
lean_object* v_res_5636_; 
v_res_5636_ = l_Lean_Parser_parserOfStackFn(v_offset_5633_, v_ctx_5634_, v_s_5635_);
lean_dec(v_offset_5633_);
return v_res_5636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object* v_prec_5637_, lean_object* v_x_5638_){
_start:
{
lean_object* v_quotDepth_5639_; uint8_t v_suppressInsideQuot_5640_; lean_object* v_savedPos_x3f_5641_; lean_object* v_forbiddenTks_5642_; lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5649_; 
v_quotDepth_5639_ = lean_ctor_get(v_x_5638_, 1);
v_suppressInsideQuot_5640_ = lean_ctor_get_uint8(v_x_5638_, sizeof(void*)*4);
v_savedPos_x3f_5641_ = lean_ctor_get(v_x_5638_, 2);
v_forbiddenTks_5642_ = lean_ctor_get(v_x_5638_, 3);
v_isSharedCheck_5649_ = !lean_is_exclusive(v_x_5638_);
if (v_isSharedCheck_5649_ == 0)
{
lean_object* v_unused_5650_; 
v_unused_5650_ = lean_ctor_get(v_x_5638_, 0);
lean_dec(v_unused_5650_);
v___x_5644_ = v_x_5638_;
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
else
{
lean_inc(v_forbiddenTks_5642_);
lean_inc(v_savedPos_x3f_5641_);
lean_inc(v_quotDepth_5639_);
lean_dec(v_x_5638_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v___x_5647_; 
if (v_isShared_5645_ == 0)
{
lean_ctor_set(v___x_5644_, 0, v_prec_5637_);
v___x_5647_ = v___x_5644_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_prec_5637_);
lean_ctor_set(v_reuseFailAlloc_5648_, 1, v_quotDepth_5639_);
lean_ctor_set(v_reuseFailAlloc_5648_, 2, v_savedPos_x3f_5641_);
lean_ctor_set(v_reuseFailAlloc_5648_, 3, v_forbiddenTks_5642_);
lean_ctor_set_uint8(v_reuseFailAlloc_5648_, sizeof(void*)*4, v_suppressInsideQuot_5640_);
v___x_5647_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
return v___x_5647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object* v___y_5651_){
_start:
{
lean_inc(v___y_5651_);
return v___y_5651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object* v___y_5652_){
_start:
{
lean_object* v_res_5653_; 
v_res_5653_ = l_Lean_Parser_parserOfStack___lam__1(v___y_5652_);
lean_dec(v___y_5652_);
return v_res_5653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object* v___y_5654_){
_start:
{
lean_inc_ref(v___y_5654_);
return v___y_5654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object* v___y_5655_){
_start:
{
lean_object* v_res_5656_; 
v_res_5656_ = l_Lean_Parser_parserOfStack___lam__2(v___y_5655_);
lean_dec_ref(v___y_5655_);
return v_res_5656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* v_offset_5663_, lean_object* v_prec_5664_){
_start:
{
lean_object* v___f_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; 
v___f_5665_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___lam__0), 2, 1);
lean_closure_set(v___f_5665_, 0, v_prec_5664_);
v___x_5666_ = ((lean_object*)(l_Lean_Parser_parserOfStack___closed__2));
v___x_5667_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___boxed), 3, 1);
lean_closure_set(v___x_5667_, 0, v_offset_5663_);
v___x_5668_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5668_, 0, v___f_5665_);
lean_closure_set(v___x_5668_, 1, v___x_5667_);
v___x_5669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5669_, 0, v___x_5666_);
lean_ctor_set(v___x_5669_, 1, v___x_5668_);
return v___x_5669_;
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
