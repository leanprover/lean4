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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__21;
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
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_6_;
v_res_6_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_();
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2____boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_();
return v_res_8_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_9_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_14_ = lean_st_mk_ref(v___x_13_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_16_;
v_res_16_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_();
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2____boxed(lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_();
return v_res_18_;
}
}
lean_object* l_Lean_Parser_registerBuiltinNodeKind(lean_object* v_k_19_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_21_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_22_ = lean_st_ref_take(v___x_21_);
v___x_23_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v___x_22_, v_k_19_);
v___x_24_ = lean_st_ref_put(v___x_21_, v___x_23_);
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT void l_Lean_Parser_registerBuiltinNodeKind_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_19_ = stack[0].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_Parser_registerBuiltinNodeKind(v_k_19_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinNodeKind___boxed(lean_object* v_k_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Parser_registerBuiltinNodeKind(v_k_27_);
return v_res_29_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_61_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_62_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_61_);
lean_dec_ref(v___x_62_);
v___x_63_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_64_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_63_);
lean_dec_ref(v___x_64_);
v___x_65_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_66_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_65_);
lean_dec_ref(v___x_66_);
v___x_67_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_68_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_67_);
lean_dec_ref(v___x_68_);
v___x_69_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_70_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_69_);
lean_dec_ref(v___x_70_);
v___x_71_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_72_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_71_);
lean_dec_ref(v___x_72_);
v___x_73_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_74_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_73_);
lean_dec_ref(v___x_74_);
v___x_75_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_76_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_75_);
lean_dec_ref(v___x_76_);
v___x_77_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_78_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_77_);
lean_dec_ref(v___x_78_);
v___x_79_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_));
v___x_80_ = l_Lean_Parser_registerBuiltinNodeKind(v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_81_;
v_res_81_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_();
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2____boxed(lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3496418232____hygCtx___hyg_2_();
return v_res_83_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_);
v___x_88_ = lean_st_mk_ref(v___x_87_);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_90_;
v_res_90_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2____boxed(lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3941088830____hygCtx___hyg_2_();
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(lean_object* v_catName_95_){
_start:
{
lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_96_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__0));
v___x_97_ = 1;
v___x_98_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_95_, v___x_97_);
v___x_99_ = lean_string_append(v___x_96_, v___x_98_);
lean_dec_ref(v___x_98_);
v___x_100_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg___closed__1));
v___x_101_ = lean_string_append(v___x_99_, v___x_100_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined(lean_object* v_00_u03b1_103_, lean_object* v_catName_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_106_, lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
lean_object* v_ks_110_; lean_object* v_vs_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_135_; 
v_ks_110_ = lean_ctor_get(v_x_106_, 0);
v_vs_111_ = lean_ctor_get(v_x_106_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_x_106_);
if (v_isSharedCheck_135_ == 0)
{
v___x_113_ = v_x_106_;
v_isShared_114_ = v_isSharedCheck_135_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_vs_111_);
lean_inc(v_ks_110_);
lean_dec(v_x_106_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_135_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = lean_array_get_size(v_ks_110_);
v___x_116_ = lean_nat_dec_lt(v_x_107_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
lean_dec(v_x_107_);
v___x_117_ = lean_array_push(v_ks_110_, v_x_108_);
v___x_118_ = lean_array_push(v_vs_111_, v_x_109_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_118_);
lean_ctor_set(v___x_113_, 0, v___x_117_);
v___x_120_ = v___x_113_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
else
{
lean_object* v_k_x27_122_; uint8_t v___x_123_; 
v_k_x27_122_ = lean_array_fget_borrowed(v_ks_110_, v_x_107_);
v___x_123_ = lean_name_eq(v_x_108_, v_k_x27_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_125_; 
if (v_isShared_114_ == 0)
{
v___x_125_ = v___x_113_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_ks_110_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_vs_111_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_add(v_x_107_, v___x_126_);
lean_dec(v_x_107_);
v_x_106_ = v___x_125_;
v_x_107_ = v___x_127_;
goto _start;
}
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_130_ = lean_array_fset(v_ks_110_, v_x_107_, v_x_108_);
v___x_131_ = lean_array_fset(v_vs_111_, v_x_107_, v_x_109_);
lean_dec(v_x_107_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_131_);
lean_ctor_set(v___x_113_, 0, v___x_130_);
v___x_133_ = v___x_113_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(lean_object* v_n_136_, lean_object* v_k_137_, lean_object* v_v_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_n_136_, v___x_139_, v_k_137_, v_v_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_141_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(lean_object* v_x_142_, size_t v_x_143_, size_t v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v_es_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v_j_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_es_147_ = lean_ctor_get(v_x_142_, 0);
v___x_148_ = ((size_t)31ULL);
v___x_149_ = lean_usize_land(v_x_143_, v___x_148_);
v_j_150_ = lean_usize_to_nat(v___x_149_);
v___x_151_ = lean_array_get_size(v_es_147_);
v___x_152_ = lean_nat_dec_lt(v_j_150_, v___x_151_);
if (v___x_152_ == 0)
{
lean_dec(v_j_150_);
lean_dec(v_x_146_);
lean_dec(v_x_145_);
return v_x_142_;
}
else
{
lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_191_; 
lean_inc_ref(v_es_147_);
v_isSharedCheck_191_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; 
v_unused_192_ = lean_ctor_get(v_x_142_, 0);
lean_dec(v_unused_192_);
v___x_154_ = v_x_142_;
v_isShared_155_ = v_isSharedCheck_191_;
goto v_resetjp_153_;
}
else
{
lean_dec(v_x_142_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_191_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v_v_156_; lean_object* v___x_157_; lean_object* v_xs_x27_158_; lean_object* v___y_160_; 
v_v_156_ = lean_array_fget(v_es_147_, v_j_150_);
v___x_157_ = lean_box(0);
v_xs_x27_158_ = lean_array_fset(v_es_147_, v_j_150_, v___x_157_);
switch(lean_obj_tag(v_v_156_))
{
case 0:
{
lean_object* v_key_165_; lean_object* v_val_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_176_; 
v_key_165_ = lean_ctor_get(v_v_156_, 0);
v_val_166_ = lean_ctor_get(v_v_156_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_v_156_);
if (v_isSharedCheck_176_ == 0)
{
v___x_168_ = v_v_156_;
v_isShared_169_ = v_isSharedCheck_176_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_val_166_);
lean_inc(v_key_165_);
lean_dec(v_v_156_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_176_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
uint8_t v___x_170_; 
v___x_170_ = lean_name_eq(v_x_145_, v_key_165_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_del_object(v___x_168_);
v___x_171_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_165_, v_val_166_, v_x_145_, v_x_146_);
v___x_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
v___y_160_ = v___x_172_;
goto v___jp_159_;
}
else
{
lean_object* v___x_174_; 
lean_dec(v_val_166_);
lean_dec(v_key_165_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v_x_146_);
lean_ctor_set(v___x_168_, 0, v_x_145_);
v___x_174_ = v___x_168_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_x_145_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_x_146_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
v___y_160_ = v___x_174_;
goto v___jp_159_;
}
}
}
}
case 1:
{
lean_object* v_node_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_189_; 
v_node_177_ = lean_ctor_get(v_v_156_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v_v_156_);
if (v_isSharedCheck_189_ == 0)
{
v___x_179_ = v_v_156_;
v_isShared_180_ = v_isSharedCheck_189_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_node_177_);
lean_dec(v_v_156_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_189_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
size_t v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_181_ = ((size_t)5ULL);
v___x_182_ = lean_usize_shift_right(v_x_143_, v___x_181_);
v___x_183_ = ((size_t)1ULL);
v___x_184_ = lean_usize_add(v_x_144_, v___x_183_);
v___x_185_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_node_177_, v___x_182_, v___x_184_, v_x_145_, v_x_146_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_185_);
v___x_187_ = v___x_179_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
v___y_160_ = v___x_187_;
goto v___jp_159_;
}
}
}
default: 
{
lean_object* v___x_190_; 
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_x_145_);
lean_ctor_set(v___x_190_, 1, v_x_146_);
v___y_160_ = v___x_190_;
goto v___jp_159_;
}
}
v___jp_159_:
{
lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_161_ = lean_array_fset(v_xs_x27_158_, v_j_150_, v___y_160_);
lean_dec(v_j_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_161_);
v___x_163_ = v___x_154_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
else
{
lean_object* v_ks_193_; lean_object* v_vs_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_212_; 
v_ks_193_ = lean_ctor_get(v_x_142_, 0);
v_vs_194_ = lean_ctor_get(v_x_142_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_212_ == 0)
{
v___x_196_ = v_x_142_;
v_isShared_197_ = v_isSharedCheck_212_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_vs_194_);
lean_inc(v_ks_193_);
lean_dec(v_x_142_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_212_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_ks_193_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_vs_194_);
v___x_199_ = v_reuseFailAlloc_211_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v_newNode_200_; size_t v___x_201_; uint8_t v___x_202_; 
v_newNode_200_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v___x_199_, v_x_145_, v_x_146_);
v___x_201_ = ((size_t)7ULL);
v___x_202_ = lean_usize_dec_le(v___x_201_, v_x_144_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_203_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_200_);
v___x_204_ = lean_unsigned_to_nat(4u);
v___x_205_ = lean_nat_dec_lt(v___x_203_, v___x_204_);
lean_dec(v___x_203_);
if (v___x_205_ == 0)
{
lean_object* v_ks_206_; lean_object* v_vs_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_ks_206_ = lean_ctor_get(v_newNode_200_, 0);
lean_inc_ref(v_ks_206_);
v_vs_207_ = lean_ctor_get(v_newNode_200_, 1);
lean_inc_ref(v_vs_207_);
lean_dec_ref(v_newNode_200_);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___closed__0);
v___x_210_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_x_144_, v_ks_206_, v_vs_207_, v___x_208_, v___x_209_);
lean_dec_ref(v_vs_207_);
lean_dec_ref(v_ks_206_);
return v___x_210_;
}
else
{
return v_newNode_200_;
}
}
else
{
return v_newNode_200_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_142_ = stack[0].m_obj;
size_t v_x_143_ = stack[1].m_num;
size_t v_x_144_ = stack[2].m_num;
lean_object* v_x_145_ = stack[3].m_obj;
lean_object* v_x_146_ = stack[4].m_obj;
lean_object* v_res_213_;
v_res_213_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_142_, v_x_143_, v_x_144_, v_x_145_, v_x_146_);
stack->m_obj
 = v_res_213_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(size_t v_depth_214_, lean_object* v_keys_215_, lean_object* v_vals_216_, lean_object* v_i_217_, lean_object* v_entries_218_){
_start:
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_array_get_size(v_keys_215_);
v___x_220_ = lean_nat_dec_lt(v_i_217_, v___x_219_);
if (v___x_220_ == 0)
{
lean_dec(v_i_217_);
return v_entries_218_;
}
else
{
lean_object* v_k_221_; lean_object* v_v_222_; uint64_t v___y_224_; 
v_k_221_ = lean_array_fget_borrowed(v_keys_215_, v_i_217_);
v_v_222_ = lean_array_fget_borrowed(v_vals_216_, v_i_217_);
if (lean_obj_tag(v_k_221_) == 0)
{
uint64_t v___x_235_; 
v___x_235_ = 1723ULL;
v___y_224_ = v___x_235_;
goto v___jp_223_;
}
else
{
uint64_t v_hash_236_; 
v_hash_236_ = lean_ctor_get_uint64(v_k_221_, sizeof(void*)*2);
v___y_224_ = v_hash_236_;
goto v___jp_223_;
}
v___jp_223_:
{
size_t v_h_225_; size_t v___x_226_; lean_object* v___x_227_; size_t v___x_228_; size_t v___x_229_; size_t v___x_230_; size_t v_h_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_h_225_ = lean_uint64_to_usize(v___y_224_);
v___x_226_ = ((size_t)5ULL);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_sub(v_depth_214_, v___x_228_);
v___x_230_ = lean_usize_mul(v___x_226_, v___x_229_);
v_h_231_ = lean_usize_shift_right(v_h_225_, v___x_230_);
v___x_232_ = lean_nat_add(v_i_217_, v___x_227_);
lean_dec(v_i_217_);
lean_inc(v_v_222_);
lean_inc(v_k_221_);
v___x_233_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_entries_218_, v_h_231_, v_depth_214_, v_k_221_, v_v_222_);
v_i_217_ = v___x_232_;
v_entries_218_ = v___x_233_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_214_ = stack[0].m_num;
lean_object* v_keys_215_ = stack[1].m_obj;
lean_object* v_vals_216_ = stack[2].m_obj;
lean_object* v_i_217_ = stack[3].m_obj;
lean_object* v_entries_218_ = stack[4].m_obj;
lean_object* v_res_237_;
v_res_237_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_214_, v_keys_215_, v_vals_216_, v_i_217_, v_entries_218_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_238_, lean_object* v_keys_239_, lean_object* v_vals_240_, lean_object* v_i_241_, lean_object* v_entries_242_){
_start:
{
size_t v_depth_boxed_243_; lean_object* v_res_244_; 
v_depth_boxed_243_ = lean_unbox_usize(v_depth_238_);
lean_dec(v_depth_238_);
v_res_244_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_boxed_243_, v_keys_239_, v_vals_240_, v_i_241_, v_entries_242_);
lean_dec_ref(v_vals_240_);
lean_dec_ref(v_keys_239_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
size_t v_x_558__boxed_250_; size_t v_x_559__boxed_251_; lean_object* v_res_252_; 
v_x_558__boxed_250_ = lean_unbox_usize(v_x_246_);
lean_dec(v_x_246_);
v_x_559__boxed_251_ = lean_unbox_usize(v_x_247_);
lean_dec(v_x_247_);
v_res_252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_245_, v_x_558__boxed_250_, v_x_559__boxed_251_, v_x_248_, v_x_249_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(lean_object* v_x_253_, lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
uint64_t v___y_257_; 
if (lean_obj_tag(v_x_254_) == 0)
{
uint64_t v___x_261_; 
v___x_261_ = 1723ULL;
v___y_257_ = v___x_261_;
goto v___jp_256_;
}
else
{
uint64_t v_hash_262_; 
v_hash_262_ = lean_ctor_get_uint64(v_x_254_, sizeof(void*)*2);
v___y_257_ = v_hash_262_;
goto v___jp_256_;
}
v___jp_256_:
{
size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_uint64_to_usize(v___y_257_);
v___x_259_ = ((size_t)1ULL);
v___x_260_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_253_, v___x_258_, v___x_259_, v_x_254_, v_x_255_);
return v___x_260_;
}
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_263_, lean_object* v_i_264_, lean_object* v_k_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_array_get_size(v_keys_263_);
v___x_267_ = lean_nat_dec_lt(v_i_264_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec(v_i_264_);
return v___x_267_;
}
else
{
lean_object* v_k_x27_268_; uint8_t v___x_269_; 
v_k_x27_268_ = lean_array_fget_borrowed(v_keys_263_, v_i_264_);
v___x_269_ = lean_name_eq(v_k_265_, v_k_x27_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_i_264_, v___x_270_);
lean_dec(v_i_264_);
v_i_264_ = v___x_271_;
goto _start;
}
else
{
lean_dec(v_i_264_);
return v___x_267_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_263_ = stack[0].m_obj;
lean_object* v_i_264_ = stack[1].m_obj;
lean_object* v_k_265_ = stack[2].m_obj;
uint8_t v_res_273_;
v_res_273_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_263_, v_i_264_, v_k_265_);
stack->m_num = v_res_273_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_274_, lean_object* v_i_275_, lean_object* v_k_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_274_, v_i_275_, v_k_276_);
lean_dec(v_k_276_);
lean_dec_ref(v_keys_274_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(lean_object* v_x_279_, size_t v_x_280_, lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v_es_282_; lean_object* v___x_283_; size_t v___x_284_; size_t v___x_285_; lean_object* v_j_286_; lean_object* v___x_287_; 
v_es_282_ = lean_ctor_get(v_x_279_, 0);
v___x_283_ = lean_box(2);
v___x_284_ = ((size_t)31ULL);
v___x_285_ = lean_usize_land(v_x_280_, v___x_284_);
v_j_286_ = lean_usize_to_nat(v___x_285_);
v___x_287_ = lean_array_get_borrowed(v___x_283_, v_es_282_, v_j_286_);
lean_dec(v_j_286_);
switch(lean_obj_tag(v___x_287_))
{
case 0:
{
lean_object* v_key_288_; uint8_t v___x_289_; 
v_key_288_ = lean_ctor_get(v___x_287_, 0);
v___x_289_ = lean_name_eq(v_x_281_, v_key_288_);
return v___x_289_;
}
case 1:
{
lean_object* v_node_290_; size_t v___x_291_; size_t v___x_292_; 
v_node_290_ = lean_ctor_get(v___x_287_, 0);
v___x_291_ = ((size_t)5ULL);
v___x_292_ = lean_usize_shift_right(v_x_280_, v___x_291_);
v_x_279_ = v_node_290_;
v_x_280_ = v___x_292_;
goto _start;
}
default: 
{
uint8_t v___x_294_; 
v___x_294_ = 0;
return v___x_294_;
}
}
}
else
{
lean_object* v_ks_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_ks_295_ = lean_ctor_get(v_x_279_, 0);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_ks_295_, v___x_296_, v_x_281_);
return v___x_297_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_279_ = stack[0].m_obj;
size_t v_x_280_ = stack[1].m_num;
lean_object* v_x_281_ = stack[2].m_obj;
uint8_t v_res_298_;
v_res_298_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_279_, v_x_280_, v_x_281_);
stack->m_num = v_res_298_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
size_t v_x_843__boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v_x_843__boxed_302_ = lean_unbox_usize(v_x_300_);
lean_dec(v_x_300_);
v_res_303_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_299_, v_x_843__boxed_302_, v_x_301_);
lean_dec(v_x_301_);
lean_dec_ref(v_x_299_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
uint64_t v___y_308_; 
if (lean_obj_tag(v_x_306_) == 0)
{
uint64_t v___x_311_; 
v___x_311_ = 1723ULL;
v___y_308_ = v___x_311_;
goto v___jp_307_;
}
else
{
uint64_t v_hash_312_; 
v_hash_312_ = lean_ctor_get_uint64(v_x_306_, sizeof(void*)*2);
v___y_308_ = v_hash_312_;
goto v___jp_307_;
}
v___jp_307_:
{
size_t v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_uint64_to_usize(v___y_308_);
v___x_310_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_305_, v___x_309_, v_x_306_);
return v___x_310_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_305_ = stack[0].m_obj;
lean_object* v_x_306_ = stack[1].m_obj;
uint8_t v_res_313_;
v_res_313_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_305_, v_x_306_);
stack->m_num = v_res_313_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg___boxed(lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_314_, v_x_315_);
lean_dec(v_x_315_);
lean_dec_ref(v_x_314_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(lean_object* v_categories_318_, lean_object* v_catName_319_, lean_object* v_initial_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_318_, v_catName_319_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_318_, v_catName_319_, v_initial_320_);
v___x_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; 
lean_dec_ref(v_initial_320_);
lean_dec_ref(v_categories_318_);
v___x_324_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_319_);
return v___x_324_;
}
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(lean_object* v_00_u03b2_325_, lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_x_326_, v_x_327_);
return v___x_328_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_326_ = stack[1].m_obj;
lean_object* v_x_327_ = stack[2].m_obj;
uint8_t v_res_329_;
v_res_329_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(lean_box(0), v_x_326_, v_x_327_);
stack->m_num = v_res_329_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___boxed(lean_object* v_00_u03b2_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0(v_00_u03b2_330_, v_x_331_, v_x_332_);
lean_dec(v_x_332_);
lean_dec_ref(v_x_331_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1(lean_object* v_00_u03b2_335_, lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_x_336_, v_x_337_, v_x_338_);
return v___x_339_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(lean_object* v_00_u03b2_340_, lean_object* v_x_341_, size_t v_x_342_, lean_object* v_x_343_){
_start:
{
uint8_t v___x_344_; 
v___x_344_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___redArg(v_x_341_, v_x_342_, v_x_343_);
return v___x_344_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_341_ = stack[1].m_obj;
size_t v_x_342_ = stack[2].m_num;
lean_object* v_x_343_ = stack[3].m_obj;
uint8_t v_res_345_;
v_res_345_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(lean_box(0), v_x_341_, v_x_342_, v_x_343_);
stack->m_num = v_res_345_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
size_t v_x_967__boxed_350_; uint8_t v_res_351_; lean_object* v_r_352_; 
v_x_967__boxed_350_ = lean_unbox_usize(v_x_348_);
lean_dec(v_x_348_);
v_res_351_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0(v_00_u03b2_346_, v_x_347_, v_x_967__boxed_350_, v_x_349_);
lean_dec(v_x_349_);
lean_dec_ref(v_x_347_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(lean_object* v_00_u03b2_353_, lean_object* v_x_354_, size_t v_x_355_, size_t v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___redArg(v_x_354_, v_x_355_, v_x_356_, v_x_357_, v_x_358_);
return v___x_359_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_354_ = stack[1].m_obj;
size_t v_x_355_ = stack[2].m_num;
size_t v_x_356_ = stack[3].m_num;
lean_object* v_x_357_ = stack[4].m_obj;
lean_object* v_x_358_ = stack[5].m_obj;
lean_object* v_res_360_;
v_res_360_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(lean_box(0), v_x_354_, v_x_355_, v_x_356_, v_x_357_, v_x_358_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_361_, lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
size_t v_x_985__boxed_367_; size_t v_x_986__boxed_368_; lean_object* v_res_369_; 
v_x_985__boxed_367_ = lean_unbox_usize(v_x_363_);
lean_dec(v_x_363_);
v_x_986__boxed_368_ = lean_unbox_usize(v_x_364_);
lean_dec(v_x_364_);
v_res_369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2(v_00_u03b2_361_, v_x_362_, v_x_985__boxed_367_, v_x_986__boxed_368_, v_x_365_, v_x_366_);
return v_res_369_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_370_, lean_object* v_keys_371_, lean_object* v_vals_372_, lean_object* v_heq_373_, lean_object* v_i_374_, lean_object* v_k_375_){
_start:
{
uint8_t v___x_376_; 
v___x_376_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___redArg(v_keys_371_, v_i_374_, v_k_375_);
return v___x_376_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_371_ = stack[1].m_obj;
lean_object* v_vals_372_ = stack[2].m_obj;
lean_object* v_i_374_ = stack[4].m_obj;
lean_object* v_k_375_ = stack[5].m_obj;
uint8_t v_res_377_;
v_res_377_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(lean_box(0), v_keys_371_, v_vals_372_, lean_box(0), v_i_374_, v_k_375_);
stack->m_num = v_res_377_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_378_, lean_object* v_keys_379_, lean_object* v_vals_380_, lean_object* v_heq_381_, lean_object* v_i_382_, lean_object* v_k_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0_spec__0_spec__1(v_00_u03b2_378_, v_keys_379_, v_vals_380_, v_heq_381_, v_i_382_, v_k_383_);
lean_dec(v_k_383_);
lean_dec_ref(v_vals_380_);
lean_dec_ref(v_keys_379_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_386_, lean_object* v_n_387_, lean_object* v_k_388_, lean_object* v_v_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4___redArg(v_n_387_, v_k_388_, v_v_389_);
return v___x_390_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_391_, size_t v_depth_392_, lean_object* v_keys_393_, lean_object* v_vals_394_, lean_object* v_heq_395_, lean_object* v_i_396_, lean_object* v_entries_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___redArg(v_depth_392_, v_keys_393_, v_vals_394_, v_i_396_, v_entries_397_);
return v___x_398_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_392_ = stack[1].m_num;
lean_object* v_keys_393_ = stack[2].m_obj;
lean_object* v_vals_394_ = stack[3].m_obj;
lean_object* v_i_396_ = stack[5].m_obj;
lean_object* v_entries_397_ = stack[6].m_obj;
lean_object* v_res_399_;
v_res_399_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(lean_box(0), v_depth_392_, v_keys_393_, v_vals_394_, lean_box(0), v_i_396_, v_entries_397_);
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_400_, lean_object* v_depth_401_, lean_object* v_keys_402_, lean_object* v_vals_403_, lean_object* v_heq_404_, lean_object* v_i_405_, lean_object* v_entries_406_){
_start:
{
size_t v_depth_boxed_407_; lean_object* v_res_408_; 
v_depth_boxed_407_ = lean_unbox_usize(v_depth_401_);
lean_dec(v_depth_401_);
v_res_408_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__5(v_00_u03b2_400_, v_depth_boxed_407_, v_keys_402_, v_vals_403_, v_heq_404_, v_i_405_, v_entries_406_);
lean_dec_ref(v_vals_403_);
lean_dec_ref(v_keys_402_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_409_, lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1_spec__2_spec__4_spec__5___redArg(v_x_410_, v_x_411_, v_x_412_, v_x_413_);
return v___x_414_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(lean_object* v_e_415_){
_start:
{
if (lean_obj_tag(v_e_415_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_425_; 
v_a_417_ = lean_ctor_get(v_e_415_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_e_415_);
if (v_isSharedCheck_425_ == 0)
{
v___x_419_ = v_e_415_;
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v_e_415_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = lean_mk_io_user_error(v_a_417_);
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 1);
lean_ctor_set(v___x_419_, 0, v___x_421_);
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_a_426_ = lean_ctor_get(v_e_415_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v_e_415_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v_e_415_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v_e_415_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set_tag(v___x_428_, 0);
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_415_ = stack[0].m_obj;
lean_object* v_res_434_;
v_res_434_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_415_);
stack->m_obj
 = v_res_434_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg___boxed(lean_object* v_e_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_435_);
return v_res_437_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(lean_object* v_00_u03b1_438_, lean_object* v_e_439_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v_e_439_);
return v___x_441_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_439_ = stack[1].m_obj;
lean_object* v_res_442_;
v_res_442_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(lean_box(0), v_e_439_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___boxed(lean_object* v_00_u03b1_443_, lean_object* v_e_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0(v_00_u03b1_443_, v_e_444_);
return v_res_446_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(lean_object* v_catName_450_, lean_object* v_declName_451_, uint8_t v_behavior_452_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_454_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_455_ = lean_st_ref_get(v___x_454_);
v___x_456_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_457_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_458_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_458_, 0, v_declName_451_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_457_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*3, v_behavior_452_);
v___x_459_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore(v___x_455_, v_catName_450_, v___x_458_);
v___x_460_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_459_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_470_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_470_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_470_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_470_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_465_ = lean_box(0);
v___x_466_ = lean_st_ref_swap(v___x_454_, v_a_461_);
lean_dec(v___x_466_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_465_);
v___x_468_ = v___x_463_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_465_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_a_471_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_460_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_460_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_0interp(lean_interpreter_value* stack)
{
lean_object* v_catName_450_ = stack[0].m_obj;
lean_object* v_declName_451_ = stack[1].m_obj;
uint8_t v_behavior_452_ = stack[2].m_num;
lean_object* v_res_479_;
v_res_479_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_450_, v_declName_451_, v_behavior_452_);
stack->m_obj
 = v_res_479_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___boxed(lean_object* v_catName_480_, lean_object* v_declName_481_, lean_object* v_behavior_482_, lean_object* v_a_483_){
_start:
{
uint8_t v_behavior_boxed_484_; lean_object* v_res_485_; 
v_behavior_boxed_484_ = lean_unbox(v_behavior_482_);
v_res_485_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_480_, v_declName_481_, v_behavior_boxed_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___impl(lean_object* v_x_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = lean_obj_tag_nat(v_x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___impl___boxed(lean_object* v_x_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorIdx___impl(v_x_488_);
lean_dec_ref(v_x_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(lean_object* v_t_490_, lean_object* v_k_491_){
_start:
{
switch(lean_obj_tag(v_t_490_))
{
case 0:
{
lean_object* v_val_492_; lean_object* v___x_493_; 
v_val_492_ = lean_ctor_get(v_t_490_, 0);
lean_inc_ref(v_val_492_);
lean_dec_ref_known(v_t_490_, 1);
v___x_493_ = lean_apply_1(v_k_491_, v_val_492_);
return v___x_493_;
}
case 1:
{
lean_object* v_val_494_; lean_object* v___x_495_; 
v_val_494_ = lean_ctor_get(v_t_490_, 0);
lean_inc(v_val_494_);
lean_dec_ref_known(v_t_490_, 1);
v___x_495_ = lean_apply_1(v_k_491_, v_val_494_);
return v___x_495_;
}
case 2:
{
lean_object* v_catName_496_; lean_object* v_declName_497_; uint8_t v_behavior_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_catName_496_ = lean_ctor_get(v_t_490_, 0);
lean_inc(v_catName_496_);
v_declName_497_ = lean_ctor_get(v_t_490_, 1);
lean_inc(v_declName_497_);
v_behavior_498_ = lean_ctor_get_uint8(v_t_490_, sizeof(void*)*2);
lean_dec_ref_known(v_t_490_, 2);
v___x_499_ = lean_box(v_behavior_498_);
v___x_500_ = lean_apply_3(v_k_491_, v_catName_496_, v_declName_497_, v___x_499_);
return v___x_500_;
}
default: 
{
lean_object* v_catName_501_; lean_object* v_declName_502_; lean_object* v_prio_503_; lean_object* v___x_504_; 
v_catName_501_ = lean_ctor_get(v_t_490_, 0);
lean_inc(v_catName_501_);
v_declName_502_ = lean_ctor_get(v_t_490_, 1);
lean_inc(v_declName_502_);
v_prio_503_ = lean_ctor_get(v_t_490_, 2);
lean_inc(v_prio_503_);
lean_dec_ref_known(v_t_490_, 3);
v___x_504_ = lean_apply_3(v_k_491_, v_catName_501_, v_declName_502_, v_prio_503_);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(lean_object* v_motive_505_, lean_object* v_ctorIdx_506_, lean_object* v_t_507_, lean_object* v_h_508_, lean_object* v_k_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_507_, v_k_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___boxed(lean_object* v_motive_511_, lean_object* v_ctorIdx_512_, lean_object* v_t_513_, lean_object* v_h_514_, lean_object* v_k_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim(v_motive_511_, v_ctorIdx_512_, v_t_513_, v_h_514_, v_k_515_);
lean_dec(v_ctorIdx_512_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim___redArg(lean_object* v_t_517_, lean_object* v_token_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_517_, v_token_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_token_elim(lean_object* v_motive_520_, lean_object* v_t_521_, lean_object* v_h_522_, lean_object* v_token_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_521_, v_token_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim___redArg(lean_object* v_t_525_, lean_object* v_kind_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_525_, v_kind_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_kind_elim(lean_object* v_motive_528_, lean_object* v_t_529_, lean_object* v_h_530_, lean_object* v_kind_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_529_, v_kind_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim___redArg(lean_object* v_t_533_, lean_object* v_category_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_533_, v_category_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_category_elim(lean_object* v_motive_536_, lean_object* v_t_537_, lean_object* v_h_538_, lean_object* v_category_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_537_, v_category_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim___redArg(lean_object* v_t_541_, lean_object* v_parser_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_541_, v_parser_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_OLeanEntry_parser_elim(lean_object* v_motive_544_, lean_object* v_t_545_, lean_object* v_h_546_, lean_object* v_parser_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_Parser_ParserExtension_OLeanEntry_ctorElim___redArg(v_t_545_, v_parser_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___impl(lean_object* v_x_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_tag_nat(v_x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorIdx___impl___boxed(lean_object* v_x_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Parser_ParserExtension_Entry_ctorIdx___impl(v_x_556_);
lean_dec_ref(v_x_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(lean_object* v_t_558_, lean_object* v_k_559_){
_start:
{
switch(lean_obj_tag(v_t_558_))
{
case 0:
{
lean_object* v_val_560_; lean_object* v___x_561_; 
v_val_560_ = lean_ctor_get(v_t_558_, 0);
lean_inc_ref(v_val_560_);
lean_dec_ref_known(v_t_558_, 1);
v___x_561_ = lean_apply_1(v_k_559_, v_val_560_);
return v___x_561_;
}
case 1:
{
lean_object* v_val_562_; lean_object* v___x_563_; 
v_val_562_ = lean_ctor_get(v_t_558_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v_t_558_, 1);
v___x_563_ = lean_apply_1(v_k_559_, v_val_562_);
return v___x_563_;
}
case 2:
{
lean_object* v_catName_564_; lean_object* v_declName_565_; uint8_t v_behavior_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_catName_564_ = lean_ctor_get(v_t_558_, 0);
lean_inc(v_catName_564_);
v_declName_565_ = lean_ctor_get(v_t_558_, 1);
lean_inc(v_declName_565_);
v_behavior_566_ = lean_ctor_get_uint8(v_t_558_, sizeof(void*)*2);
lean_dec_ref_known(v_t_558_, 2);
v___x_567_ = lean_box(v_behavior_566_);
v___x_568_ = lean_apply_3(v_k_559_, v_catName_564_, v_declName_565_, v___x_567_);
return v___x_568_;
}
default: 
{
lean_object* v_catName_569_; lean_object* v_declName_570_; uint8_t v_leading_571_; lean_object* v_p_572_; lean_object* v_prio_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_catName_569_ = lean_ctor_get(v_t_558_, 0);
lean_inc(v_catName_569_);
v_declName_570_ = lean_ctor_get(v_t_558_, 1);
lean_inc(v_declName_570_);
v_leading_571_ = lean_ctor_get_uint8(v_t_558_, sizeof(void*)*4);
v_p_572_ = lean_ctor_get(v_t_558_, 2);
lean_inc_ref(v_p_572_);
v_prio_573_ = lean_ctor_get(v_t_558_, 3);
lean_inc(v_prio_573_);
lean_dec_ref_known(v_t_558_, 4);
v___x_574_ = lean_box(v_leading_571_);
v___x_575_ = lean_apply_5(v_k_559_, v_catName_569_, v_declName_570_, v___x_574_, v_p_572_, v_prio_573_);
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim(lean_object* v_motive_576_, lean_object* v_ctorIdx_577_, lean_object* v_t_578_, lean_object* v_h_579_, lean_object* v_k_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_578_, v_k_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_ctorElim___boxed(lean_object* v_motive_582_, lean_object* v_ctorIdx_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_k_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Parser_ParserExtension_Entry_ctorElim(v_motive_582_, v_ctorIdx_583_, v_t_584_, v_h_585_, v_k_586_);
lean_dec(v_ctorIdx_583_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim___redArg(lean_object* v_t_588_, lean_object* v_token_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_588_, v_token_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_token_elim(lean_object* v_motive_591_, lean_object* v_t_592_, lean_object* v_h_593_, lean_object* v_token_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_592_, v_token_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim___redArg(lean_object* v_t_596_, lean_object* v_kind_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_596_, v_kind_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_kind_elim(lean_object* v_motive_599_, lean_object* v_t_600_, lean_object* v_h_601_, lean_object* v_kind_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_600_, v_kind_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim___redArg(lean_object* v_t_604_, lean_object* v_category_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_604_, v_category_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_category_elim(lean_object* v_motive_607_, lean_object* v_t_608_, lean_object* v_h_609_, lean_object* v_category_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_608_, v_category_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim___redArg(lean_object* v_t_612_, lean_object* v_parser_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_612_, v_parser_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_parser_elim(lean_object* v_motive_615_, lean_object* v_t_616_, lean_object* v_h_617_, lean_object* v_parser_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Parser_ParserExtension_Entry_ctorElim___redArg(v_t_616_, v_parser_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_Entry_toOLeanEntry(lean_object* v_x_624_){
_start:
{
switch(lean_obj_tag(v_x_624_))
{
case 0:
{
lean_object* v_val_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_val_625_ = lean_ctor_get(v_x_624_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v_x_624_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v_x_624_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_val_625_);
lean_dec(v_x_624_);
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
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_val_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
case 1:
{
lean_object* v_val_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_val_633_ = lean_ctor_get(v_x_624_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_624_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v_x_624_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_val_633_);
lean_dec(v_x_624_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_val_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
case 2:
{
lean_object* v_catName_641_; lean_object* v_declName_642_; uint8_t v_behavior_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
v_catName_641_ = lean_ctor_get(v_x_624_, 0);
v_declName_642_ = lean_ctor_get(v_x_624_, 1);
v_behavior_643_ = lean_ctor_get_uint8(v_x_624_, sizeof(void*)*2);
v_isSharedCheck_650_ = !lean_is_exclusive(v_x_624_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v_x_624_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_declName_642_);
lean_inc(v_catName_641_);
lean_dec(v_x_624_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_catName_641_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_declName_642_);
lean_ctor_set_uint8(v_reuseFailAlloc_649_, sizeof(void*)*2, v_behavior_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
default: 
{
lean_object* v_catName_651_; lean_object* v_declName_652_; lean_object* v_prio_653_; lean_object* v___x_654_; 
v_catName_651_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_catName_651_);
v_declName_652_ = lean_ctor_get(v_x_624_, 1);
lean_inc(v_declName_652_);
v_prio_653_ = lean_ctor_get(v_x_624_, 3);
lean_inc(v_prio_653_);
lean_dec_ref_known(v_x_624_, 4);
v___x_654_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_654_, 0, v_catName_651_);
lean_ctor_set(v___x_654_, 1, v_declName_652_);
lean_ctor_set(v___x_654_, 2, v_prio_653_);
return v___x_654_;
}
}
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_656_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
lean_ctor_set(v___x_657_, 2, v___x_655_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState_default(void){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = lean_obj_once(&l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0, &l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0_once, _init_l_Lean_Parser_ParserExtension_instInhabitedState_default___closed__0);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_Parser_ParserExtension_instInhabitedState(void){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
return v___x_659_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial(){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_661_ = l_Lean_Parser_builtinTokenTable;
v___x_662_ = lean_st_ref_get(v___x_661_);
v___x_663_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_664_ = lean_st_ref_get(v___x_663_);
v___x_665_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_666_ = lean_st_ref_get(v___x_665_);
v___x_667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_667_, 0, v___x_662_);
lean_ctor_set(v___x_667_, 1, v___x_664_);
lean_ctor_set(v___x_667_, 2, v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_669_;
v_res_669_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
stack->m_obj
 = v_res_669_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed(lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial();
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(lean_object* v_tokens_675_, lean_object* v_tk_676_){
_start:
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = ((lean_object*)(l_Lean_Parser_ParserExtension_instInhabitedOLeanEntry_default___closed__0));
v___x_678_ = lean_string_dec_eq(v_tk_676_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Data_Trie_find_x3f___redArg(v_tokens_675_, v_tk_676_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
lean_inc_ref(v_tk_676_);
v___x_680_ = l_Lean_Data_Trie_insert___redArg(v_tokens_675_, v_tk_676_, v_tk_676_);
lean_dec_ref(v_tk_676_);
v___x_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
else
{
lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v_tk_676_);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v___x_679_, 0);
lean_dec(v_unused_689_);
v___x_683_ = v___x_679_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_dec(v___x_679_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v_tokens_675_);
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_tokens_675_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v___x_690_; 
lean_dec_ref(v_tk_676_);
lean_dec_ref(v_tokens_675_);
v___x_690_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig___closed__1));
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory___redArg(lean_object* v_catName_693_){
_start:
{
lean_object* v___x_694_; uint8_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_694_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__0));
v___x_695_ = 1;
v___x_696_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_catName_693_, v___x_695_);
v___x_697_ = lean_string_append(v___x_694_, v___x_696_);
lean_dec_ref(v___x_696_);
v___x_698_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_699_ = lean_string_append(v___x_697_, v___x_698_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_throwUnknownParserCategory(lean_object* v_00_u03b1_701_, lean_object* v_catName_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory(lean_object* v_categories_706_, lean_object* v_catName_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__0));
v___x_709_ = ((lean_object*)(l_Lean_Parser_getCategory___closed__1));
v___x_710_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_708_, v___x_709_, v_categories_706_, v_catName_707_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getCategory___boxed(lean_object* v_categories_711_, lean_object* v_catName_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Parser_getCategory(v_categories_711_, v_catName_712_);
lean_dec_ref(v_categories_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(lean_object* v_as_715_){
_start:
{
lean_object* v___f_716_; lean_object* v___x_717_; 
v___f_716_ = ((lean_object*)(l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2___closed__0));
v___x_717_ = l_List_eraseDupsBy___redArg(v___f_716_, v_as_715_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(lean_object* v_p_718_, lean_object* v_prio_719_, lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
if (lean_obj_tag(v_x_721_) == 0)
{
lean_dec(v_prio_719_);
lean_dec_ref(v_p_718_);
return v_x_720_;
}
else
{
lean_object* v_head_722_; lean_object* v_tail_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_743_; 
v_head_722_ = lean_ctor_get(v_x_721_, 0);
v_tail_723_ = lean_ctor_get(v_x_721_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_x_721_);
if (v_isSharedCheck_743_ == 0)
{
v___x_725_ = v_x_721_;
v_isShared_726_ = v_isSharedCheck_743_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_tail_723_);
lean_inc(v_head_722_);
lean_dec(v_x_721_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_743_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v_leadingTable_727_; lean_object* v_leadingParsers_728_; lean_object* v_trailingTable_729_; lean_object* v_trailingParsers_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_742_; 
v_leadingTable_727_ = lean_ctor_get(v_x_720_, 0);
v_leadingParsers_728_ = lean_ctor_get(v_x_720_, 1);
v_trailingTable_729_ = lean_ctor_get(v_x_720_, 2);
v_trailingParsers_730_ = lean_ctor_get(v_x_720_, 3);
v_isSharedCheck_742_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_742_ == 0)
{
v___x_732_ = v_x_720_;
v_isShared_733_ = v_isSharedCheck_742_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_trailingParsers_730_);
lean_inc(v_trailingTable_729_);
lean_inc(v_leadingParsers_728_);
lean_inc(v_leadingTable_727_);
lean_dec(v_x_720_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_742_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
lean_inc(v_prio_719_);
lean_inc_ref(v_p_718_);
if (v_isShared_726_ == 0)
{
lean_ctor_set_tag(v___x_725_, 0);
lean_ctor_set(v___x_725_, 1, v_prio_719_);
lean_ctor_set(v___x_725_, 0, v_p_718_);
v___x_735_ = v___x_725_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_p_718_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_prio_719_);
v___x_735_ = v_reuseFailAlloc_741_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_736_ = l_Lean_Parser_TokenMap_insert___redArg(v_leadingTable_727_, v_head_722_, v___x_735_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_736_);
v___x_738_ = v___x_732_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_leadingParsers_728_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_trailingTable_729_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_trailingParsers_730_);
v___x_738_ = v_reuseFailAlloc_740_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
v_x_720_ = v___x_738_;
v_x_721_ = v_tail_723_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_744_, lean_object* v_vals_745_, lean_object* v_i_746_, lean_object* v_k_747_){
_start:
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_array_get_size(v_keys_744_);
v___x_749_ = lean_nat_dec_lt(v_i_746_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
lean_dec(v_i_746_);
v___x_750_ = lean_box(0);
return v___x_750_;
}
else
{
lean_object* v_k_x27_751_; uint8_t v___x_752_; 
v_k_x27_751_ = lean_array_fget_borrowed(v_keys_744_, v_i_746_);
v___x_752_ = lean_name_eq(v_k_747_, v_k_x27_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_add(v_i_746_, v___x_753_);
lean_dec(v_i_746_);
v_i_746_ = v___x_754_;
goto _start;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_array_fget_borrowed(v_vals_745_, v_i_746_);
lean_dec(v_i_746_);
lean_inc(v___x_756_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_758_, lean_object* v_vals_759_, lean_object* v_i_760_, lean_object* v_k_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_758_, v_vals_759_, v_i_760_, v_k_761_);
lean_dec(v_k_761_);
lean_dec_ref(v_vals_759_);
lean_dec_ref(v_keys_758_);
return v_res_762_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(lean_object* v_x_763_, size_t v_x_764_, lean_object* v_x_765_){
_start:
{
if (lean_obj_tag(v_x_763_) == 0)
{
lean_object* v_es_766_; lean_object* v___x_767_; size_t v___x_768_; size_t v___x_769_; lean_object* v_j_770_; lean_object* v___x_771_; 
v_es_766_ = lean_ctor_get(v_x_763_, 0);
v___x_767_ = lean_box(2);
v___x_768_ = ((size_t)31ULL);
v___x_769_ = lean_usize_land(v_x_764_, v___x_768_);
v_j_770_ = lean_usize_to_nat(v___x_769_);
v___x_771_ = lean_array_get_borrowed(v___x_767_, v_es_766_, v_j_770_);
lean_dec(v_j_770_);
switch(lean_obj_tag(v___x_771_))
{
case 0:
{
lean_object* v_key_772_; lean_object* v_val_773_; uint8_t v___x_774_; 
v_key_772_ = lean_ctor_get(v___x_771_, 0);
v_val_773_ = lean_ctor_get(v___x_771_, 1);
v___x_774_ = lean_name_eq(v_x_765_, v_key_772_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
v___x_775_ = lean_box(0);
return v___x_775_;
}
else
{
lean_object* v___x_776_; 
lean_inc(v_val_773_);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v_val_773_);
return v___x_776_;
}
}
case 1:
{
lean_object* v_node_777_; size_t v___x_778_; size_t v___x_779_; 
v_node_777_ = lean_ctor_get(v___x_771_, 0);
v___x_778_ = ((size_t)5ULL);
v___x_779_ = lean_usize_shift_right(v_x_764_, v___x_778_);
v_x_763_ = v_node_777_;
v_x_764_ = v___x_779_;
goto _start;
}
default: 
{
lean_object* v___x_781_; 
v___x_781_ = lean_box(0);
return v___x_781_;
}
}
}
else
{
lean_object* v_ks_782_; lean_object* v_vs_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_ks_782_ = lean_ctor_get(v_x_763_, 0);
v_vs_783_ = lean_ctor_get(v_x_763_, 1);
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_ks_782_, v_vs_783_, v___x_784_, v_x_765_);
return v___x_785_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_763_ = stack[0].m_obj;
size_t v_x_764_ = stack[1].m_num;
lean_object* v_x_765_ = stack[2].m_obj;
lean_object* v_res_786_;
v_res_786_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_763_, v_x_764_, v_x_765_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg___boxed(lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
size_t v_x_528__boxed_790_; lean_object* v_res_791_; 
v_x_528__boxed_790_ = lean_unbox_usize(v_x_788_);
lean_dec(v_x_788_);
v_res_791_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_787_, v_x_528__boxed_790_, v_x_789_);
lean_dec(v_x_789_);
lean_dec_ref(v_x_787_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
uint64_t v___y_795_; 
if (lean_obj_tag(v_x_793_) == 0)
{
uint64_t v___x_798_; 
v___x_798_ = 1723ULL;
v___y_795_ = v___x_798_;
goto v___jp_794_;
}
else
{
uint64_t v_hash_799_; 
v_hash_799_ = lean_ctor_get_uint64(v_x_793_, sizeof(void*)*2);
v___y_795_ = v_hash_799_;
goto v___jp_794_;
}
v___jp_794_:
{
size_t v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_uint64_to_usize(v___y_795_);
v___x_797_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_792_, v___x_796_, v_x_793_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg___boxed(lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_800_, v_x_801_);
lean_dec(v_x_801_);
lean_dec_ref(v_x_800_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
if (lean_obj_tag(v_a_803_) == 0)
{
lean_object* v___x_805_; 
v___x_805_ = l_List_reverse___redArg(v_a_804_);
return v___x_805_;
}
else
{
lean_object* v_head_806_; lean_object* v_tail_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_817_; 
v_head_806_ = lean_ctor_get(v_a_803_, 0);
v_tail_807_ = lean_ctor_get(v_a_803_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_a_803_);
if (v_isSharedCheck_817_ == 0)
{
v___x_809_ = v_a_803_;
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_tail_807_);
lean_inc(v_head_806_);
lean_dec(v_a_803_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_811_ = lean_box(0);
v___x_812_ = l_Lean_Name_str___override(v___x_811_, v_head_806_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 1, v_a_804_);
lean_ctor_set(v___x_809_, 0, v___x_812_);
v___x_814_ = v___x_809_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_a_804_);
v___x_814_ = v_reuseFailAlloc_816_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
v_a_803_ = v_tail_807_;
v_a_804_ = v___x_814_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addLeadingParser(lean_object* v_categories_818_, lean_object* v_catName_819_, lean_object* v_declName_820_, lean_object* v_p_821_, lean_object* v_prio_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_818_, v_catName_819_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; 
lean_dec(v_prio_822_);
lean_dec_ref(v_p_821_);
lean_dec(v_declName_820_);
lean_dec_ref(v_categories_818_);
v___x_824_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_819_);
return v___x_824_;
}
else
{
lean_object* v_val_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_871_; 
v_val_825_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_871_ == 0)
{
v___x_827_ = v___x_823_;
v_isShared_828_ = v_isSharedCheck_871_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_val_825_);
lean_dec(v___x_823_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_871_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_info_829_; lean_object* v_declName_830_; lean_object* v_kinds_831_; lean_object* v_tables_832_; uint8_t v_behavior_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_870_; 
v_info_829_ = lean_ctor_get(v_p_821_, 0);
v_declName_830_ = lean_ctor_get(v_val_825_, 0);
v_kinds_831_ = lean_ctor_get(v_val_825_, 1);
v_tables_832_ = lean_ctor_get(v_val_825_, 2);
v_behavior_833_ = lean_ctor_get_uint8(v_val_825_, sizeof(void*)*3);
v_isSharedCheck_870_ = !lean_is_exclusive(v_val_825_);
if (v_isSharedCheck_870_ == 0)
{
v___x_835_ = v_val_825_;
v_isShared_836_ = v_isSharedCheck_870_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_tables_832_);
lean_inc(v_kinds_831_);
lean_inc(v_declName_830_);
lean_dec(v_val_825_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_870_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_firstTokens_837_; lean_object* v_kinds_838_; lean_object* v_tks_840_; 
v_firstTokens_837_ = lean_ctor_get(v_info_829_, 2);
v_kinds_838_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_831_, v_declName_820_);
switch(lean_obj_tag(v_firstTokens_837_))
{
case 2:
{
lean_object* v_a_852_; 
v_a_852_ = lean_ctor_get(v_firstTokens_837_, 0);
lean_inc(v_a_852_);
v_tks_840_ = v_a_852_;
goto v___jp_839_;
}
case 3:
{
lean_object* v_a_853_; 
v_a_853_ = lean_ctor_get(v_firstTokens_837_, 0);
lean_inc(v_a_853_);
v_tks_840_ = v_a_853_;
goto v___jp_839_;
}
default: 
{
lean_object* v_leadingTable_854_; lean_object* v_leadingParsers_855_; lean_object* v_trailingTable_856_; lean_object* v_trailingParsers_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_869_; 
lean_del_object(v___x_835_);
lean_del_object(v___x_827_);
v_leadingTable_854_ = lean_ctor_get(v_tables_832_, 0);
v_leadingParsers_855_ = lean_ctor_get(v_tables_832_, 1);
v_trailingTable_856_ = lean_ctor_get(v_tables_832_, 2);
v_trailingParsers_857_ = lean_ctor_get(v_tables_832_, 3);
v_isSharedCheck_869_ = !lean_is_exclusive(v_tables_832_);
if (v_isSharedCheck_869_ == 0)
{
v___x_859_ = v_tables_832_;
v_isShared_860_ = v_isSharedCheck_869_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_trailingParsers_857_);
lean_inc(v_trailingTable_856_);
lean_inc(v_leadingParsers_855_);
lean_inc(v_leadingTable_854_);
lean_dec(v_tables_832_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_869_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_tables_864_; 
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_p_821_);
lean_ctor_set(v___x_861_, 1, v_prio_822_);
v___x_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v_leadingParsers_855_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v___x_862_);
v_tables_864_ = v___x_859_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_leadingTable_854_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_trailingTable_856_);
lean_ctor_set(v_reuseFailAlloc_868_, 3, v_trailingParsers_857_);
v_tables_864_ = v_reuseFailAlloc_868_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_865_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_865_, 0, v_declName_830_);
lean_ctor_set(v___x_865_, 1, v_kinds_838_);
lean_ctor_set(v___x_865_, 2, v_tables_864_);
lean_ctor_set_uint8(v___x_865_, sizeof(void*)*3, v_behavior_833_);
v___x_866_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_818_, v_catName_819_, v___x_865_);
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
}
}
}
v___jp_839_:
{
lean_object* v___x_841_; lean_object* v_tks_842_; lean_object* v___x_843_; lean_object* v_tables_844_; lean_object* v___x_846_; 
v___x_841_ = lean_box(0);
v_tks_842_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_840_, v___x_841_);
v___x_843_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_842_);
v_tables_844_ = l_List_foldl___at___00Lean_Parser_addLeadingParser_spec__3(v_p_821_, v_prio_822_, v_tables_832_, v___x_843_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 2, v_tables_844_);
lean_ctor_set(v___x_835_, 1, v_kinds_838_);
v___x_846_ = v___x_835_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_declName_830_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_kinds_838_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_tables_844_);
lean_ctor_set_uint8(v_reuseFailAlloc_851_, sizeof(void*)*3, v_behavior_833_);
v___x_846_ = v_reuseFailAlloc_851_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_847_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_818_, v_catName_819_, v___x_846_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_847_);
v___x_849_ = v___x_827_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_x_873_, v_x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___boxed(lean_object* v_00_u03b2_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0(v_00_u03b2_876_, v_x_877_, v_x_878_);
lean_dec(v_x_878_);
lean_dec_ref(v_x_877_);
return v_res_879_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_object* v_00_u03b2_880_, lean_object* v_x_881_, size_t v_x_882_, lean_object* v_x_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___redArg(v_x_881_, v_x_882_, v_x_883_);
return v___x_884_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_881_ = stack[1].m_obj;
size_t v_x_882_ = stack[2].m_num;
lean_object* v_x_883_ = stack[3].m_obj;
lean_object* v_res_885_;
v_res_885_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(lean_box(0), v_x_881_, v_x_882_, v_x_883_);
stack->m_obj
 = v_res_885_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0___boxed(lean_object* v_00_u03b2_886_, lean_object* v_x_887_, lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
size_t v_x_785__boxed_890_; lean_object* v_res_891_; 
v_x_785__boxed_890_ = lean_unbox_usize(v_x_888_);
lean_dec(v_x_888_);
v_res_891_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0(v_00_u03b2_886_, v_x_887_, v_x_785__boxed_890_, v_x_889_);
lean_dec(v_x_889_);
lean_dec_ref(v_x_887_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_892_, lean_object* v_keys_893_, lean_object* v_vals_894_, lean_object* v_heq_895_, lean_object* v_i_896_, lean_object* v_k_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___redArg(v_keys_893_, v_vals_894_, v_i_896_, v_k_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_899_, lean_object* v_keys_900_, lean_object* v_vals_901_, lean_object* v_heq_902_, lean_object* v_i_903_, lean_object* v_k_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0_spec__0_spec__2(v_00_u03b2_899_, v_keys_900_, v_vals_901_, v_heq_902_, v_i_903_, v_k_904_);
lean_dec(v_k_904_);
lean_dec_ref(v_vals_901_);
lean_dec_ref(v_keys_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(lean_object* v_p_906_, lean_object* v_prio_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
if (lean_obj_tag(v_x_909_) == 0)
{
lean_dec(v_prio_907_);
lean_dec_ref(v_p_906_);
return v_x_908_;
}
else
{
lean_object* v_head_910_; lean_object* v_tail_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_931_; 
v_head_910_ = lean_ctor_get(v_x_909_, 0);
v_tail_911_ = lean_ctor_get(v_x_909_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v_x_909_);
if (v_isSharedCheck_931_ == 0)
{
v___x_913_ = v_x_909_;
v_isShared_914_ = v_isSharedCheck_931_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_tail_911_);
lean_inc(v_head_910_);
lean_dec(v_x_909_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_931_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_leadingTable_915_; lean_object* v_leadingParsers_916_; lean_object* v_trailingTable_917_; lean_object* v_trailingParsers_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_930_; 
v_leadingTable_915_ = lean_ctor_get(v_x_908_, 0);
v_leadingParsers_916_ = lean_ctor_get(v_x_908_, 1);
v_trailingTable_917_ = lean_ctor_get(v_x_908_, 2);
v_trailingParsers_918_ = lean_ctor_get(v_x_908_, 3);
v_isSharedCheck_930_ = !lean_is_exclusive(v_x_908_);
if (v_isSharedCheck_930_ == 0)
{
v___x_920_ = v_x_908_;
v_isShared_921_ = v_isSharedCheck_930_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_trailingParsers_918_);
lean_inc(v_trailingTable_917_);
lean_inc(v_leadingParsers_916_);
lean_inc(v_leadingTable_915_);
lean_dec(v_x_908_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_930_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
lean_inc(v_prio_907_);
lean_inc_ref(v_p_906_);
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 0);
lean_ctor_set(v___x_913_, 1, v_prio_907_);
lean_ctor_set(v___x_913_, 0, v_p_906_);
v___x_923_ = v___x_913_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_p_906_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_prio_907_);
v___x_923_ = v_reuseFailAlloc_929_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = l_Lean_Parser_TokenMap_insert___redArg(v_trailingTable_917_, v_head_910_, v___x_923_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 2, v___x_924_);
v___x_926_ = v___x_920_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_leadingTable_915_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_leadingParsers_916_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_928_, 3, v_trailingParsers_918_);
v___x_926_ = v_reuseFailAlloc_928_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
v_x_908_ = v___x_926_;
v_x_909_ = v_tail_911_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(lean_object* v_tables_932_, lean_object* v_p_933_, lean_object* v_prio_934_){
_start:
{
lean_object* v_tks_936_; lean_object* v_info_941_; lean_object* v_firstTokens_942_; 
v_info_941_ = lean_ctor_get(v_p_933_, 0);
v_firstTokens_942_ = lean_ctor_get(v_info_941_, 2);
switch(lean_obj_tag(v_firstTokens_942_))
{
case 2:
{
lean_object* v_a_943_; 
v_a_943_ = lean_ctor_get(v_firstTokens_942_, 0);
lean_inc(v_a_943_);
v_tks_936_ = v_a_943_;
goto v___jp_935_;
}
case 3:
{
lean_object* v_a_944_; 
v_a_944_ = lean_ctor_get(v_firstTokens_942_, 0);
lean_inc(v_a_944_);
v_tks_936_ = v_a_944_;
goto v___jp_935_;
}
default: 
{
lean_object* v_leadingTable_945_; lean_object* v_leadingParsers_946_; lean_object* v_trailingTable_947_; lean_object* v_trailingParsers_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_957_; 
v_leadingTable_945_ = lean_ctor_get(v_tables_932_, 0);
v_leadingParsers_946_ = lean_ctor_get(v_tables_932_, 1);
v_trailingTable_947_ = lean_ctor_get(v_tables_932_, 2);
v_trailingParsers_948_ = lean_ctor_get(v_tables_932_, 3);
v_isSharedCheck_957_ = !lean_is_exclusive(v_tables_932_);
if (v_isSharedCheck_957_ == 0)
{
v___x_950_ = v_tables_932_;
v_isShared_951_ = v_isSharedCheck_957_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_trailingParsers_948_);
lean_inc(v_trailingTable_947_);
lean_inc(v_leadingParsers_946_);
lean_inc(v_leadingTable_945_);
lean_dec(v_tables_932_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_957_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_p_933_);
lean_ctor_set(v___x_952_, 1, v_prio_934_);
v___x_953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set(v___x_953_, 1, v_trailingParsers_948_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 3, v___x_953_);
v___x_955_ = v___x_950_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_leadingTable_945_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_leadingParsers_946_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_trailingTable_947_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v___x_953_);
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
v___jp_935_:
{
lean_object* v___x_937_; lean_object* v_tks_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_937_ = lean_box(0);
v_tks_938_ = l_List_mapTR_loop___at___00Lean_Parser_addLeadingParser_spec__1(v_tks_936_, v___x_937_);
v___x_939_ = l_List_eraseDups___at___00Lean_Parser_addLeadingParser_spec__2(v_tks_938_);
v___x_940_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux_spec__0(v_p_933_, v_prio_934_, v_tables_932_, v___x_939_);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addTrailingParser(lean_object* v_categories_958_, lean_object* v_catName_959_, lean_object* v_declName_960_, lean_object* v_p_961_, lean_object* v_prio_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_958_, v_catName_959_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v___x_964_; 
lean_dec(v_prio_962_);
lean_dec_ref(v_p_961_);
lean_dec(v_declName_960_);
lean_dec_ref(v_categories_958_);
v___x_964_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_959_);
return v___x_964_;
}
else
{
lean_object* v_val_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_986_; 
v_val_965_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_986_ == 0)
{
v___x_967_ = v___x_963_;
v_isShared_968_ = v_isSharedCheck_986_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_val_965_);
lean_dec(v___x_963_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_986_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_declName_969_; lean_object* v_kinds_970_; lean_object* v_tables_971_; uint8_t v_behavior_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_985_; 
v_declName_969_ = lean_ctor_get(v_val_965_, 0);
v_kinds_970_ = lean_ctor_get(v_val_965_, 1);
v_tables_971_ = lean_ctor_get(v_val_965_, 2);
v_behavior_972_ = lean_ctor_get_uint8(v_val_965_, sizeof(void*)*3);
v_isSharedCheck_985_ = !lean_is_exclusive(v_val_965_);
if (v_isSharedCheck_985_ == 0)
{
v___x_974_ = v_val_965_;
v_isShared_975_ = v_isSharedCheck_985_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_tables_971_);
lean_inc(v_kinds_970_);
lean_inc(v_declName_969_);
lean_dec(v_val_965_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_985_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_kinds_976_; lean_object* v_tables_977_; lean_object* v___x_979_; 
v_kinds_976_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_970_, v_declName_960_);
v_tables_977_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTrailingParserAux(v_tables_971_, v_p_961_, v_prio_962_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 2, v_tables_977_);
lean_ctor_set(v___x_974_, 1, v_kinds_976_);
v___x_979_ = v___x_974_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_declName_969_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_kinds_976_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_tables_977_);
lean_ctor_set_uint8(v_reuseFailAlloc_984_, sizeof(void*)*3, v_behavior_972_);
v___x_979_ = v_reuseFailAlloc_984_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_958_, v_catName_959_, v___x_979_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_980_);
v___x_982_ = v___x_967_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
}
}
lean_object* l_Lean_Parser_addParser(lean_object* v_categories_987_, lean_object* v_catName_988_, lean_object* v_declName_989_, uint8_t v_leading_990_, lean_object* v_p_991_, lean_object* v_prio_992_){
_start:
{
if (v_leading_990_ == 0)
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Parser_addTrailingParser(v_categories_987_, v_catName_988_, v_declName_989_, v_p_991_, v_prio_992_);
return v___x_993_;
}
else
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_Parser_addLeadingParser(v_categories_987_, v_catName_988_, v_declName_989_, v_p_991_, v_prio_992_);
return v___x_994_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_addParser_0interp(lean_interpreter_value* stack)
{
lean_object* v_categories_987_ = stack[0].m_obj;
lean_object* v_catName_988_ = stack[1].m_obj;
lean_object* v_declName_989_ = stack[2].m_obj;
uint8_t v_leading_990_ = stack[3].m_num;
lean_object* v_p_991_ = stack[4].m_obj;
lean_object* v_prio_992_ = stack[5].m_obj;
lean_object* v_res_995_;
v_res_995_ = l_Lean_Parser_addParser(v_categories_987_, v_catName_988_, v_declName_989_, v_leading_990_, v_p_991_, v_prio_992_);
stack->m_obj
 = v_res_995_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParser___boxed(lean_object* v_categories_996_, lean_object* v_catName_997_, lean_object* v_declName_998_, lean_object* v_leading_999_, lean_object* v_p_1000_, lean_object* v_prio_1001_){
_start:
{
uint8_t v_leading_boxed_1002_; lean_object* v_res_1003_; 
v_leading_boxed_1002_ = lean_unbox(v_leading_999_);
v_res_1003_ = l_Lean_Parser_addParser(v_categories_996_, v_catName_997_, v_declName_998_, v_leading_boxed_1002_, v_p_1000_, v_prio_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v_x_1004_);
return v___x_1006_;
}
else
{
lean_object* v_head_1007_; lean_object* v_tail_1008_; lean_object* v___x_1009_; 
v_head_1007_ = lean_ctor_get(v_x_1005_, 0);
lean_inc(v_head_1007_);
v_tail_1008_ = lean_ctor_get(v_x_1005_, 1);
lean_inc(v_tail_1008_);
lean_dec_ref_known(v_x_1005_, 2);
v___x_1009_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_x_1004_, v_head_1007_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_dec(v_tail_1008_);
return v___x_1009_;
}
else
{
lean_object* v_a_1010_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v_x_1004_ = v_a_1010_;
v_x_1005_ = v_tail_1008_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserTokens(lean_object* v_tokenTable_1012_, lean_object* v_info_1013_){
_start:
{
lean_object* v_collectTokens_1014_; lean_object* v___x_1015_; lean_object* v_newTokens_1016_; lean_object* v___x_1017_; 
v_collectTokens_1014_ = lean_ctor_get(v_info_1013_, 0);
lean_inc_ref(v_collectTokens_1014_);
lean_dec_ref(v_info_1013_);
v___x_1015_ = lean_box(0);
v_newTokens_1016_ = lean_apply_1(v_collectTokens_1014_, v___x_1015_);
v___x_1017_ = l_List_foldlM___at___00Lean_Parser_addParserTokens_spec__0(v_tokenTable_1012_, v_newTokens_1016_);
return v___x_1017_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(lean_object* v_info_1020_, lean_object* v_declName_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1023_ = l_Lean_Parser_builtinTokenTable;
v___x_1024_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3332318574____hygCtx___hyg_2_);
v___x_1025_ = lean_st_ref_swap(v___x_1023_, v___x_1024_);
v___x_1026_ = l_Lean_Parser_addParserTokens(v___x_1025_, v_info_1020_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1043_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1043_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1043_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1031_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__0));
v___x_1032_ = l_Lean_privateToUserName(v_declName_1021_);
v___x_1033_ = 1;
v___x_1034_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1032_, v___x_1033_);
v___x_1035_ = lean_string_append(v___x_1031_, v___x_1034_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_1037_ = lean_string_append(v___x_1035_, v___x_1036_);
v___x_1038_ = lean_string_append(v___x_1037_, v_a_1027_);
lean_dec(v_a_1027_);
v___x_1039_ = lean_mk_io_user_error(v___x_1038_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set_tag(v___x_1029_, 1);
lean_ctor_set(v___x_1029_, 0, v___x_1039_);
v___x_1041_ = v___x_1029_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1053_; 
lean_dec(v_declName_1021_);
v_a_1044_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1046_ = v___x_1026_;
v_isShared_1047_ = v_isSharedCheck_1053_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1026_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1053_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1048_ = lean_box(0);
v___x_1049_ = lean_st_ref_swap(v___x_1023_, v_a_1044_);
lean_dec(v___x_1049_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1048_);
v___x_1051_ = v___x_1046_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1048_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_1020_ = stack[0].m_obj;
lean_object* v_declName_1021_ = stack[1].m_obj;
lean_object* v_res_1054_;
v_res_1054_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_1020_, v_declName_1021_);
stack->m_obj
 = v_res_1054_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___boxed(lean_object* v_info_1055_, lean_object* v_declName_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_1055_, v_declName_1056_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(lean_object* v_msg_1059_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_1061_ = lean_panic_fn_borrowed(v___x_1060_, v_msg_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserExtension_addEntryImpl(lean_object* v_s_1065_, lean_object* v_e_1066_){
_start:
{
switch(lean_obj_tag(v_e_1066_))
{
case 0:
{
lean_object* v_val_1067_; lean_object* v_tokens_1068_; lean_object* v_kinds_1069_; lean_object* v_categories_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1088_; 
v_val_1067_ = lean_ctor_get(v_e_1066_, 0);
lean_inc_ref(v_val_1067_);
lean_dec_ref_known(v_e_1066_, 1);
v_tokens_1068_ = lean_ctor_get(v_s_1065_, 0);
v_kinds_1069_ = lean_ctor_get(v_s_1065_, 1);
v_categories_1070_ = lean_ctor_get(v_s_1065_, 2);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_s_1065_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1072_ = v_s_1065_;
v_isShared_1073_ = v_isSharedCheck_1088_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_categories_1070_);
lean_inc(v_kinds_1069_);
lean_inc(v_tokens_1068_);
lean_dec(v_s_1065_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1088_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; 
v___x_1074_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_1068_, v_val_1067_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_del_object(v___x_1072_);
lean_dec_ref(v_categories_1070_);
lean_dec_ref(v_kinds_1069_);
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1077_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1078_ = lean_unsigned_to_nat(166u);
v___x_1079_ = lean_unsigned_to_nat(26u);
v___x_1080_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1081_ = lean_string_append(v___x_1080_, v_a_1075_);
lean_dec(v_a_1075_);
v___x_1082_ = l_mkPanicMessageWithDecl(v___x_1076_, v___x_1077_, v___x_1078_, v___x_1079_, v___x_1081_);
lean_dec_ref(v___x_1081_);
v___x_1083_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1082_);
return v___x_1083_;
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; 
v_a_1084_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1074_, 1);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v_a_1084_);
v___x_1086_ = v___x_1072_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1084_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_kinds_1069_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_categories_1070_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
case 1:
{
lean_object* v_val_1089_; lean_object* v_tokens_1090_; lean_object* v_kinds_1091_; lean_object* v_categories_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1100_; 
v_val_1089_ = lean_ctor_get(v_e_1066_, 0);
lean_inc(v_val_1089_);
lean_dec_ref_known(v_e_1066_, 1);
v_tokens_1090_ = lean_ctor_get(v_s_1065_, 0);
v_kinds_1091_ = lean_ctor_get(v_s_1065_, 1);
v_categories_1092_ = lean_ctor_get(v_s_1065_, 2);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_s_1065_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1094_ = v_s_1065_;
v_isShared_1095_ = v_isSharedCheck_1100_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_categories_1092_);
lean_inc(v_kinds_1091_);
lean_inc(v_tokens_1090_);
lean_dec(v_s_1065_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1100_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = l_Lean_Parser_SyntaxNodeKindSet_insert(v_kinds_1091_, v_val_1089_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v___x_1096_);
v___x_1098_ = v___x_1094_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_tokens_1090_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v_categories_1092_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
case 2:
{
lean_object* v_catName_1101_; lean_object* v_declName_1102_; uint8_t v_behavior_1103_; lean_object* v_tokens_1104_; lean_object* v_kinds_1105_; lean_object* v_categories_1106_; uint8_t v___x_1107_; 
v_catName_1101_ = lean_ctor_get(v_e_1066_, 0);
lean_inc(v_catName_1101_);
v_declName_1102_ = lean_ctor_get(v_e_1066_, 1);
lean_inc(v_declName_1102_);
v_behavior_1103_ = lean_ctor_get_uint8(v_e_1066_, sizeof(void*)*2);
lean_dec_ref_known(v_e_1066_, 2);
v_tokens_1104_ = lean_ctor_get(v_s_1065_, 0);
v_kinds_1105_ = lean_ctor_get(v_s_1065_, 1);
v_categories_1106_ = lean_ctor_get(v_s_1065_, 2);
v___x_1107_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_categories_1106_, v_catName_1101_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1118_; 
lean_inc_ref(v_categories_1106_);
lean_inc_ref(v_kinds_1105_);
lean_inc_ref(v_tokens_1104_);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_s_1065_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; lean_object* v_unused_1120_; lean_object* v_unused_1121_; 
v_unused_1119_ = lean_ctor_get(v_s_1065_, 2);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_s_1065_, 1);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_s_1065_, 0);
lean_dec(v_unused_1121_);
v___x_1109_ = v_s_1065_;
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
else
{
lean_dec(v_s_1065_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1111_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_1112_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory___closed__0));
v___x_1113_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1113_, 0, v_declName_1102_);
lean_ctor_set(v___x_1113_, 1, v___x_1111_);
lean_ctor_set(v___x_1113_, 2, v___x_1112_);
lean_ctor_set_uint8(v___x_1113_, sizeof(void*)*3, v_behavior_1103_);
v___x_1114_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__1___redArg(v_categories_1106_, v_catName_1101_, v___x_1113_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 2, v___x_1114_);
v___x_1116_ = v___x_1109_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_tokens_1104_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_kinds_1105_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
else
{
lean_dec(v_declName_1102_);
lean_dec(v_catName_1101_);
return v_s_1065_;
}
}
default: 
{
lean_object* v_catName_1122_; lean_object* v_declName_1123_; uint8_t v_leading_1124_; lean_object* v_p_1125_; lean_object* v_prio_1126_; lean_object* v_tokens_1127_; lean_object* v_kinds_1128_; lean_object* v_categories_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1147_; 
v_catName_1122_ = lean_ctor_get(v_e_1066_, 0);
lean_inc(v_catName_1122_);
v_declName_1123_ = lean_ctor_get(v_e_1066_, 1);
lean_inc(v_declName_1123_);
v_leading_1124_ = lean_ctor_get_uint8(v_e_1066_, sizeof(void*)*4);
v_p_1125_ = lean_ctor_get(v_e_1066_, 2);
lean_inc_ref(v_p_1125_);
v_prio_1126_ = lean_ctor_get(v_e_1066_, 3);
lean_inc(v_prio_1126_);
lean_dec_ref_known(v_e_1066_, 4);
v_tokens_1127_ = lean_ctor_get(v_s_1065_, 0);
v_kinds_1128_ = lean_ctor_get(v_s_1065_, 1);
v_categories_1129_ = lean_ctor_get(v_s_1065_, 2);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_s_1065_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1131_ = v_s_1065_;
v_isShared_1132_ = v_isSharedCheck_1147_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_categories_1129_);
lean_inc(v_kinds_1128_);
lean_inc(v_tokens_1127_);
lean_dec(v_s_1065_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1147_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_Parser_addParser(v_categories_1129_, v_catName_1122_, v_declName_1123_, v_leading_1124_, v_p_1125_, v_prio_1126_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_del_object(v___x_1131_);
lean_dec_ref(v_kinds_1128_);
lean_dec_ref(v_tokens_1127_);
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1135_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__0));
v___x_1136_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__1));
v___x_1137_ = lean_unsigned_to_nat(176u);
v___x_1138_ = lean_unsigned_to_nat(30u);
v___x_1139_ = ((lean_object*)(l_Lean_Parser_ParserExtension_addEntryImpl___closed__2));
v___x_1140_ = lean_string_append(v___x_1139_, v_a_1134_);
lean_dec(v_a_1134_);
v___x_1141_ = l_mkPanicMessageWithDecl(v___x_1135_, v___x_1136_, v___x_1137_, v___x_1138_, v___x_1140_);
lean_dec_ref(v___x_1140_);
v___x_1142_ = l_panic___at___00Lean_Parser_ParserExtension_addEntryImpl_spec__0(v___x_1141_);
return v___x_1142_;
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; 
v_a_1143_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1133_, 1);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 2, v_a_1143_);
v___x_1145_ = v___x_1131_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_tokens_1127_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_kinds_1128_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_a_1143_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl___redArg(lean_object* v_x_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_obj_tag_nat(v_x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl___redArg___boxed(lean_object* v_x_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_Parser_AliasValue_ctorIdx___impl___redArg(v_x_1150_);
lean_dec_ref(v_x_1150_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl(lean_object* v_00_u03b1_1152_, lean_object* v_x_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_obj_tag_nat(v_x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorIdx___impl___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_x_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Parser_AliasValue_ctorIdx___impl(v_00_u03b1_1155_, v_x_1156_);
lean_dec_ref(v_x_1156_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___redArg(lean_object* v_t_1158_, lean_object* v_k_1159_){
_start:
{
lean_object* v_p_1160_; lean_object* v___x_1161_; 
v_p_1160_ = lean_ctor_get(v_t_1158_, 0);
lean_inc(v_p_1160_);
lean_dec_ref(v_t_1158_);
v___x_1161_ = lean_apply_1(v_k_1159_, v_p_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim(lean_object* v_00_u03b1_1162_, lean_object* v_motive_1163_, lean_object* v_ctorIdx_1164_, lean_object* v_t_1165_, lean_object* v_h_1166_, lean_object* v_k_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1165_, v_k_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_ctorElim___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_motive_1170_, lean_object* v_ctorIdx_1171_, lean_object* v_t_1172_, lean_object* v_h_1173_, lean_object* v_k_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Parser_AliasValue_ctorElim(v_00_u03b1_1169_, v_motive_1170_, v_ctorIdx_1171_, v_t_1172_, v_h_1173_, v_k_1174_);
lean_dec(v_ctorIdx_1171_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim___redArg(lean_object* v_t_1176_, lean_object* v_const_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1176_, v_const_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_const_elim(lean_object* v_00_u03b1_1179_, lean_object* v_motive_1180_, lean_object* v_t_1181_, lean_object* v_h_1182_, lean_object* v_const_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1181_, v_const_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim___redArg(lean_object* v_t_1185_, lean_object* v_unary_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1185_, v_unary_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_unary_elim(lean_object* v_00_u03b1_1188_, lean_object* v_motive_1189_, lean_object* v_t_1190_, lean_object* v_h_1191_, lean_object* v_unary_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1190_, v_unary_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim___redArg(lean_object* v_t_1194_, lean_object* v_binary_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1194_, v_binary_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_AliasValue_binary_elim(lean_object* v_00_u03b1_1197_, lean_object* v_motive_1198_, lean_object* v_t_1199_, lean_object* v_h_1200_, lean_object* v_binary_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Parser_AliasValue_ctorElim___redArg(v_t_1199_, v_binary_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_Parser_registerAliasCore___redArg___closed__1(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__0));
v___x_1205_ = lean_mk_io_user_error(v___x_1204_);
return v___x_1205_;
}
}
lean_object* l_Lean_Parser_registerAliasCore___redArg(lean_object* v_mapRef_1208_, lean_object* v_aliasName_1209_, lean_object* v_value_1210_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = l_Lean_initializing();
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_dec_ref(v_value_1210_);
lean_dec(v_aliasName_1209_);
v___x_1213_ = lean_obj_once(&l_Lean_Parser_registerAliasCore___redArg___closed__1, &l_Lean_Parser_registerAliasCore___redArg___closed__1_once, _init_l_Lean_Parser_registerAliasCore___redArg___closed__1);
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
else
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_st_ref_get(v_mapRef_1208_);
v___x_1216_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_aliasName_1209_, v___x_1215_);
lean_dec(v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1217_ = lean_st_ref_take(v_mapRef_1208_);
v___x_1218_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1209_, v_value_1210_, v___x_1217_);
v___x_1219_ = lean_st_ref_put(v_mapRef_1208_, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec_ref(v_value_1210_);
v___x_1221_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__2));
v___x_1222_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1209_, v___x_1216_);
v___x_1223_ = lean_string_append(v___x_1221_, v___x_1222_);
lean_dec_ref(v___x_1222_);
v___x_1224_ = ((lean_object*)(l_Lean_Parser_registerAliasCore___redArg___closed__3));
v___x_1225_ = lean_string_append(v___x_1223_, v___x_1224_);
v___x_1226_ = lean_mk_io_user_error(v___x_1225_);
v___x_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_registerAliasCore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mapRef_1208_ = stack[0].m_obj;
lean_object* v_aliasName_1209_ = stack[1].m_obj;
lean_object* v_value_1210_ = stack[2].m_obj;
lean_object* v_res_1228_;
v_res_1228_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1208_, v_aliasName_1209_, v_value_1210_);
stack->m_obj
 = v_res_1228_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAliasCore___redArg___boxed(lean_object* v_mapRef_1229_, lean_object* v_aliasName_1230_, lean_object* v_value_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1229_, v_aliasName_1230_, v_value_1231_);
lean_dec(v_mapRef_1229_);
return v_res_1233_;
}
}
lean_object* l_Lean_Parser_registerAliasCore(lean_object* v_00_u03b1_1234_, lean_object* v_mapRef_1235_, lean_object* v_aliasName_1236_, lean_object* v_value_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Parser_registerAliasCore___redArg(v_mapRef_1235_, v_aliasName_1236_, v_value_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT void l_Lean_Parser_registerAliasCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mapRef_1235_ = stack[1].m_obj;
lean_object* v_aliasName_1236_ = stack[2].m_obj;
lean_object* v_value_1237_ = stack[3].m_obj;
lean_object* v_res_1240_;
v_res_1240_ = l_Lean_Parser_registerAliasCore(lean_box(0), v_mapRef_1235_, v_aliasName_1236_, v_value_1237_);
stack->m_obj
 = v_res_1240_;
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
lean_object* l_Lean_Parser_getAlias___redArg(lean_object* v_mapRef_1247_, lean_object* v_aliasName_1248_){
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
LEAN_EXPORT void l_Lean_Parser_getAlias___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mapRef_1247_ = stack[0].m_obj;
lean_object* v_aliasName_1248_ = stack[1].m_obj;
lean_object* v_res_1253_;
v_res_1253_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1247_, v_aliasName_1248_);
stack->m_obj
 = v_res_1253_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___redArg___boxed(lean_object* v_mapRef_1254_, lean_object* v_aliasName_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1254_, v_aliasName_1255_);
lean_dec(v_aliasName_1255_);
lean_dec(v_mapRef_1254_);
return v_res_1257_;
}
}
lean_object* l_Lean_Parser_getAlias(lean_object* v_00_u03b1_1258_, lean_object* v_mapRef_1259_, lean_object* v_aliasName_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1259_, v_aliasName_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT void l_Lean_Parser_getAlias_0interp(lean_interpreter_value* stack)
{
lean_object* v_mapRef_1259_ = stack[1].m_obj;
lean_object* v_aliasName_1260_ = stack[2].m_obj;
lean_object* v_res_1263_;
v_res_1263_ = l_Lean_Parser_getAlias(lean_box(0), v_mapRef_1259_, v_aliasName_1260_);
stack->m_obj
 = v_res_1263_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_getAlias___boxed(lean_object* v_00_u03b1_1264_, lean_object* v_mapRef_1265_, lean_object* v_aliasName_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Parser_getAlias(v_00_u03b1_1264_, v_mapRef_1265_, v_aliasName_1266_);
lean_dec(v_aliasName_1266_);
lean_dec(v_mapRef_1265_);
return v_res_1268_;
}
}
lean_object* l_Lean_Parser_getConstAlias___redArg(lean_object* v_mapRef_1273_, lean_object* v_aliasName_1274_){
_start:
{
lean_object* v___x_1276_; lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1316_; 
v___x_1276_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1273_, v_aliasName_1274_);
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1316_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1316_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
if (lean_obj_tag(v_a_1277_) == 0)
{
lean_object* v___x_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1281_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1282_ = 1;
v___x_1283_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1274_, v___x_1282_);
v___x_1284_ = lean_string_append(v___x_1281_, v___x_1283_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1286_ = lean_string_append(v___x_1284_, v___x_1285_);
v___x_1287_ = lean_mk_io_user_error(v___x_1286_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 1);
lean_ctor_set(v___x_1279_, 0, v___x_1287_);
v___x_1289_ = v___x_1279_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
lean_object* v_val_1291_; 
v_val_1291_ = lean_ctor_get(v_a_1277_, 0);
lean_inc(v_val_1291_);
lean_dec_ref_known(v_a_1277_, 1);
switch(lean_obj_tag(v_val_1291_))
{
case 0:
{
lean_object* v_p_1292_; lean_object* v___x_1294_; 
lean_dec(v_aliasName_1274_);
v_p_1292_ = lean_ctor_get(v_val_1291_, 0);
lean_inc(v_p_1292_);
lean_dec_ref_known(v_val_1291_, 1);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v_p_1292_);
v___x_1294_ = v___x_1279_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_p_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
case 1:
{
lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
lean_dec_ref_known(v_val_1291_, 1);
v___x_1296_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1297_ = 1;
v___x_1298_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1274_, v___x_1297_);
v___x_1299_ = lean_string_append(v___x_1296_, v___x_1298_);
lean_dec_ref(v___x_1298_);
v___x_1300_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__2));
v___x_1301_ = lean_string_append(v___x_1299_, v___x_1300_);
v___x_1302_ = lean_mk_io_user_error(v___x_1301_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 1);
lean_ctor_set(v___x_1279_, 0, v___x_1302_);
v___x_1304_ = v___x_1279_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
default: 
{
lean_object* v___x_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_dec_ref_known(v_val_1291_, 1);
v___x_1306_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1307_ = 1;
v___x_1308_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1274_, v___x_1307_);
v___x_1309_ = lean_string_append(v___x_1306_, v___x_1308_);
lean_dec_ref(v___x_1308_);
v___x_1310_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__3));
v___x_1311_ = lean_string_append(v___x_1309_, v___x_1310_);
v___x_1312_ = lean_mk_io_user_error(v___x_1311_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 1);
lean_ctor_set(v___x_1279_, 0, v___x_1312_);
v___x_1314_ = v___x_1279_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_getConstAlias___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mapRef_1273_ = stack[0].m_obj;
lean_object* v_aliasName_1274_ = stack[1].m_obj;
lean_object* v_res_1317_;
v_res_1317_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1273_, v_aliasName_1274_);
stack->m_obj
 = v_res_1317_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___redArg___boxed(lean_object* v_mapRef_1318_, lean_object* v_aliasName_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1318_, v_aliasName_1319_);
lean_dec(v_mapRef_1318_);
return v_res_1321_;
}
}
lean_object* l_Lean_Parser_getConstAlias(lean_object* v_00_u03b1_1322_, lean_object* v_mapRef_1323_, lean_object* v_aliasName_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Parser_getConstAlias___redArg(v_mapRef_1323_, v_aliasName_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT void l_Lean_Parser_getConstAlias_0interp(lean_interpreter_value* stack)
{
lean_object* v_mapRef_1323_ = stack[1].m_obj;
lean_object* v_aliasName_1324_ = stack[2].m_obj;
lean_object* v_res_1327_;
v_res_1327_ = l_Lean_Parser_getConstAlias(lean_box(0), v_mapRef_1323_, v_aliasName_1324_);
stack->m_obj
 = v_res_1327_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_getConstAlias___boxed(lean_object* v_00_u03b1_1328_, lean_object* v_mapRef_1329_, lean_object* v_aliasName_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Parser_getConstAlias(v_00_u03b1_1328_, v_mapRef_1329_, v_aliasName_1330_);
lean_dec(v_mapRef_1329_);
return v_res_1332_;
}
}
lean_object* l_Lean_Parser_getUnaryAlias___redArg(lean_object* v_mapRef_1334_, lean_object* v_aliasName_1335_){
_start:
{
lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1367_; 
v___x_1337_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1334_, v_aliasName_1335_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1367_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1367_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
if (lean_obj_tag(v_a_1338_) == 0)
{
lean_object* v___x_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1342_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1343_ = 1;
v___x_1344_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1335_, v___x_1343_);
v___x_1345_ = lean_string_append(v___x_1342_, v___x_1344_);
lean_dec_ref(v___x_1344_);
v___x_1346_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1347_ = lean_string_append(v___x_1345_, v___x_1346_);
v___x_1348_ = lean_mk_io_user_error(v___x_1347_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set_tag(v___x_1340_, 1);
lean_ctor_set(v___x_1340_, 0, v___x_1348_);
v___x_1350_ = v___x_1340_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
else
{
lean_object* v_val_1352_; 
v_val_1352_ = lean_ctor_get(v_a_1338_, 0);
lean_inc(v_val_1352_);
lean_dec_ref_known(v_a_1338_, 1);
if (lean_obj_tag(v_val_1352_) == 1)
{
lean_object* v_p_1353_; lean_object* v___x_1355_; 
lean_dec(v_aliasName_1335_);
v_p_1353_ = lean_ctor_get(v_val_1352_, 0);
lean_inc(v_p_1353_);
lean_dec_ref_known(v_val_1352_, 1);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v_p_1353_);
v___x_1355_ = v___x_1340_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_p_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
else
{
lean_object* v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
lean_dec(v_val_1352_);
v___x_1357_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1358_ = 1;
v___x_1359_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1335_, v___x_1358_);
v___x_1360_ = lean_string_append(v___x_1357_, v___x_1359_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = ((lean_object*)(l_Lean_Parser_getUnaryAlias___redArg___closed__0));
v___x_1362_ = lean_string_append(v___x_1360_, v___x_1361_);
v___x_1363_ = lean_mk_io_user_error(v___x_1362_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set_tag(v___x_1340_, 1);
lean_ctor_set(v___x_1340_, 0, v___x_1363_);
v___x_1365_ = v___x_1340_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_getUnaryAlias___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mapRef_1334_ = stack[0].m_obj;
lean_object* v_aliasName_1335_ = stack[1].m_obj;
lean_object* v_res_1368_;
v_res_1368_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1334_, v_aliasName_1335_);
stack->m_obj
 = v_res_1368_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___redArg___boxed(lean_object* v_mapRef_1369_, lean_object* v_aliasName_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1369_, v_aliasName_1370_);
lean_dec(v_mapRef_1369_);
return v_res_1372_;
}
}
lean_object* l_Lean_Parser_getUnaryAlias(lean_object* v_00_u03b1_1373_, lean_object* v_mapRef_1374_, lean_object* v_aliasName_1375_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_Parser_getUnaryAlias___redArg(v_mapRef_1374_, v_aliasName_1375_);
return v___x_1377_;
}
}
LEAN_EXPORT void l_Lean_Parser_getUnaryAlias_0interp(lean_interpreter_value* stack)
{
lean_object* v_mapRef_1374_ = stack[1].m_obj;
lean_object* v_aliasName_1375_ = stack[2].m_obj;
lean_object* v_res_1378_;
v_res_1378_ = l_Lean_Parser_getUnaryAlias(lean_box(0), v_mapRef_1374_, v_aliasName_1375_);
stack->m_obj
 = v_res_1378_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_getUnaryAlias___boxed(lean_object* v_00_u03b1_1379_, lean_object* v_mapRef_1380_, lean_object* v_aliasName_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_Parser_getUnaryAlias(v_00_u03b1_1379_, v_mapRef_1380_, v_aliasName_1381_);
lean_dec(v_mapRef_1380_);
return v_res_1383_;
}
}
lean_object* l_Lean_Parser_getBinaryAlias___redArg(lean_object* v_mapRef_1385_, lean_object* v_aliasName_1386_){
_start:
{
lean_object* v___x_1388_; lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1418_; 
v___x_1388_ = l_Lean_Parser_getAlias___redArg(v_mapRef_1385_, v_aliasName_1386_);
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1418_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1418_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
if (lean_obj_tag(v_a_1389_) == 0)
{
lean_object* v___x_1393_; uint8_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1393_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1394_ = 1;
v___x_1395_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1386_, v___x_1394_);
v___x_1396_ = lean_string_append(v___x_1393_, v___x_1395_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__1));
v___x_1398_ = lean_string_append(v___x_1396_, v___x_1397_);
v___x_1399_ = lean_mk_io_user_error(v___x_1398_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 1);
lean_ctor_set(v___x_1391_, 0, v___x_1399_);
v___x_1401_ = v___x_1391_;
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
else
{
lean_object* v_val_1403_; 
v_val_1403_ = lean_ctor_get(v_a_1389_, 0);
lean_inc(v_val_1403_);
lean_dec_ref_known(v_a_1389_, 1);
if (lean_obj_tag(v_val_1403_) == 2)
{
lean_object* v_p_1404_; lean_object* v___x_1406_; 
lean_dec(v_aliasName_1386_);
v_p_1404_ = lean_ctor_get(v_val_1403_, 0);
lean_inc(v_p_1404_);
lean_dec_ref_known(v_val_1403_, 1);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v_p_1404_);
v___x_1406_ = v___x_1391_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_p_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
else
{
lean_object* v___x_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
lean_dec(v_val_1403_);
v___x_1408_ = ((lean_object*)(l_Lean_Parser_getConstAlias___redArg___closed__0));
v___x_1409_ = 1;
v___x_1410_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_aliasName_1386_, v___x_1409_);
v___x_1411_ = lean_string_append(v___x_1408_, v___x_1410_);
lean_dec_ref(v___x_1410_);
v___x_1412_ = ((lean_object*)(l_Lean_Parser_getBinaryAlias___redArg___closed__0));
v___x_1413_ = lean_string_append(v___x_1411_, v___x_1412_);
v___x_1414_ = lean_mk_io_user_error(v___x_1413_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 1);
lean_ctor_set(v___x_1391_, 0, v___x_1414_);
v___x_1416_ = v___x_1391_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_getBinaryAlias___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mapRef_1385_ = stack[0].m_obj;
lean_object* v_aliasName_1386_ = stack[1].m_obj;
lean_object* v_res_1419_;
v_res_1419_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1385_, v_aliasName_1386_);
stack->m_obj
 = v_res_1419_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___redArg___boxed(lean_object* v_mapRef_1420_, lean_object* v_aliasName_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1420_, v_aliasName_1421_);
lean_dec(v_mapRef_1420_);
return v_res_1423_;
}
}
lean_object* l_Lean_Parser_getBinaryAlias(lean_object* v_00_u03b1_1424_, lean_object* v_mapRef_1425_, lean_object* v_aliasName_1426_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_Parser_getBinaryAlias___redArg(v_mapRef_1425_, v_aliasName_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT void l_Lean_Parser_getBinaryAlias_0interp(lean_interpreter_value* stack)
{
lean_object* v_mapRef_1425_ = stack[1].m_obj;
lean_object* v_aliasName_1426_ = stack[2].m_obj;
lean_object* v_res_1429_;
v_res_1429_ = l_Lean_Parser_getBinaryAlias(lean_box(0), v_mapRef_1425_, v_aliasName_1426_);
stack->m_obj
 = v_res_1429_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_getBinaryAlias___boxed(lean_object* v_00_u03b1_1430_, lean_object* v_mapRef_1431_, lean_object* v_aliasName_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_Parser_getBinaryAlias(v_00_u03b1_1430_, v_mapRef_1431_, v_aliasName_1432_);
lean_dec(v_mapRef_1431_);
return v_res_1434_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = lean_box(1);
v___x_1437_ = lean_st_mk_ref(v___x_1436_);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1439_;
v_res_1439_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1439_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2____boxed(lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1840072248____hygCtx___hyg_2_();
return v_res_1441_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = lean_box(1);
v___x_1444_ = lean_st_mk_ref(v___x_1443_);
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1446_;
v_res_1446_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1446_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2____boxed(lean_object* v_a_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1409780179____hygCtx___hyg_2_();
return v_res_1448_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = lean_box(1);
v___x_1451_ = lean_st_mk_ref(v___x_1450_);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1453_;
v_res_1453_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1453_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2____boxed(lean_object* v_a_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1856488369____hygCtx___hyg_2_();
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(lean_object* v_t_1456_, lean_object* v_k_1457_, lean_object* v_fallback_1458_){
_start:
{
if (lean_obj_tag(v_t_1456_) == 0)
{
lean_object* v_k_1459_; lean_object* v_v_1460_; lean_object* v_l_1461_; lean_object* v_r_1462_; uint8_t v___x_1463_; 
v_k_1459_ = lean_ctor_get(v_t_1456_, 1);
v_v_1460_ = lean_ctor_get(v_t_1456_, 2);
v_l_1461_ = lean_ctor_get(v_t_1456_, 3);
v_r_1462_ = lean_ctor_get(v_t_1456_, 4);
v___x_1463_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1457_, v_k_1459_);
switch(v___x_1463_)
{
case 0:
{
v_t_1456_ = v_l_1461_;
goto _start;
}
case 1:
{
lean_inc(v_v_1460_);
return v_v_1460_;
}
default: 
{
v_t_1456_ = v_r_1462_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_1458_);
return v_fallback_1458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg___boxed(lean_object* v_t_1466_, lean_object* v_k_1467_, lean_object* v_fallback_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1466_, v_k_1467_, v_fallback_1468_);
lean_dec(v_fallback_1468_);
lean_dec(v_k_1467_);
lean_dec(v_t_1466_);
return v_res_1469_;
}
}
lean_object* l_Lean_Parser_getParserAliasInfo(lean_object* v_aliasName_1476_){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1478_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1479_ = lean_st_ref_get(v___x_1478_);
v___x_1480_ = ((lean_object*)(l_Lean_Parser_getParserAliasInfo___closed__1));
v___x_1481_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v___x_1479_, v_aliasName_1476_, v___x_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT void l_Lean_Parser_getParserAliasInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_aliasName_1476_ = stack[0].m_obj;
lean_object* v_res_1483_;
v_res_1483_ = l_Lean_Parser_getParserAliasInfo(v_aliasName_1476_);
stack->m_obj
 = v_res_1483_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserAliasInfo___boxed(lean_object* v_aliasName_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Parser_getParserAliasInfo(v_aliasName_1484_);
lean_dec(v_aliasName_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(lean_object* v_00_u03b4_1487_, lean_object* v_t_1488_, lean_object* v_k_1489_, lean_object* v_fallback_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___redArg(v_t_1488_, v_k_1489_, v_fallback_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0___boxed(lean_object* v_00_u03b4_1492_, lean_object* v_t_1493_, lean_object* v_k_1494_, lean_object* v_fallback_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Parser_getParserAliasInfo_spec__0(v_00_u03b4_1492_, v_t_1493_, v_k_1494_, v_fallback_1495_);
lean_dec(v_fallback_1495_);
lean_dec(v_k_1494_);
lean_dec(v_t_1493_);
return v_res_1496_;
}
}
lean_object* l_Lean_Parser_registerAlias(lean_object* v_aliasName_1497_, lean_object* v_declName_1498_, lean_object* v_p_1499_, lean_object* v_kind_x3f_1500_, lean_object* v_info_1501_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = l_Lean_Parser_parserAliasesRef;
lean_inc(v_aliasName_1497_);
v___x_1520_ = l_Lean_Parser_registerAliasCore___redArg(v___x_1519_, v_aliasName_1497_, v_p_1499_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_dec_ref_known(v___x_1520_, 1);
if (lean_obj_tag(v_kind_x3f_1500_) == 1)
{
lean_object* v_val_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_val_1521_ = lean_ctor_get(v_kind_x3f_1500_, 0);
lean_inc(v_val_1521_);
lean_dec_ref_known(v_kind_x3f_1500_, 1);
v___x_1522_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1523_ = lean_st_ref_take(v___x_1522_);
lean_inc(v_aliasName_1497_);
v___x_1524_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1497_, v_val_1521_, v___x_1523_);
v___x_1525_ = lean_st_ref_put(v___x_1522_, v___x_1524_);
goto v___jp_1503_;
}
else
{
lean_dec(v_kind_x3f_1500_);
goto v___jp_1503_;
}
}
else
{
lean_dec_ref(v_info_1501_);
lean_dec(v_kind_x3f_1500_);
lean_dec(v_declName_1498_);
lean_dec(v_aliasName_1497_);
return v___x_1520_;
}
v___jp_1503_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_stackSz_x3f_1506_; uint8_t v_autoGroupArgs_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1517_; 
v___x_1504_ = l_Lean_Parser_parserAliases2infoRef;
v___x_1505_ = lean_st_ref_take(v___x_1504_);
v_stackSz_x3f_1506_ = lean_ctor_get(v_info_1501_, 1);
v_autoGroupArgs_1507_ = lean_ctor_get_uint8(v_info_1501_, sizeof(void*)*2);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_info_1501_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v_info_1501_, 0);
lean_dec(v_unused_1518_);
v___x_1509_ = v_info_1501_;
v_isShared_1510_ = v_isSharedCheck_1517_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_stackSz_x3f_1506_);
lean_dec(v_info_1501_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1517_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v_declName_1498_);
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_declName_1498_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_stackSz_x3f_1506_);
lean_ctor_set_uint8(v_reuseFailAlloc_1516_, sizeof(void*)*2, v_autoGroupArgs_1507_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_aliasName_1497_, v___x_1512_, v___x_1505_);
v___x_1514_ = lean_st_ref_put(v___x_1504_, v___x_1513_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_registerAlias_0interp(lean_interpreter_value* stack)
{
lean_object* v_aliasName_1497_ = stack[0].m_obj;
lean_object* v_declName_1498_ = stack[1].m_obj;
lean_object* v_p_1499_ = stack[2].m_obj;
lean_object* v_kind_x3f_1500_ = stack[3].m_obj;
lean_object* v_info_1501_ = stack[4].m_obj;
lean_object* v_res_1526_;
v_res_1526_ = l_Lean_Parser_registerAlias(v_aliasName_1497_, v_declName_1498_, v_p_1499_, v_kind_x3f_1500_, v_info_1501_);
stack->m_obj
 = v_res_1526_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerAlias___boxed(lean_object* v_aliasName_1527_, lean_object* v_declName_1528_, lean_object* v_p_1529_, lean_object* v_kind_x3f_1530_, lean_object* v_info_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_Parser_registerAlias(v_aliasName_1527_, v_declName_1528_, v_p_1529_, v_kind_x3f_1530_, v_info_1531_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserParserAliasValue___lam__0(lean_object* v_p_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_p_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserParserAliasValue___lam__0(lean_object* v_p_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1539_, 0, v_p_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeForallParserForallParserAliasValue___lam__0(lean_object* v_p_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_p_1542_);
return v___x_1543_;
}
}
lean_object* l_Lean_Parser_isParserAlias(lean_object* v_aliasName_1546_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1564_; 
v___x_1548_ = l_Lean_Parser_parserAliasesRef;
v___x_1549_ = l_Lean_Parser_getAlias___redArg(v___x_1548_, v_aliasName_1546_);
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1564_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1564_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
if (lean_obj_tag(v_a_1550_) == 1)
{
uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
lean_dec_ref_known(v_a_1550_, 1);
v___x_1554_ = 1;
v___x_1555_ = lean_box(v___x_1554_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1555_);
v___x_1557_ = v___x_1552_;
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
else
{
uint8_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
lean_dec(v_a_1550_);
v___x_1559_ = 0;
v___x_1560_ = lean_box(v___x_1559_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1560_);
v___x_1562_ = v___x_1552_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_isParserAlias_0interp(lean_interpreter_value* stack)
{
lean_object* v_aliasName_1546_ = stack[0].m_obj;
lean_object* v_res_1565_;
v_res_1565_ = l_Lean_Parser_isParserAlias(v_aliasName_1546_);
stack->m_obj
 = v_res_1565_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserAlias___boxed(lean_object* v_aliasName_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Parser_isParserAlias(v_aliasName_1566_);
lean_dec(v_aliasName_1566_);
return v_res_1568_;
}
}
lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(lean_object* v_aliasName_1569_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1571_ = l_Lean_Parser_parserAlias2kindRef;
v___x_1572_ = lean_st_ref_get(v___x_1571_);
v___x_1573_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1572_, v_aliasName_1569_);
lean_dec(v___x_1572_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT void l_Lean_Parser_getSyntaxKindOfParserAlias_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_aliasName_1569_ = stack[0].m_obj;
lean_object* v_res_1575_;
v_res_1575_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v_aliasName_1569_);
stack->m_obj
 = v_res_1575_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxKindOfParserAlias_x3f___boxed(lean_object* v_aliasName_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_Parser_getSyntaxKindOfParserAlias_x3f(v_aliasName_1576_);
lean_dec(v_aliasName_1576_);
return v_res_1578_;
}
}
lean_object* l_Lean_Parser_ensureUnaryParserAlias(lean_object* v_aliasName_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = l_Lean_Parser_parserAliasesRef;
v___x_1582_ = lean_box(0);
v___x_1583_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1581_, v_aliasName_1579_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v___x_1583_, 0);
lean_dec(v_unused_1591_);
v___x_1585_ = v___x_1583_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_dec(v___x_1583_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1582_);
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1582_);
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
v_a_1592_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1583_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1583_);
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
LEAN_EXPORT void l_Lean_Parser_ensureUnaryParserAlias_0interp(lean_interpreter_value* stack)
{
lean_object* v_aliasName_1579_ = stack[0].m_obj;
lean_object* v_res_1600_;
v_res_1600_ = l_Lean_Parser_ensureUnaryParserAlias(v_aliasName_1579_);
stack->m_obj
 = v_res_1600_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureUnaryParserAlias___boxed(lean_object* v_aliasName_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Parser_ensureUnaryParserAlias(v_aliasName_1601_);
return v_res_1603_;
}
}
lean_object* l_Lean_Parser_ensureBinaryParserAlias(lean_object* v_aliasName_1604_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = l_Lean_Parser_parserAliasesRef;
v___x_1607_ = lean_box(0);
v___x_1608_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1606_, v_aliasName_1604_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v___x_1608_, 0);
lean_dec(v_unused_1616_);
v___x_1610_ = v___x_1608_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_dec(v___x_1608_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1607_);
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1607_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_a_1617_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1608_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1608_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_ensureBinaryParserAlias_0interp(lean_interpreter_value* stack)
{
lean_object* v_aliasName_1604_ = stack[0].m_obj;
lean_object* v_res_1625_;
v_res_1625_ = l_Lean_Parser_ensureBinaryParserAlias(v_aliasName_1604_);
stack->m_obj
 = v_res_1625_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureBinaryParserAlias___boxed(lean_object* v_aliasName_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Parser_ensureBinaryParserAlias(v_aliasName_1626_);
return v_res_1628_;
}
}
lean_object* l_Lean_Parser_ensureConstantParserAlias(lean_object* v_aliasName_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = l_Lean_Parser_parserAliasesRef;
v___x_1632_ = lean_box(0);
v___x_1633_ = l_Lean_Parser_getConstAlias___redArg(v___x_1631_, v_aliasName_1629_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; 
v_unused_1641_ = lean_ctor_get(v___x_1633_, 0);
lean_dec(v_unused_1641_);
v___x_1635_ = v___x_1633_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_dec(v___x_1633_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1632_);
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1632_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_a_1642_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1633_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1633_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_ensureConstantParserAlias_0interp(lean_interpreter_value* stack)
{
lean_object* v_aliasName_1629_ = stack[0].m_obj;
lean_object* v_res_1650_;
v_res_1650_ = l_Lean_Parser_ensureConstantParserAlias(v_aliasName_1629_);
stack->m_obj
 = v_res_1650_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ensureConstantParserAlias___boxed(lean_object* v_aliasName_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Parser_ensureConstantParserAlias(v_aliasName_1651_);
return v_res_1653_;
}
}
lean_object* l_Lean_Parser_mkParserOfConstantUnsafe(lean_object* v_constName_1662_, lean_object* v_compileParserDescr_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_env_1675_; lean_object* v_opts_1676_; uint8_t v___x_1677_; lean_object* v___x_1678_; 
v_env_1675_ = lean_ctor_get(v_a_1664_, 0);
v_opts_1676_ = lean_ctor_get(v_a_1664_, 1);
v___x_1677_ = 0;
lean_inc(v_constName_1662_);
lean_inc_ref(v_env_1675_);
v___x_1678_ = l_Lean_Environment_find_x3f(v_env_1675_, v_constName_1662_, v___x_1677_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v___x_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_dec_ref(v_compileParserDescr_1663_);
v___x_1679_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_1680_ = 1;
v___x_1681_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1662_, v___x_1680_);
v___x_1682_ = lean_string_append(v___x_1679_, v___x_1681_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_1684_ = lean_string_append(v___x_1682_, v___x_1683_);
v___x_1685_ = lean_mk_io_user_error(v___x_1684_);
v___x_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
else
{
lean_object* v_val_1687_; lean_object* v___x_1688_; 
v_val_1687_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_val_1687_);
lean_dec_ref_known(v___x_1678_, 1);
v___x_1688_ = l_Lean_ConstantInfo_type(v_val_1687_);
lean_dec(v_val_1687_);
if (lean_obj_tag(v___x_1688_) == 4)
{
lean_object* v_declName_1689_; 
v_declName_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_declName_1689_);
lean_dec_ref_known(v___x_1688_, 2);
if (lean_obj_tag(v_declName_1689_) == 1)
{
lean_object* v_pre_1690_; 
v_pre_1690_ = lean_ctor_get(v_declName_1689_, 0);
lean_inc(v_pre_1690_);
if (lean_obj_tag(v_pre_1690_) == 1)
{
lean_object* v_pre_1691_; 
v_pre_1691_ = lean_ctor_get(v_pre_1690_, 0);
switch(lean_obj_tag(v_pre_1691_))
{
case 1:
{
lean_object* v_pre_1692_; 
lean_inc_ref(v_pre_1691_);
lean_dec_ref(v_compileParserDescr_1663_);
v_pre_1692_ = lean_ctor_get(v_pre_1691_, 0);
if (lean_obj_tag(v_pre_1692_) == 0)
{
lean_object* v_str_1693_; lean_object* v_str_1694_; lean_object* v_str_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_str_1693_ = lean_ctor_get(v_declName_1689_, 1);
lean_inc_ref(v_str_1693_);
lean_dec_ref_known(v_declName_1689_, 2);
v_str_1694_ = lean_ctor_get(v_pre_1690_, 1);
lean_inc_ref(v_str_1694_);
lean_dec_ref_known(v_pre_1690_, 2);
v_str_1695_ = lean_ctor_get(v_pre_1691_, 1);
lean_inc_ref(v_str_1695_);
lean_dec_ref_known(v_pre_1691_, 2);
v___x_1696_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1697_ = lean_string_dec_eq(v_str_1695_, v___x_1696_);
lean_dec_ref(v_str_1695_);
if (v___x_1697_ == 0)
{
lean_dec_ref(v_str_1694_);
lean_dec_ref(v_str_1693_);
goto v___jp_1666_;
}
else
{
lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_1699_ = lean_string_dec_eq(v_str_1694_, v___x_1698_);
lean_dec_ref(v_str_1694_);
if (v___x_1699_ == 0)
{
lean_dec_ref(v_str_1693_);
goto v___jp_1666_;
}
else
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_1701_ = lean_string_dec_eq(v_str_1693_, v___x_1700_);
if (v___x_1701_ == 0)
{
uint8_t v___x_1702_; 
v___x_1702_ = lean_string_dec_eq(v_str_1693_, v___x_1698_);
lean_dec_ref(v_str_1693_);
if (v___x_1702_ == 0)
{
goto v___jp_1666_;
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = l_Lean_Environment_evalConst___redArg(v_env_1675_, v_opts_1676_, v_constName_1662_, v___x_1702_);
lean_dec(v_constName_1662_);
v___x_1704_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1703_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1714_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1714_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1714_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1709_ = lean_box(v___x_1702_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v_a_1705_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1710_);
v___x_1712_ = v___x_1707_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
v_a_1715_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1704_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1704_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_dec_ref(v_str_1693_);
v___x_1723_ = l_Lean_Environment_evalConst___redArg(v_env_1675_, v_opts_1676_, v_constName_1662_, v___x_1701_);
lean_dec(v_constName_1662_);
v___x_1724_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1723_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1734_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1729_ = lean_box(v___x_1677_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v_a_1725_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1730_);
v___x_1732_ = v___x_1727_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
v_a_1735_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1724_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1724_);
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
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1691_, 2);
lean_dec_ref_known(v_pre_1690_, 2);
lean_dec_ref_known(v_declName_1689_, 2);
goto v___jp_1666_;
}
}
case 0:
{
lean_object* v_str_1743_; lean_object* v_str_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v_str_1743_ = lean_ctor_get(v_declName_1689_, 1);
lean_inc_ref(v_str_1743_);
lean_dec_ref_known(v_declName_1689_, 2);
v_str_1744_ = lean_ctor_get(v_pre_1690_, 1);
lean_inc_ref(v_str_1744_);
lean_dec_ref_known(v_pre_1690_, 2);
v___x_1745_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_1746_ = lean_string_dec_eq(v_str_1744_, v___x_1745_);
lean_dec_ref(v_str_1744_);
if (v___x_1746_ == 0)
{
lean_dec_ref(v_str_1743_);
lean_dec_ref(v_compileParserDescr_1663_);
goto v___jp_1666_;
}
else
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_1748_ = lean_string_dec_eq(v_str_1743_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_1750_ = lean_string_dec_eq(v_str_1743_, v___x_1749_);
lean_dec_ref(v_str_1743_);
if (v___x_1750_ == 0)
{
lean_dec_ref(v_compileParserDescr_1663_);
goto v___jp_1666_;
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = l_Lean_Environment_evalConst___redArg(v_env_1675_, v_opts_1676_, v_constName_1662_, v___x_1750_);
lean_dec(v_constName_1662_);
v___x_1752_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1751_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
lean_inc_ref(v_a_1664_);
v___x_1754_ = lean_apply_3(v_compileParserDescr_1663_, v_a_1753_, v_a_1664_, lean_box(0));
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1764_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1764_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1764_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1759_ = lean_box(v___x_1748_);
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v_a_1755_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1760_);
v___x_1762_ = v___x_1757_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
v_a_1765_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1754_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1754_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v_compileParserDescr_1663_);
v_a_1773_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1752_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1752_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec_ref(v_str_1743_);
v___x_1781_ = l_Lean_Environment_evalConst___redArg(v_env_1675_, v_opts_1676_, v_constName_1662_, v___x_1748_);
lean_dec(v_constName_1662_);
v___x_1782_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1781_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
lean_inc_ref(v_a_1664_);
v___x_1784_ = lean_apply_3(v_compileParserDescr_1663_, v_a_1783_, v_a_1664_, lean_box(0));
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1794_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1794_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1794_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1789_ = lean_box(v___x_1748_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v_a_1785_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1790_);
v___x_1792_ = v___x_1787_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v_a_1795_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1784_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1784_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec_ref(v_compileParserDescr_1663_);
v_a_1803_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1782_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1782_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
}
default: 
{
lean_dec_ref_known(v_pre_1690_, 2);
lean_dec_ref_known(v_declName_1689_, 2);
lean_dec_ref(v_compileParserDescr_1663_);
goto v___jp_1666_;
}
}
}
else
{
lean_dec_ref_known(v_declName_1689_, 2);
lean_dec(v_pre_1690_);
lean_dec_ref(v_compileParserDescr_1663_);
goto v___jp_1666_;
}
}
else
{
lean_dec(v_declName_1689_);
lean_dec_ref(v_compileParserDescr_1663_);
goto v___jp_1666_;
}
}
else
{
lean_dec_ref(v___x_1688_);
lean_dec_ref(v_compileParserDescr_1663_);
goto v___jp_1666_;
}
}
v___jp_1666_:
{
lean_object* v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1667_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__0));
v___x_1668_ = 1;
v___x_1669_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_1662_, v___x_1668_);
v___x_1670_ = lean_string_append(v___x_1667_, v___x_1669_);
lean_dec_ref(v___x_1669_);
v___x_1671_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__1));
v___x_1672_ = lean_string_append(v___x_1670_, v___x_1671_);
v___x_1673_ = lean_mk_io_user_error(v___x_1672_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_mkParserOfConstantUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1662_ = stack[0].m_obj;
lean_object* v_compileParserDescr_1663_ = stack[1].m_obj;
lean_object* v_a_1664_ = stack[2].m_obj;
lean_object* v_res_1811_;
v_res_1811_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1662_, v_compileParserDescr_1663_, v_a_1664_);
stack->m_obj
 = v_res_1811_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstantUnsafe___boxed(lean_object* v_constName_1812_, lean_object* v_compileParserDescr_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_1812_, v_compileParserDescr_1813_, v_a_1814_);
lean_dec_ref(v_a_1814_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed(lean_object* v_categories_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1817_, v_a_1818_, v_a_1819_);
lean_dec_ref(v_a_1819_);
return v_res_1821_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(lean_object* v_categories_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
switch(lean_obj_tag(v_a_1823_))
{
case 0:
{
lean_object* v_name_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec_ref(v_categories_1822_);
v_name_1826_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_name_1826_);
lean_dec_ref_known(v_a_1823_, 1);
v___x_1827_ = l_Lean_Parser_parserAliasesRef;
v___x_1828_ = l_Lean_Parser_getConstAlias___redArg(v___x_1827_, v_name_1826_);
return v___x_1828_;
}
case 1:
{
lean_object* v_name_1829_; lean_object* v_p_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_name_1829_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_name_1829_);
v_p_1830_ = lean_ctor_get(v_a_1823_, 1);
lean_inc_ref(v_p_1830_);
lean_dec_ref_known(v_a_1823_, 2);
v___x_1831_ = l_Lean_Parser_parserAliasesRef;
v___x_1832_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_1831_, v_name_1829_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1834_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
v___x_1834_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1822_, v_p_1830_, v_a_1824_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1843_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = lean_apply_1(v_a_1833_, v_a_1835_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1839_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
else
{
lean_dec(v_a_1833_);
return v___x_1834_;
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec_ref(v_p_1830_);
lean_dec_ref(v_categories_1822_);
v_a_1844_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1832_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1832_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
case 2:
{
lean_object* v_name_1852_; lean_object* v_p_u2081_1853_; lean_object* v_p_u2082_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_name_1852_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_name_1852_);
v_p_u2081_1853_ = lean_ctor_get(v_a_1823_, 1);
lean_inc_ref(v_p_u2081_1853_);
v_p_u2082_1854_ = lean_ctor_get(v_a_1823_, 2);
lean_inc_ref(v_p_u2082_1854_);
lean_dec_ref_known(v_a_1823_, 3);
v___x_1855_ = l_Lean_Parser_parserAliasesRef;
v___x_1856_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_1855_, v_name_1852_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1858_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1856_, 1);
lean_inc_ref(v_categories_1822_);
v___x_1858_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1822_, v_p_u2081_1853_, v_a_1824_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1860_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1858_, 1);
v___x_1860_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1822_, v_p_u2082_1854_, v_a_1824_);
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
v___x_1865_ = lean_apply_2(v_a_1857_, v_a_1859_, v_a_1861_);
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
lean_dec(v_a_1859_);
lean_dec(v_a_1857_);
return v___x_1860_;
}
}
else
{
lean_dec(v_a_1857_);
lean_dec_ref(v_p_u2082_1854_);
lean_dec_ref(v_categories_1822_);
return v___x_1858_;
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v_p_u2082_1854_);
lean_dec_ref(v_p_u2081_1853_);
lean_dec_ref(v_categories_1822_);
v_a_1870_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1856_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1856_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
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
case 3:
{
lean_object* v_kind_1878_; lean_object* v_prec_1879_; lean_object* v_p_1880_; lean_object* v___x_1881_; 
v_kind_1878_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_kind_1878_);
v_prec_1879_ = lean_ctor_get(v_a_1823_, 1);
lean_inc(v_prec_1879_);
v_p_1880_ = lean_ctor_get(v_a_1823_, 2);
lean_inc_ref(v_p_1880_);
lean_dec_ref_known(v_a_1823_, 3);
v___x_1881_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1822_, v_p_1880_, v_a_1824_);
if (lean_obj_tag(v___x_1881_) == 0)
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
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_dec(v_prec_1879_);
lean_dec(v_kind_1878_);
return v___x_1881_;
}
}
case 4:
{
lean_object* v_kind_1891_; lean_object* v_prec_1892_; lean_object* v_lhsPrec_1893_; lean_object* v_p_1894_; lean_object* v___x_1895_; 
v_kind_1891_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_kind_1891_);
v_prec_1892_ = lean_ctor_get(v_a_1823_, 1);
lean_inc(v_prec_1892_);
v_lhsPrec_1893_ = lean_ctor_get(v_a_1823_, 2);
lean_inc(v_lhsPrec_1893_);
v_p_1894_ = lean_ctor_get(v_a_1823_, 3);
lean_inc_ref(v_p_1894_);
lean_dec_ref_known(v_a_1823_, 4);
v___x_1895_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1822_, v_p_1894_, v_a_1824_);
if (lean_obj_tag(v___x_1895_) == 0)
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
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_dec(v_lhsPrec_1893_);
lean_dec(v_prec_1892_);
lean_dec(v_kind_1891_);
return v___x_1895_;
}
}
case 5:
{
lean_object* v_val_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1913_; 
lean_dec_ref(v_categories_1822_);
v_val_1905_ = lean_ctor_get(v_a_1823_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_a_1823_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1907_ = v_a_1823_;
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_val_1905_);
lean_dec(v_a_1823_);
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
lean_ctor_set_tag(v___x_1907_, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
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
lean_dec_ref(v_categories_1822_);
v_val_1914_ = lean_ctor_get(v_a_1823_, 0);
lean_inc_ref(v_val_1914_);
v_includeIdent_1915_ = lean_ctor_get_uint8(v_a_1823_, sizeof(void*)*1);
lean_dec_ref_known(v_a_1823_, 1);
v___x_1916_ = l_Lean_Parser_nonReservedSymbol(v_val_1914_, v_includeIdent_1915_);
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
return v___x_1917_;
}
case 7:
{
lean_object* v_catName_1918_; lean_object* v_rbp_1919_; lean_object* v___x_1920_; 
v_catName_1918_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_catName_1918_);
v_rbp_1919_ = lean_ctor_get(v_a_1823_, 1);
lean_inc(v_rbp_1919_);
lean_dec_ref_known(v_a_1823_, 2);
v___x_1920_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_1822_, v_catName_1918_);
lean_dec_ref(v_categories_1822_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
lean_dec(v_rbp_1919_);
v___x_1921_ = l_Lean_Parser_throwUnknownParserCategory___redArg(v_catName_1918_);
v___x_1922_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_1921_);
return v___x_1922_;
}
else
{
lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1930_; 
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v___x_1920_, 0);
lean_dec(v_unused_1931_);
v___x_1924_ = v___x_1920_;
v_isShared_1925_ = v_isSharedCheck_1930_;
goto v_resetjp_1923_;
}
else
{
lean_dec(v___x_1920_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1930_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1926_ = l_Lean_Parser_categoryParser(v_catName_1918_, v_rbp_1919_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set_tag(v___x_1924_, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1926_);
v___x_1928_ = v___x_1924_;
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
}
case 8:
{
lean_object* v_declName_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v_declName_1932_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_declName_1932_);
lean_dec_ref_known(v_a_1823_, 1);
v___x_1933_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit___boxed), 4, 1);
lean_closure_set(v___x_1933_, 0, v_categories_1822_);
v___x_1934_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_declName_1932_, v___x_1933_, v_a_1824_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1943_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1943_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1943_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v_snd_1939_; lean_object* v___x_1941_; 
v_snd_1939_ = lean_ctor_get(v_a_1935_, 1);
lean_inc(v_snd_1939_);
lean_dec(v_a_1935_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v_snd_1939_);
v___x_1941_ = v___x_1937_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_snd_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_a_1944_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1934_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1934_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
case 9:
{
lean_object* v_name_1952_; lean_object* v_kind_1953_; lean_object* v_p_1954_; lean_object* v___x_1955_; 
v_name_1952_ = lean_ctor_get(v_a_1823_, 0);
lean_inc_ref(v_name_1952_);
v_kind_1953_ = lean_ctor_get(v_a_1823_, 1);
lean_inc(v_kind_1953_);
v_p_1954_ = lean_ctor_get(v_a_1823_, 2);
lean_inc_ref(v_p_1954_);
lean_dec_ref_known(v_a_1823_, 3);
v___x_1955_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1822_, v_p_1954_, v_a_1824_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1966_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1966_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1966_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1960_ = 1;
lean_inc(v_kind_1953_);
v___x_1961_ = l_Lean_Parser_nodeWithAntiquot(v_name_1952_, v_kind_1953_, v_a_1956_, v___x_1960_);
v___x_1962_ = l_Lean_Parser_withCache(v_kind_1953_, v___x_1961_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1962_);
v___x_1964_ = v___x_1958_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
else
{
lean_dec(v_kind_1953_);
lean_dec_ref(v_name_1952_);
return v___x_1955_;
}
}
case 10:
{
lean_object* v_p_1967_; lean_object* v_sep_1968_; lean_object* v_psep_1969_; uint8_t v_allowTrailingSep_1970_; lean_object* v___x_1971_; 
v_p_1967_ = lean_ctor_get(v_a_1823_, 0);
lean_inc_ref(v_p_1967_);
v_sep_1968_ = lean_ctor_get(v_a_1823_, 1);
lean_inc_ref(v_sep_1968_);
v_psep_1969_ = lean_ctor_get(v_a_1823_, 2);
lean_inc_ref(v_psep_1969_);
v_allowTrailingSep_1970_ = lean_ctor_get_uint8(v_a_1823_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1823_, 3);
lean_inc_ref(v_categories_1822_);
v___x_1971_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1822_, v_p_1967_, v_a_1824_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1973_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v___x_1973_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1822_, v_psep_1969_, v_a_1824_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1982_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1978_ = l_Lean_Parser_sepBy(v_a_1972_, v_sep_1968_, v_a_1974_, v_allowTrailingSep_1970_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1978_);
v___x_1980_ = v___x_1976_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
else
{
lean_dec(v_a_1972_);
lean_dec_ref(v_sep_1968_);
return v___x_1973_;
}
}
else
{
lean_dec_ref(v_psep_1969_);
lean_dec_ref(v_sep_1968_);
lean_dec_ref(v_categories_1822_);
return v___x_1971_;
}
}
case 11:
{
lean_object* v_p_1983_; lean_object* v_sep_1984_; lean_object* v_psep_1985_; uint8_t v_allowTrailingSep_1986_; lean_object* v___x_1987_; 
v_p_1983_ = lean_ctor_get(v_a_1823_, 0);
lean_inc_ref(v_p_1983_);
v_sep_1984_ = lean_ctor_get(v_a_1823_, 1);
lean_inc_ref(v_sep_1984_);
v_psep_1985_ = lean_ctor_get(v_a_1823_, 2);
lean_inc_ref(v_psep_1985_);
v_allowTrailingSep_1986_ = lean_ctor_get_uint8(v_a_1823_, sizeof(void*)*3);
lean_dec_ref_known(v_a_1823_, 3);
lean_inc_ref(v_categories_1822_);
v___x_1987_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1822_, v_p_1983_, v_a_1824_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1989_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v___x_1989_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1822_, v_psep_1985_, v_a_1824_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1998_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_1998_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1998_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = l_Lean_Parser_sepBy1(v_a_1988_, v_sep_1984_, v_a_1990_, v_allowTrailingSep_1986_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1994_);
v___x_1996_ = v___x_1992_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
else
{
lean_dec(v_a_1988_);
lean_dec_ref(v_sep_1984_);
return v___x_1989_;
}
}
else
{
lean_dec_ref(v_psep_1985_);
lean_dec_ref(v_sep_1984_);
lean_dec_ref(v_categories_1822_);
return v___x_1987_;
}
}
default: 
{
lean_object* v_val_1999_; lean_object* v_asciiVal_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_dec_ref(v_categories_1822_);
v_val_1999_ = lean_ctor_get(v_a_1823_, 0);
lean_inc_ref(v_val_1999_);
v_asciiVal_2000_ = lean_ctor_get(v_a_1823_, 1);
lean_inc_ref(v_asciiVal_2000_);
lean_dec_ref_known(v_a_1823_, 2);
v___x_2001_ = l_Lean_Parser_unicodeSymbol___redArg(v_val_1999_, v_asciiVal_2000_);
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
return v___x_2002_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_categories_1822_ = stack[0].m_obj;
lean_object* v_a_1823_ = stack[1].m_obj;
lean_object* v_a_1824_ = stack[2].m_obj;
lean_object* v_res_2003_;
v_res_2003_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_1822_, v_a_1823_, v_a_1824_);
stack->m_obj
 = v_res_2003_;
}
lean_object* l_Lean_Parser_compileParserDescr(lean_object* v_categories_2004_, lean_object* v_d_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_2004_, v_d_2005_, v_a_2006_);
return v___x_2008_;
}
}
LEAN_EXPORT void l_Lean_Parser_compileParserDescr_0interp(lean_interpreter_value* stack)
{
lean_object* v_categories_2004_ = stack[0].m_obj;
lean_object* v_d_2005_ = stack[1].m_obj;
lean_object* v_a_2006_ = stack[2].m_obj;
lean_object* v_res_2009_;
v_res_2009_ = l_Lean_Parser_compileParserDescr(v_categories_2004_, v_d_2005_, v_a_2006_);
stack->m_obj
 = v_res_2009_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_compileParserDescr___boxed(lean_object* v_categories_2010_, lean_object* v_d_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Parser_compileParserDescr(v_categories_2010_, v_d_2011_, v_a_2012_);
lean_dec_ref(v_a_2012_);
return v_res_2014_;
}
}
lean_object* l_Lean_Parser_mkParserOfConstant___lam__0(lean_object* v_categories_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l___private_Lean_Parser_Extension_0__Lean_Parser_compileParserDescr_visit(v_categories_2015_, v___y_2016_, v___y_2017_);
return v___x_2019_;
}
}
LEAN_EXPORT void l_Lean_Parser_mkParserOfConstant___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_categories_2015_ = stack[0].m_obj;
lean_object* v___y_2016_ = stack[1].m_obj;
lean_object* v___y_2017_ = stack[2].m_obj;
lean_object* v_res_2020_;
v_res_2020_ = l_Lean_Parser_mkParserOfConstant___lam__0(v_categories_2015_, v___y_2016_, v___y_2017_);
stack->m_obj
 = v_res_2020_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___lam__0___boxed(lean_object* v_categories_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_Parser_mkParserOfConstant___lam__0(v_categories_2021_, v___y_2022_, v___y_2023_);
lean_dec_ref(v___y_2023_);
return v_res_2025_;
}
}
lean_object* l_Lean_Parser_mkParserOfConstant(lean_object* v_categories_2026_, lean_object* v_constName_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v___f_2030_; lean_object* v___x_2031_; 
v___f_2030_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserOfConstant___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2030_, 0, v_categories_2026_);
v___x_2031_ = l_Lean_Parser_mkParserOfConstantUnsafe(v_constName_2027_, v___f_2030_, v_a_2028_);
return v___x_2031_;
}
}
LEAN_EXPORT void l_Lean_Parser_mkParserOfConstant_0interp(lean_interpreter_value* stack)
{
lean_object* v_categories_2026_ = stack[0].m_obj;
lean_object* v_constName_2027_ = stack[1].m_obj;
lean_object* v_a_2028_ = stack[2].m_obj;
lean_object* v_res_2032_;
v_res_2032_ = l_Lean_Parser_mkParserOfConstant(v_categories_2026_, v_constName_2027_, v_a_2028_);
stack->m_obj
 = v_res_2032_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserOfConstant___boxed(lean_object* v_categories_2033_, lean_object* v_constName_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Parser_mkParserOfConstant(v_categories_2033_, v_constName_2034_, v_a_2035_);
lean_dec_ref(v_a_2035_);
return v_res_2037_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_st_mk_ref(v___x_2039_);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2042_;
v_res_2042_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2042_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2____boxed(lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_917526378____hygCtx___hyg_2_();
return v_res_2044_;
}
}
lean_object* l_Lean_Parser_registerParserAttributeHook(lean_object* v_hook_2045_){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2047_ = l_Lean_Parser_parserAttributeHooks;
v___x_2048_ = lean_st_ref_take(v___x_2047_);
v___x_2049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2049_, 0, v_hook_2045_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = lean_st_ref_put(v___x_2047_, v___x_2049_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT void l_Lean_Parser_registerParserAttributeHook_0interp(lean_interpreter_value* stack)
{
lean_object* v_hook_2045_ = stack[0].m_obj;
lean_object* v_res_2052_;
v_res_2052_ = l_Lean_Parser_registerParserAttributeHook(v_hook_2045_);
stack->m_obj
 = v_res_2052_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserAttributeHook___boxed(lean_object* v_hook_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_Parser_registerParserAttributeHook(v_hook_2053_);
return v_res_2055_;
}
}
lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(lean_object* v_catName_2056_, lean_object* v_declName_2057_, uint8_t v_builtin_2058_, lean_object* v_as_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
if (lean_obj_tag(v_as_2059_) == 0)
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_dec(v_declName_2057_);
lean_dec(v_catName_2056_);
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
return v___x_2064_;
}
else
{
lean_object* v_head_2065_; lean_object* v_tail_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v_head_2065_ = lean_ctor_get(v_as_2059_, 0);
lean_inc(v_head_2065_);
v_tail_2066_ = lean_ctor_get(v_as_2059_, 1);
lean_inc(v_tail_2066_);
lean_dec_ref_known(v_as_2059_, 2);
v___x_2067_ = lean_box(v_builtin_2058_);
lean_inc(v___y_2061_);
lean_inc_ref(v___y_2060_);
lean_inc(v_declName_2057_);
lean_inc(v_catName_2056_);
v___x_2068_ = lean_apply_6(v_head_2065_, v_catName_2056_, v_declName_2057_, v___x_2067_, v___y_2060_, v___y_2061_, lean_box(0));
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_dec_ref_known(v___x_2068_, 1);
v_as_2059_ = v_tail_2066_;
goto _start;
}
else
{
lean_dec(v_tail_2066_);
lean_dec(v_declName_2057_);
lean_dec(v_catName_2056_);
return v___x_2068_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_catName_2056_ = stack[0].m_obj;
lean_object* v_declName_2057_ = stack[1].m_obj;
uint8_t v_builtin_2058_ = stack[2].m_num;
lean_object* v_as_2059_ = stack[3].m_obj;
lean_object* v___y_2060_ = stack[4].m_obj;
lean_object* v___y_2061_ = stack[5].m_obj;
lean_object* v_res_2070_;
v_res_2070_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2056_, v_declName_2057_, v_builtin_2058_, v_as_2059_, v___y_2060_, v___y_2061_);
stack->m_obj
 = v_res_2070_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0___boxed(lean_object* v_catName_2071_, lean_object* v_declName_2072_, lean_object* v_builtin_2073_, lean_object* v_as_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
uint8_t v_builtin_boxed_2078_; lean_object* v_res_2079_; 
v_builtin_boxed_2078_ = lean_unbox(v_builtin_2073_);
v_res_2079_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2071_, v_declName_2072_, v_builtin_boxed_2078_, v_as_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
return v_res_2079_;
}
}
lean_object* l_Lean_Parser_runParserAttributeHooks(lean_object* v_catName_2080_, lean_object* v_declName_2081_, uint8_t v_builtin_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = l_Lean_Parser_parserAttributeHooks;
v___x_2087_ = lean_st_ref_get(v___x_2086_);
v___x_2088_ = l_List_forM___at___00Lean_Parser_runParserAttributeHooks_spec__0(v_catName_2080_, v_declName_2081_, v_builtin_2082_, v___x_2087_, v_a_2083_, v_a_2084_);
return v___x_2088_;
}
}
LEAN_EXPORT void l_Lean_Parser_runParserAttributeHooks_0interp(lean_interpreter_value* stack)
{
lean_object* v_catName_2080_ = stack[0].m_obj;
lean_object* v_declName_2081_ = stack[1].m_obj;
uint8_t v_builtin_2082_ = stack[2].m_num;
lean_object* v_a_2083_ = stack[3].m_obj;
lean_object* v_a_2084_ = stack[4].m_obj;
lean_object* v_res_2089_;
v_res_2089_ = l_Lean_Parser_runParserAttributeHooks(v_catName_2080_, v_declName_2081_, v_builtin_2082_, v_a_2083_, v_a_2084_);
stack->m_obj
 = v_res_2089_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserAttributeHooks___boxed(lean_object* v_catName_2090_, lean_object* v_declName_2091_, lean_object* v_builtin_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
uint8_t v_builtin_boxed_2096_; lean_object* v_res_2097_; 
v_builtin_boxed_2096_ = lean_unbox(v_builtin_2092_);
v_res_2097_ = l_Lean_Parser_runParserAttributeHooks(v_catName_2090_, v_declName_2091_, v_builtin_boxed_2096_, v_a_2093_, v_a_2094_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
return v_res_2097_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2098_, lean_object* v_decl_2099_, lean_object* v_stx_2100_, uint8_t v_x_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2100_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2105_) == 0)
{
uint8_t v___x_2106_; lean_object* v___x_2107_; 
lean_dec_ref_known(v___x_2105_, 1);
v___x_2106_ = 1;
v___x_2107_ = l_Lean_Parser_runParserAttributeHooks(v___x_2098_, v_decl_2099_, v___x_2106_, v___y_2102_, v___y_2103_);
return v___x_2107_;
}
else
{
lean_dec(v_decl_2099_);
lean_dec(v___x_2098_);
return v___x_2105_;
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2098_ = stack[0].m_obj;
lean_object* v_decl_2099_ = stack[1].m_obj;
lean_object* v_stx_2100_ = stack[2].m_obj;
uint8_t v_x_2101_ = stack[3].m_num;
lean_object* v___y_2102_ = stack[4].m_obj;
lean_object* v___y_2103_ = stack[5].m_obj;
lean_object* v_res_2108_;
v_res_2108_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2098_, v_decl_2099_, v_stx_2100_, v_x_2101_, v___y_2102_, v___y_2103_);
stack->m_obj
 = v_res_2108_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2109_, lean_object* v_decl_2110_, lean_object* v_stx_2111_, lean_object* v_x_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
uint8_t v_x_1104__boxed_2116_; lean_object* v_res_2117_; 
v_x_1104__boxed_2116_ = lean_unbox(v_x_2112_);
v_res_2117_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2109_, v_decl_2110_, v_stx_2111_, v_x_1104__boxed_2116_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
return v_res_2117_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2120_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2121_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
lean_ctor_set(v___x_2123_, 2, v___x_2122_);
lean_ctor_set(v___x_2123_, 3, v___x_2122_);
lean_ctor_set(v___x_2123_, 4, v___x_2121_);
lean_ctor_set(v___x_2123_, 5, v___x_2121_);
lean_ctor_set(v___x_2123_, 6, v___x_2121_);
lean_ctor_set(v___x_2123_, 7, v___x_2121_);
lean_ctor_set(v___x_2123_, 8, v___x_2121_);
lean_ctor_set(v___x_2123_, 9, v___x_2121_);
lean_ctor_set(v___x_2123_, 10, v___x_2121_);
lean_ctor_set(v___x_2123_, 11, v___x_2120_);
return v___x_2123_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_unsigned_to_nat(32u);
v___x_2125_ = lean_mk_empty_array_with_capacity(v___x_2124_);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2127_ = ((size_t)5ULL);
v___x_2128_ = lean_unsigned_to_nat(0u);
v___x_2129_ = lean_unsigned_to_nat(32u);
v___x_2130_ = lean_mk_empty_array_with_capacity(v___x_2129_);
v___x_2131_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_2132_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___x_2130_);
lean_ctor_set(v___x_2132_, 2, v___x_2128_);
lean_ctor_set(v___x_2132_, 3, v___x_2128_);
lean_ctor_set_usize(v___x_2132_, 4, v___x_2127_);
return v___x_2132_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2133_ = lean_box(1);
v___x_2134_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_2135_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_2136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v___x_2134_);
lean_ctor_set(v___x_2136_, 2, v___x_2133_);
return v___x_2136_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; lean_object* v_toCold_2142_; lean_object* v_env_2143_; lean_object* v_options_2144_; uint8_t v___x_2145_; lean_object* v_env_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2141_ = lean_st_ref_get(v___y_2139_);
v_toCold_2142_ = lean_ctor_get(v___y_2138_, 0);
v_env_2143_ = lean_ctor_get(v___x_2141_, 0);
lean_inc_ref(v_env_2143_);
lean_dec(v___x_2141_);
v_options_2144_ = lean_ctor_get(v_toCold_2142_, 2);
v___x_2145_ = 0;
v_env_2146_ = l_Lean_Environment_setRecordingDeps(v_env_2143_, v___x_2145_);
v___x_2147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_2148_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_2144_);
v___x_2149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2149_, 0, v_env_2146_);
lean_ctor_set(v___x_2149_, 1, v___x_2147_);
lean_ctor_set(v___x_2149_, 2, v___x_2148_);
lean_ctor_set(v___x_2149_, 3, v_options_2144_);
v___x_2150_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
lean_ctor_set(v___x_2150_, 1, v_msgData_2137_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2137_ = stack[0].m_obj;
lean_object* v___y_2138_ = stack[1].m_obj;
lean_object* v___y_2139_ = stack[2].m_obj;
lean_object* v_res_2152_;
v_res_2152_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2137_, v___y_2138_, v___y_2139_);
stack->m_obj
 = v_res_2152_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2157_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_ref_2162_; lean_object* v___x_2163_; lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2172_; 
v_ref_2162_ = lean_ctor_get(v___y_2159_, 2);
v___x_2163_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0(v_msg_2158_, v___y_2159_, v___y_2160_);
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2172_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2172_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
lean_inc(v_ref_2162_);
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v_ref_2162_);
lean_ctor_set(v___x_2168_, 1, v_a_2164_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set_tag(v___x_2166_, 1);
lean_ctor_set(v___x_2166_, 0, v___x_2168_);
v___x_2170_ = v___x_2166_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2158_ = stack[0].m_obj;
lean_object* v___y_2159_ = stack[1].m_obj;
lean_object* v___y_2160_ = stack[2].m_obj;
lean_object* v_res_2173_;
v_res_2173_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2158_, v___y_2159_, v___y_2160_);
stack->m_obj
 = v_res_2173_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
return v_res_2178_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
return v___x_2181_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__2_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
return v___x_2184_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(lean_object* v___x_2185_, lean_object* v_decl_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2190_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2191_ = l_Lean_MessageData_ofName(v___x_2185_);
v___x_2192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2194_, v___y_2187_, v___y_2188_);
return v___x_2195_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2185_ = stack[0].m_obj;
lean_object* v_decl_2186_ = stack[1].m_obj;
lean_object* v___y_2187_ = stack[2].m_obj;
lean_object* v___y_2188_ = stack[3].m_obj;
lean_object* v_res_2196_;
v_res_2196_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2185_, v_decl_2186_, v___y_2187_, v___y_2188_);
stack->m_obj
 = v_res_2196_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v___x_2197_, lean_object* v_decl_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(v___x_2197_, v_decl_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v_decl_2198_);
return v_res_2202_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_unsigned_to_nat(3646333153u);
v___x_2246_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2247_ = l_Lean_Name_num___override(v___x_2246_, v___x_2245_);
return v___x_2247_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2250_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2251_ = l_Lean_Name_str___override(v___x_2250_, v___x_2249_);
return v___x_2251_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2254_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2255_ = l_Lean_Name_str___override(v___x_2254_, v___x_2253_);
return v___x_2255_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = lean_unsigned_to_nat(2u);
v___x_2257_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2258_ = l_Lean_Name_num___override(v___x_2257_, v___x_2256_);
return v___x_2258_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2265_ = 0;
v___x_2266_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2267_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2268_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2269_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set(v___x_2269_, 1, v___x_2267_);
lean_ctor_set(v___x_2269_, 2, v___x_2266_);
lean_ctor_set_uint8(v___x_2269_, sizeof(void*)*3, v___x_2265_);
return v___x_2269_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2270_; lean_object* v___f_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___f_2270_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___f_2271_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2272_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v___f_2271_);
lean_ctor_set(v___x_2273_, 2, v___f_2270_);
return v___x_2273_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_2276_ = l_Lean_registerBuiltinAttribute(v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2277_;
v_res_2277_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2277_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2____boxed(lean_object* v_a_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_();
return v_res_2279_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_2280_, lean_object* v_msg_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_2281_, v___y_2282_, v___y_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2281_ = stack[1].m_obj;
lean_object* v___y_2282_ = stack[2].m_obj;
lean_object* v___y_2283_ = stack[3].m_obj;
lean_object* v_res_2286_;
v_res_2286_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(lean_box(0), v_msg_2281_, v___y_2282_, v___y_2283_);
stack->m_obj
 = v_res_2286_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_2287_, lean_object* v_msg_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0(v_00_u03b1_2287_, v_msg_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
return v_res_2292_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(lean_object* v___x_2293_, lean_object* v_decl_2294_, lean_object* v_stx_2295_, uint8_t v_x_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2295_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2300_) == 0)
{
uint8_t v___x_2301_; lean_object* v___x_2302_; 
lean_dec_ref_known(v___x_2300_, 1);
v___x_2301_ = 0;
v___x_2302_ = l_Lean_Parser_runParserAttributeHooks(v___x_2293_, v_decl_2294_, v___x_2301_, v___y_2297_, v___y_2298_);
return v___x_2302_;
}
else
{
lean_dec(v_decl_2294_);
lean_dec(v___x_2293_);
return v___x_2300_;
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2293_ = stack[0].m_obj;
lean_object* v_decl_2294_ = stack[1].m_obj;
lean_object* v_stx_2295_ = stack[2].m_obj;
uint8_t v_x_2296_ = stack[3].m_num;
lean_object* v___y_2297_ = stack[4].m_obj;
lean_object* v___y_2298_ = stack[5].m_obj;
lean_object* v_res_2303_;
v_res_2303_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2293_, v_decl_2294_, v_stx_2295_, v_x_2296_, v___y_2297_, v___y_2298_);
stack->m_obj
 = v_res_2303_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v___x_2304_, lean_object* v_decl_2305_, lean_object* v_stx_2306_, lean_object* v_x_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
uint8_t v_x_212__boxed_2311_; lean_object* v_res_2312_; 
v_x_212__boxed_2311_ = lean_unbox(v_x_2307_);
v_res_2312_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(v___x_2304_, v_decl_2305_, v_stx_2306_, v_x_212__boxed_2311_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
return v_res_2312_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2315_ = lean_unsigned_to_nat(3789407938u);
v___x_2316_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2317_ = l_Lean_Name_num___override(v___x_2316_, v___x_2315_);
return v___x_2317_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2318_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2319_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2320_ = l_Lean_Name_str___override(v___x_2319_, v___x_2318_);
return v___x_2320_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_2322_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2323_ = l_Lean_Name_str___override(v___x_2322_, v___x_2321_);
return v___x_2323_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = lean_unsigned_to_nat(2u);
v___x_2325_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2326_ = l_Lean_Name_num___override(v___x_2325_, v___x_2324_);
return v___x_2326_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2333_ = 0;
v___x_2334_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2335_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2336_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2337_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v___x_2335_);
lean_ctor_set(v___x_2337_, 2, v___x_2334_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*3, v___x_2333_);
return v___x_2337_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2338_; lean_object* v___f_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___f_2338_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___f_2339_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_));
v___x_2340_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
lean_ctor_set(v___x_2341_, 1, v___f_2339_);
lean_ctor_set(v___x_2341_, 2, v___f_2338_);
return v___x_2341_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_);
v___x_2344_ = l_Lean_registerBuiltinAttribute(v___x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2345_;
v_res_2345_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2345_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2____boxed(lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3789407938____hygCtx___hyg_2_();
return v_res_2347_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(lean_object* v_s_2348_, lean_object* v_x_2349_, lean_object* v_a_2350_){
_start:
{
switch(lean_obj_tag(v_x_2349_))
{
case 0:
{
lean_object* v_val_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v_s_2348_);
v_val_2352_ = lean_ctor_get(v_x_2349_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_x_2349_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2354_ = v_x_2349_;
v_isShared_2355_ = v_isSharedCheck_2360_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_val_2352_);
lean_dec(v_x_2349_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2360_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_val_2352_);
v___x_2357_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
return v___x_2358_;
}
}
}
case 1:
{
lean_object* v_val_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2369_; 
lean_dec_ref(v_s_2348_);
v_val_2361_ = lean_ctor_get(v_x_2349_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_x_2349_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2363_ = v_x_2349_;
v_isShared_2364_ = v_isSharedCheck_2369_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_val_2361_);
lean_dec(v_x_2349_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2369_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_val_2361_);
v___x_2366_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2367_; 
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
return v___x_2367_;
}
}
}
case 2:
{
lean_object* v_catName_2370_; lean_object* v_declName_2371_; uint8_t v_behavior_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2380_; 
lean_dec_ref(v_s_2348_);
v_catName_2370_ = lean_ctor_get(v_x_2349_, 0);
v_declName_2371_ = lean_ctor_get(v_x_2349_, 1);
v_behavior_2372_ = lean_ctor_get_uint8(v_x_2349_, sizeof(void*)*2);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_x_2349_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2374_ = v_x_2349_;
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_declName_2371_);
lean_inc(v_catName_2370_);
lean_dec(v_x_2349_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2380_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_catName_2370_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_declName_2371_);
lean_ctor_set_uint8(v_reuseFailAlloc_2379_, sizeof(void*)*2, v_behavior_2372_);
v___x_2377_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
}
}
default: 
{
lean_object* v_catName_2381_; lean_object* v_declName_2382_; lean_object* v_prio_2383_; lean_object* v_categories_2384_; lean_object* v___x_2385_; 
v_catName_2381_ = lean_ctor_get(v_x_2349_, 0);
lean_inc(v_catName_2381_);
v_declName_2382_ = lean_ctor_get(v_x_2349_, 1);
lean_inc_n(v_declName_2382_, 2);
v_prio_2383_ = lean_ctor_get(v_x_2349_, 2);
lean_inc(v_prio_2383_);
lean_dec_ref_known(v_x_2349_, 3);
v_categories_2384_ = lean_ctor_get(v_s_2348_, 2);
lean_inc_ref(v_categories_2384_);
lean_dec_ref(v_s_2348_);
v___x_2385_ = l_Lean_Parser_mkParserOfConstant(v_categories_2384_, v_declName_2382_, v_a_2350_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2397_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2397_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2397_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v_fst_2390_; lean_object* v_snd_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2395_; 
v_fst_2390_ = lean_ctor_get(v_a_2386_, 0);
lean_inc(v_fst_2390_);
v_snd_2391_ = lean_ctor_get(v_a_2386_, 1);
lean_inc(v_snd_2391_);
lean_dec(v_a_2386_);
v___x_2392_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_2392_, 0, v_catName_2381_);
lean_ctor_set(v___x_2392_, 1, v_declName_2382_);
lean_ctor_set(v___x_2392_, 2, v_snd_2391_);
lean_ctor_set(v___x_2392_, 3, v_prio_2383_);
v___x_2393_ = lean_unbox(v_fst_2390_);
lean_dec(v_fst_2390_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*4, v___x_2393_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2392_);
v___x_2395_ = v___x_2388_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2392_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec(v_prio_2383_);
lean_dec(v_declName_2382_);
lean_dec(v_catName_2381_);
v_a_2398_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2385_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2385_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2348_ = stack[0].m_obj;
lean_object* v_x_2349_ = stack[1].m_obj;
lean_object* v_a_2350_ = stack[2].m_obj;
lean_object* v_res_2406_;
v_res_2406_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(v_s_2348_, v_x_2349_, v_a_2350_);
stack->m_obj
 = v_res_2406_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry___boxed(lean_object* v_s_2407_, lean_object* v_x_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_OLeanEntry_toEntry(v_s_2407_, v_x_2408_, v_a_2409_);
lean_dec_ref(v_a_2409_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v_x_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_a_2413_);
lean_inc_ref_n(v___x_2414_, 2);
v___x_2415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
lean_ctor_set(v___x_2415_, 2, v___x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_x_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v_x_2416_, v_a_2417_);
lean_dec_ref(v_x_2416_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(lean_object* v___y_2419_){
_start:
{
lean_inc_ref(v___y_2419_);
return v___y_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(v___y_2420_);
lean_dec_ref(v___y_2420_);
return v_res_2421_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2432_; uint8_t v___x_2433_; lean_object* v___f_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2432_ = lean_box(0);
v___x_2433_ = 0;
v___f_2434_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___f_2435_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2436_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2437_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2438_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2439_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserExtension_mkInitial___boxed), 1, 0);
v___x_2440_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_));
v___x_2441_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
lean_ctor_set(v___x_2441_, 1, v___x_2439_);
lean_ctor_set(v___x_2441_, 2, v___x_2438_);
lean_ctor_set(v___x_2441_, 3, v___x_2437_);
lean_ctor_set(v___x_2441_, 4, v___x_2436_);
lean_ctor_set(v___x_2441_, 5, v___f_2435_);
lean_ctor_set(v___x_2441_, 6, v___f_2434_);
lean_ctor_set(v___x_2441_, 7, v___x_2432_);
lean_ctor_set_uint8(v___x_2441_, sizeof(void*)*8, v___x_2433_);
lean_ctor_set_uint8(v___x_2441_, sizeof(void*)*8 + 1, v___x_2433_);
return v___x_2441_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_);
v___x_2444_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2445_;
v_res_2445_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2445_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2____boxed(lean_object* v_a_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_227734417____hygCtx___hyg_2_();
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f(lean_object* v_env_2448_, lean_object* v_catName_2449_){
_start:
{
lean_object* v___x_2450_; lean_object* v_ext_2451_; lean_object* v_toEnvExtension_2452_; lean_object* v_asyncMode_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; lean_object* v_categories_2457_; lean_object* v___x_2458_; 
v___x_2450_ = l_Lean_Parser_parserExtension;
v_ext_2451_ = lean_ctor_get(v___x_2450_, 1);
v_toEnvExtension_2452_ = lean_ctor_get(v_ext_2451_, 0);
v_asyncMode_2453_ = lean_ctor_get(v_toEnvExtension_2452_, 2);
v___x_2454_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2455_ = 0;
v___x_2456_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2454_, v___x_2450_, v_env_2448_, v_asyncMode_2453_, v___x_2455_);
v_categories_2457_ = lean_ctor_get(v___x_2456_, 2);
lean_inc_ref(v_categories_2457_);
lean_dec(v___x_2456_);
v___x_2458_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2457_, v_catName_2449_);
lean_dec_ref(v_categories_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserCategory_x3f___boxed(lean_object* v_env_2459_, lean_object* v_catName_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_Parser_getParserCategory_x3f(v_env_2459_, v_catName_2460_);
lean_dec(v_catName_2460_);
return v_res_2461_;
}
}
uint8_t l_Lean_Parser_isParserCategory(lean_object* v_env_2462_, lean_object* v_catName_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_Parser_getParserCategory_x3f(v_env_2462_, v_catName_2463_);
if (lean_obj_tag(v___x_2464_) == 0)
{
uint8_t v___x_2465_; 
v___x_2465_ = 0;
return v___x_2465_;
}
else
{
uint8_t v___x_2466_; 
lean_dec_ref_known(v___x_2464_, 1);
v___x_2466_ = 1;
return v___x_2466_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_isParserCategory_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2462_ = stack[0].m_obj;
lean_object* v_catName_2463_ = stack[1].m_obj;
uint8_t v_res_2467_;
v_res_2467_ = l_Lean_Parser_isParserCategory(v_env_2462_, v_catName_2463_);
stack->m_num = v_res_2467_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_isParserCategory___boxed(lean_object* v_env_2468_, lean_object* v_catName_2469_){
_start:
{
uint8_t v_res_2470_; lean_object* v_r_2471_; 
v_res_2470_ = l_Lean_Parser_isParserCategory(v_env_2468_, v_catName_2469_);
lean_dec(v_catName_2469_);
v_r_2471_ = lean_box(v_res_2470_);
return v_r_2471_;
}
}
lean_object* l_Lean_Parser_addParserCategory(lean_object* v_env_2472_, lean_object* v_catName_2473_, lean_object* v_declName_2474_, uint8_t v_behavior_2475_){
_start:
{
uint8_t v___x_2476_; 
lean_inc_ref(v_env_2472_);
v___x_2476_ = l_Lean_Parser_isParserCategory(v_env_2472_, v_catName_2473_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2477_ = l_Lean_Parser_parserExtension;
v___x_2478_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2478_, 0, v_catName_2473_);
lean_ctor_set(v___x_2478_, 1, v_declName_2474_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*2, v_behavior_2475_);
v___x_2479_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2477_, v_env_2472_, v___x_2478_);
v___x_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; 
lean_dec(v_declName_2474_);
lean_dec_ref(v_env_2472_);
v___x_2481_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_2473_);
return v___x_2481_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_addParserCategory_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2472_ = stack[0].m_obj;
lean_object* v_catName_2473_ = stack[1].m_obj;
lean_object* v_declName_2474_ = stack[2].m_obj;
uint8_t v_behavior_2475_ = stack[3].m_num;
lean_object* v_res_2482_;
v_res_2482_ = l_Lean_Parser_addParserCategory(v_env_2472_, v_catName_2473_, v_declName_2474_, v_behavior_2475_);
stack->m_obj
 = v_res_2482_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* v_env_2483_, lean_object* v_catName_2484_, lean_object* v_declName_2485_, lean_object* v_behavior_2486_){
_start:
{
uint8_t v_behavior_boxed_2487_; lean_object* v_res_2488_; 
v_behavior_boxed_2487_ = lean_unbox(v_behavior_2486_);
v_res_2488_ = l_Lean_Parser_addParserCategory(v_env_2483_, v_catName_2484_, v_declName_2485_, v_behavior_boxed_2487_);
return v_res_2488_;
}
}
uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object* v_env_2489_, lean_object* v_catName_2490_){
_start:
{
lean_object* v___x_2491_; lean_object* v_ext_2492_; lean_object* v_toEnvExtension_2493_; lean_object* v_asyncMode_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; lean_object* v___x_2497_; lean_object* v_categories_2498_; lean_object* v___x_2499_; 
v___x_2491_ = l_Lean_Parser_parserExtension;
v_ext_2492_ = lean_ctor_get(v___x_2491_, 1);
v_toEnvExtension_2493_ = lean_ctor_get(v_ext_2492_, 0);
v_asyncMode_2494_ = lean_ctor_get(v_toEnvExtension_2493_, 2);
v___x_2495_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2496_ = 0;
v___x_2497_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2495_, v___x_2491_, v_env_2489_, v_asyncMode_2494_, v___x_2496_);
v_categories_2498_ = lean_ctor_get(v___x_2497_, 2);
lean_inc_ref(v_categories_2498_);
lean_dec(v___x_2497_);
v___x_2499_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2498_, v_catName_2490_);
lean_dec_ref(v_categories_2498_);
if (lean_obj_tag(v___x_2499_) == 0)
{
uint8_t v___x_2500_; 
v___x_2500_ = 0;
return v___x_2500_;
}
else
{
lean_object* v_val_2501_; uint8_t v_behavior_2502_; 
v_val_2501_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_val_2501_);
lean_dec_ref_known(v___x_2499_, 1);
v_behavior_2502_ = lean_ctor_get_uint8(v_val_2501_, sizeof(void*)*3);
lean_dec(v_val_2501_);
return v_behavior_2502_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_leadingIdentBehavior_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2489_ = stack[0].m_obj;
lean_object* v_catName_2490_ = stack[1].m_obj;
uint8_t v_res_2503_;
v_res_2503_ = l_Lean_Parser_leadingIdentBehavior(v_env_2489_, v_catName_2490_);
stack->m_num = v_res_2503_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object* v_env_2504_, lean_object* v_catName_2505_){
_start:
{
uint8_t v_res_2506_; lean_object* v_r_2507_; 
v_res_2506_ = l_Lean_Parser_leadingIdentBehavior(v_env_2504_, v_catName_2505_);
lean_dec(v_catName_2505_);
v_r_2507_ = lean_box(v_res_2506_);
return v_r_2507_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(lean_object* v_x_2508_, lean_object* v_x_2509_){
_start:
{
if (lean_obj_tag(v_x_2509_) == 0)
{
return v_x_2508_;
}
else
{
lean_object* v_head_2510_; lean_object* v_tail_2511_; lean_object* v___x_2512_; 
v_head_2510_ = lean_ctor_get(v_x_2509_, 0);
lean_inc_n(v_head_2510_, 2);
v_tail_2511_ = lean_ctor_get(v_x_2509_, 1);
lean_inc(v_tail_2511_);
lean_dec_ref_known(v_x_2509_, 2);
v___x_2512_ = l_Lean_Data_Trie_insert___redArg(v_x_2508_, v_head_2510_, v_head_2510_);
lean_dec(v_head_2510_);
v_x_2508_ = v___x_2512_;
v_x_2509_ = v_tail_2511_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__0(lean_object* v_info_2514_, lean_object* v_ctx_2515_){
_start:
{
lean_object* v_toInputContext_2516_; lean_object* v_toParserModuleContext_2517_; lean_object* v_toCacheableParserContext_2518_; lean_object* v_tokens_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2530_; 
v_toInputContext_2516_ = lean_ctor_get(v_ctx_2515_, 0);
v_toParserModuleContext_2517_ = lean_ctor_get(v_ctx_2515_, 1);
v_toCacheableParserContext_2518_ = lean_ctor_get(v_ctx_2515_, 2);
v_tokens_2519_ = lean_ctor_get(v_ctx_2515_, 3);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_ctx_2515_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2521_ = v_ctx_2515_;
v_isShared_2522_ = v_isSharedCheck_2530_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_tokens_2519_);
lean_inc(v_toCacheableParserContext_2518_);
lean_inc(v_toParserModuleContext_2517_);
lean_inc(v_toInputContext_2516_);
lean_dec(v_ctx_2515_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2530_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v_collectTokens_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
v_collectTokens_2523_ = lean_ctor_get(v_info_2514_, 0);
lean_inc_ref(v_collectTokens_2523_);
lean_dec_ref(v_info_2514_);
v___x_2524_ = lean_box(0);
v___x_2525_ = lean_apply_1(v_collectTokens_2523_, v___x_2524_);
v___x_2526_ = l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(v_tokens_2519_, v___x_2525_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 3, v___x_2526_);
v___x_2528_ = v___x_2521_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_toInputContext_2516_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_toParserModuleContext_2517_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v_toCacheableParserContext_2518_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1(lean_object* v_categories_2531_, lean_object* v_declName_2532_, lean_object* v___x_2533_, lean_object* v_ctx_2534_, lean_object* v_s_2535_, lean_object* v_evalFallback_x3f_2536_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Lean_Parser_mkParserOfConstant(v_categories_2531_, v_declName_2532_, v___x_2533_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v_snd_2540_; lean_object* v_info_2541_; lean_object* v_fn_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; 
lean_dec(v_evalFallback_x3f_2536_);
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
v_snd_2540_ = lean_ctor_get(v_a_2539_, 1);
lean_inc(v_snd_2540_);
lean_dec(v_a_2539_);
v_info_2541_ = lean_ctor_get(v_snd_2540_, 0);
lean_inc_ref(v_info_2541_);
v_fn_2542_ = lean_ctor_get(v_snd_2540_, 1);
lean_inc_ref(v_fn_2542_);
lean_dec(v_snd_2540_);
v___f_2543_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__0), 2, 1);
lean_closure_set(v___f_2543_, 0, v_info_2541_);
v___x_2544_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2543_, v_fn_2542_, v_ctx_2534_, v_s_2535_);
return v___x_2544_;
}
else
{
if (lean_obj_tag(v_evalFallback_x3f_2536_) == 1)
{
lean_object* v_val_2545_; lean_object* v___x_2546_; 
lean_dec_ref_known(v___x_2538_, 1);
v_val_2545_ = lean_ctor_get(v_evalFallback_x3f_2536_, 0);
lean_inc(v_val_2545_);
lean_dec_ref_known(v_evalFallback_x3f_2536_, 1);
v___x_2546_ = lean_apply_2(v_val_2545_, v_ctx_2534_, v_s_2535_);
return v___x_2546_;
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; lean_object* v___x_2551_; 
lean_dec(v_evalFallback_x3f_2536_);
lean_dec_ref(v_ctx_2534_);
v_a_2547_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2538_, 1);
v___x_2548_ = lean_io_error_to_string(v_a_2547_);
v___x_2549_ = lean_box(0);
v___x_2550_ = 1;
v___x_2551_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2535_, v___x_2548_, v___x_2549_, v___x_2550_);
return v___x_2551_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_evalParserConstUnsafe___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_categories_2531_ = stack[0].m_obj;
lean_object* v_declName_2532_ = stack[1].m_obj;
lean_object* v___x_2533_ = stack[2].m_obj;
lean_object* v_ctx_2534_ = stack[3].m_obj;
lean_object* v_s_2535_ = stack[4].m_obj;
lean_object* v_evalFallback_x3f_2536_ = stack[5].m_obj;
lean_object* v_res_2552_;
v_res_2552_ = l_Lean_Parser_evalParserConstUnsafe___lam__1(v_categories_2531_, v_declName_2532_, v___x_2533_, v_ctx_2534_, v_s_2535_, v_evalFallback_x3f_2536_);
stack->m_obj
 = v_res_2552_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed(lean_object* v_categories_2553_, lean_object* v_declName_2554_, lean_object* v___x_2555_, lean_object* v_ctx_2556_, lean_object* v_s_2557_, lean_object* v_evalFallback_x3f_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Parser_evalParserConstUnsafe___lam__1(v_categories_2553_, v_declName_2554_, v___x_2555_, v_ctx_2556_, v_s_2557_, v_evalFallback_x3f_2558_);
lean_dec_ref(v___x_2555_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* v_declName_2561_, lean_object* v_evalFallback_x3f_2562_, lean_object* v_ctx_2563_, lean_object* v_s_2564_){
_start:
{
lean_object* v_toParserModuleContext_2565_; lean_object* v_env_2566_; lean_object* v_options_2567_; lean_object* v___x_2568_; lean_object* v_ext_2569_; lean_object* v_toEnvExtension_2570_; lean_object* v_asyncMode_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; lean_object* v_categories_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; lean_object* v___x_2578_; 
v_toParserModuleContext_2565_ = lean_ctor_get(v_ctx_2563_, 1);
v_env_2566_ = lean_ctor_get(v_toParserModuleContext_2565_, 0);
v_options_2567_ = lean_ctor_get(v_toParserModuleContext_2565_, 1);
v___x_2568_ = l_Lean_Parser_parserExtension;
v_ext_2569_ = lean_ctor_get(v___x_2568_, 1);
v_toEnvExtension_2570_ = lean_ctor_get(v_ext_2569_, 0);
v_asyncMode_2571_ = lean_ctor_get(v_toEnvExtension_2570_, 2);
v___x_2572_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2573_ = 0;
lean_inc_ref_n(v_env_2566_, 2);
v___x_2574_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2572_, v___x_2568_, v_env_2566_, v_asyncMode_2571_, v___x_2573_);
v_categories_2575_ = lean_ctor_get(v___x_2574_, 2);
lean_inc_ref(v_categories_2575_);
lean_dec(v___x_2574_);
lean_inc_ref(v_options_2567_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_env_2566_);
lean_ctor_set(v___x_2576_, 1, v_options_2567_);
v___f_2577_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2577_, 0, v_categories_2575_);
lean_closure_set(v___f_2577_, 1, v_declName_2561_);
lean_closure_set(v___f_2577_, 2, v___x_2576_);
lean_closure_set(v___f_2577_, 3, v_ctx_2563_);
lean_closure_set(v___f_2577_, 4, v_s_2564_);
lean_closure_set(v___f_2577_, 5, v_evalFallback_x3f_2562_);
v___x_2578_ = l_unsafeBaseIO___redArg(v___f_2577_);
return v___x_2578_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(lean_object* v_name_2579_, lean_object* v_decl_2580_, lean_object* v_ref_2581_){
_start:
{
lean_object* v_defValue_2583_; lean_object* v_descr_2584_; lean_object* v_deprecation_x3f_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v_defValue_2583_ = lean_ctor_get(v_decl_2580_, 0);
v_descr_2584_ = lean_ctor_get(v_decl_2580_, 1);
v_deprecation_x3f_2585_ = lean_ctor_get(v_decl_2580_, 2);
v___x_2586_ = lean_alloc_ctor(1, 0, 1);
v___x_2587_ = lean_unbox(v_defValue_2583_);
lean_ctor_set_uint8(v___x_2586_, 0, v___x_2587_);
lean_inc(v_deprecation_x3f_2585_);
lean_inc_ref(v_descr_2584_);
lean_inc_n(v_name_2579_, 2);
v___x_2588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2588_, 0, v_name_2579_);
lean_ctor_set(v___x_2588_, 1, v_ref_2581_);
lean_ctor_set(v___x_2588_, 2, v___x_2586_);
lean_ctor_set(v___x_2588_, 3, v_descr_2584_);
lean_ctor_set(v___x_2588_, 4, v_deprecation_x3f_2585_);
v___x_2589_ = lean_register_option(v_name_2579_, v___x_2588_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2597_; 
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v___x_2589_, 0);
lean_dec(v_unused_2598_);
v___x_2591_ = v___x_2589_;
v_isShared_2592_ = v_isSharedCheck_2597_;
goto v_resetjp_2590_;
}
else
{
lean_dec(v___x_2589_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2597_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
lean_inc(v_defValue_2583_);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v_name_2579_);
lean_ctor_set(v___x_2593_, 1, v_defValue_2583_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2593_);
v___x_2595_ = v___x_2591_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v_name_2579_);
v_a_2599_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2589_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2589_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2579_ = stack[0].m_obj;
lean_object* v_decl_2580_ = stack[1].m_obj;
lean_object* v_ref_2581_ = stack[2].m_obj;
lean_object* v_res_2607_;
v_res_2607_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v_name_2579_, v_decl_2580_, v_ref_2581_);
stack->m_obj
 = v_res_2607_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_2608_, lean_object* v_decl_2609_, lean_object* v_ref_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v_name_2608_, v_decl_2609_, v_ref_2610_);
lean_dec_ref(v_decl_2609_);
return v_res_2612_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2630_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2631_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2632_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_));
v___x_2633_ = l_Lean_Option_register___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__spec__0(v___x_2630_, v___x_2631_, v___x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2634_;
v_res_2634_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
stack->m_obj
 = v_res_2634_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4____boxed(lean_object* v_a_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_4243742150____hygCtx___hyg_4_();
return v_res_2636_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(lean_object* v_o_2640_, lean_object* v_k_2641_, uint8_t v_v_2642_){
_start:
{
lean_object* v_map_2643_; uint8_t v_hasTrace_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2658_; 
v_map_2643_ = lean_ctor_get(v_o_2640_, 0);
v_hasTrace_2644_ = lean_ctor_get_uint8(v_o_2640_, sizeof(void*)*1);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_o_2640_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2646_ = v_o_2640_;
v_isShared_2647_ = v_isSharedCheck_2658_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_map_2643_);
lean_dec(v_o_2640_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2658_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2648_, 0, v_v_2642_);
lean_inc(v_k_2641_);
v___x_2649_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2641_, v___x_2648_, v_map_2643_);
if (v_hasTrace_2644_ == 0)
{
lean_object* v___x_2650_; uint8_t v___x_2651_; lean_object* v___x_2653_; 
v___x_2650_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_2651_ = l_Lean_Name_isPrefixOf(v___x_2650_, v_k_2641_);
lean_dec(v_k_2641_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2649_);
v___x_2653_ = v___x_2646_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2649_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_ctor_set_uint8(v___x_2653_, sizeof(void*)*1, v___x_2651_);
return v___x_2653_;
}
}
else
{
lean_object* v___x_2656_; 
lean_dec(v_k_2641_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2649_);
v___x_2656_ = v___x_2646_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, sizeof(void*)*1, v_hasTrace_2644_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_2640_ = stack[0].m_obj;
lean_object* v_k_2641_ = stack[1].m_obj;
uint8_t v_v_2642_ = stack[2].m_num;
lean_object* v_res_2659_;
v_res_2659_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_o_2640_, v_k_2641_, v_v_2642_);
stack->m_obj
 = v_res_2659_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___boxed(lean_object* v_o_2660_, lean_object* v_k_2661_, lean_object* v_v_2662_){
_start:
{
uint8_t v_v_boxed_2663_; lean_object* v_res_2664_; 
v_v_boxed_2663_ = lean_unbox(v_v_2662_);
v_res_2664_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_o_2660_, v_k_2661_, v_v_boxed_2663_);
return v_res_2664_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(lean_object* v_opts_2665_, lean_object* v_opt_2666_){
_start:
{
lean_object* v_name_2667_; lean_object* v_defValue_2668_; lean_object* v_map_2669_; lean_object* v___x_2670_; 
v_name_2667_ = lean_ctor_get(v_opt_2666_, 0);
v_defValue_2668_ = lean_ctor_get(v_opt_2666_, 1);
v_map_2669_ = lean_ctor_get(v_opts_2665_, 0);
v___x_2670_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2669_, v_name_2667_);
if (lean_obj_tag(v___x_2670_) == 0)
{
uint8_t v___x_2671_; 
v___x_2671_ = lean_unbox(v_defValue_2668_);
return v___x_2671_;
}
else
{
lean_object* v_val_2672_; 
v_val_2672_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_val_2672_);
lean_dec_ref_known(v___x_2670_, 1);
if (lean_obj_tag(v_val_2672_) == 1)
{
uint8_t v_v_2673_; 
v_v_2673_ = lean_ctor_get_uint8(v_val_2672_, 0);
lean_dec_ref_known(v_val_2672_, 0);
return v_v_2673_;
}
else
{
uint8_t v___x_2674_; 
lean_dec(v_val_2672_);
v___x_2674_ = lean_unbox(v_defValue_2668_);
return v___x_2674_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2665_ = stack[0].m_obj;
lean_object* v_opt_2666_ = stack[1].m_obj;
uint8_t v_res_2675_;
v_res_2675_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_opts_2665_, v_opt_2666_);
stack->m_num = v_res_2675_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1___boxed(lean_object* v_opts_2676_, lean_object* v_opt_2677_){
_start:
{
uint8_t v_res_2678_; lean_object* v_r_2679_; 
v_res_2678_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_opts_2676_, v_opt_2677_);
lean_dec_ref(v_opt_2677_);
lean_dec_ref(v_opts_2676_);
v_r_2679_ = lean_box(v_res_2678_);
return v_r_2679_;
}
}
lean_object* l_Lean_Parser_evalInsideQuot___lam__0(uint8_t v_suppressInsideQuot_2685_, lean_object* v_ctx_2686_){
_start:
{
lean_object* v_toParserModuleContext_2687_; lean_object* v_toInputContext_2688_; lean_object* v_toCacheableParserContext_2689_; lean_object* v_tokens_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2710_; 
v_toParserModuleContext_2687_ = lean_ctor_get(v_ctx_2686_, 1);
v_toInputContext_2688_ = lean_ctor_get(v_ctx_2686_, 0);
v_toCacheableParserContext_2689_ = lean_ctor_get(v_ctx_2686_, 2);
v_tokens_2690_ = lean_ctor_get(v_ctx_2686_, 3);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_ctx_2686_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2692_ = v_ctx_2686_;
v_isShared_2693_ = v_isSharedCheck_2710_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_tokens_2690_);
lean_inc(v_toCacheableParserContext_2689_);
lean_inc(v_toParserModuleContext_2687_);
lean_inc(v_toInputContext_2688_);
lean_dec(v_ctx_2686_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2710_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v_env_2694_; lean_object* v_options_2695_; lean_object* v_currNamespace_2696_; lean_object* v_openDecls_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2709_; 
v_env_2694_ = lean_ctor_get(v_toParserModuleContext_2687_, 0);
v_options_2695_ = lean_ctor_get(v_toParserModuleContext_2687_, 1);
v_currNamespace_2696_ = lean_ctor_get(v_toParserModuleContext_2687_, 2);
v_openDecls_2697_ = lean_ctor_get(v_toParserModuleContext_2687_, 3);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_toParserModuleContext_2687_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2699_ = v_toParserModuleContext_2687_;
v_isShared_2700_ = v_isSharedCheck_2709_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_openDecls_2697_);
lean_inc(v_currNamespace_2696_);
lean_inc(v_options_2695_);
lean_inc(v_env_2694_);
lean_dec(v_toParserModuleContext_2687_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2709_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2701_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_2702_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_2695_, v___x_2701_, v_suppressInsideQuot_2685_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v___x_2702_);
v___x_2704_ = v___x_2699_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_env_2694_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_currNamespace_2696_);
lean_ctor_set(v_reuseFailAlloc_2708_, 3, v_openDecls_2697_);
v___x_2704_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 1, v___x_2704_);
v___x_2706_ = v___x_2692_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_toInputContext_2688_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_toCacheableParserContext_2689_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_tokens_2690_);
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
}
LEAN_EXPORT void l_Lean_Parser_evalInsideQuot___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressInsideQuot_2685_ = stack[0].m_num;
lean_object* v_ctx_2686_ = stack[1].m_obj;
lean_object* v_res_2711_;
v_res_2711_ = l_Lean_Parser_evalInsideQuot___lam__0(v_suppressInsideQuot_2685_, v_ctx_2686_);
stack->m_obj
 = v_res_2711_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__0___boxed(lean_object* v_suppressInsideQuot_2712_, lean_object* v_ctx_2713_){
_start:
{
uint8_t v_suppressInsideQuot_boxed_2714_; lean_object* v_res_2715_; 
v_suppressInsideQuot_boxed_2714_ = lean_unbox(v_suppressInsideQuot_2712_);
v_res_2715_ = l_Lean_Parser_evalInsideQuot___lam__0(v_suppressInsideQuot_boxed_2714_, v_ctx_2713_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot___lam__1(lean_object* v_fn_2716_, lean_object* v_declName_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_toCacheableParserContext_2720_; lean_object* v_toParserModuleContext_2721_; lean_object* v_quotDepth_2722_; uint8_t v_suppressInsideQuot_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v_toCacheableParserContext_2720_ = lean_ctor_get(v___y_2718_, 2);
v_toParserModuleContext_2721_ = lean_ctor_get(v___y_2718_, 1);
v_quotDepth_2722_ = lean_ctor_get(v_toCacheableParserContext_2720_, 1);
v_suppressInsideQuot_2723_ = lean_ctor_get_uint8(v_toCacheableParserContext_2720_, sizeof(void*)*4);
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = lean_nat_dec_lt(v___x_2724_, v_quotDepth_2722_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; 
lean_dec(v_declName_2717_);
v___x_2726_ = lean_apply_2(v_fn_2716_, v___y_2718_, v___y_2719_);
return v___x_2726_;
}
else
{
if (v_suppressInsideQuot_2723_ == 0)
{
lean_object* v_env_2727_; lean_object* v_options_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v_env_2727_ = lean_ctor_get(v_toParserModuleContext_2721_, 0);
v_options_2728_ = lean_ctor_get(v_toParserModuleContext_2721_, 1);
v___x_2729_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_2730_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_2728_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
lean_dec(v_declName_2717_);
v___x_2731_ = lean_apply_2(v_fn_2716_, v___y_2718_, v___y_2719_);
return v___x_2731_;
}
else
{
uint8_t v___x_2732_; 
lean_inc(v_declName_2717_);
lean_inc_ref(v_env_2727_);
v___x_2732_ = l_Lean_Environment_contains(v_env_2727_, v_declName_2717_, v___x_2730_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; 
lean_dec(v_declName_2717_);
v___x_2733_ = lean_apply_2(v_fn_2716_, v___y_2718_, v___y_2719_);
return v___x_2733_;
}
else
{
lean_object* v___x_2734_; lean_object* v___f_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2734_ = lean_box(v_suppressInsideQuot_2723_);
v___f_2735_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2735_, 0, v___x_2734_);
v___x_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2736_, 0, v_fn_2716_);
v___x_2737_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_2737_, 0, v_declName_2717_);
lean_closure_set(v___x_2737_, 1, v___x_2736_);
v___x_2738_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2735_, v___x_2737_, v___y_2718_, v___y_2719_);
return v___x_2738_;
}
}
}
else
{
lean_object* v___x_2739_; 
lean_dec(v_declName_2717_);
v___x_2739_ = lean_apply_2(v_fn_2716_, v___y_2718_, v___y_2719_);
return v___x_2739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalInsideQuot(lean_object* v_declName_2740_, lean_object* v_p_2741_){
_start:
{
lean_object* v_info_2742_; lean_object* v_fn_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2751_; 
v_info_2742_ = lean_ctor_get(v_p_2741_, 0);
v_fn_2743_ = lean_ctor_get(v_p_2741_, 1);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_p_2741_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2745_ = v_p_2741_;
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_fn_2743_);
lean_inc(v_info_2742_);
lean_dec(v_p_2741_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___f_2747_; lean_object* v___x_2749_; 
v___f_2747_ = lean_alloc_closure((void*)(l_Lean_Parser_evalInsideQuot___lam__1), 4, 2);
lean_closure_set(v___f_2747_, 0, v_fn_2743_);
lean_closure_set(v___f_2747_, 1, v_declName_2740_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 1, v___f_2747_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_info_2742_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v___f_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
lean_object* l_Lean_Parser_addBuiltinParser(lean_object* v_catName_2752_, lean_object* v_declName_2753_, uint8_t v_leading_2754_, lean_object* v_p_2755_, lean_object* v_prio_2756_){
_start:
{
lean_object* v_p_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_inc_n(v_declName_2753_, 2);
v_p_2758_ = l_Lean_Parser_evalInsideQuot(v_declName_2753_, v_p_2755_);
v___x_2759_ = l_Lean_Parser_builtinParserCategoriesRef;
v___x_2760_ = lean_st_ref_get(v___x_2759_);
lean_inc_ref(v_p_2758_);
v___x_2761_ = l_Lean_Parser_addParser(v___x_2760_, v_catName_2752_, v_declName_2753_, v_leading_2754_, v_p_2758_, v_prio_2756_);
v___x_2762_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_2761_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; lean_object* v_info_2765_; lean_object* v_collectKinds_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2764_ = lean_st_ref_swap(v___x_2759_, v_a_2763_);
lean_dec(v___x_2764_);
v_info_2765_ = lean_ctor_get(v_p_2758_, 0);
lean_inc_ref(v_info_2765_);
lean_dec_ref(v_p_2758_);
v_collectKinds_2766_ = lean_ctor_get(v_info_2765_, 1);
v___x_2767_ = l_Lean_Parser_builtinSyntaxNodeKindSetRef;
v___x_2768_ = lean_st_ref_take(v___x_2767_);
lean_inc_ref(v_collectKinds_2766_);
v___x_2769_ = lean_apply_1(v_collectKinds_2766_, v___x_2768_);
v___x_2770_ = lean_st_ref_put(v___x_2767_, v___x_2769_);
v___x_2771_ = l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens(v_info_2765_, v_declName_2753_);
return v___x_2771_;
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec_ref(v_p_2758_);
lean_dec(v_declName_2753_);
v_a_2772_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2762_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2762_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_addBuiltinParser_0interp(lean_interpreter_value* stack)
{
lean_object* v_catName_2752_ = stack[0].m_obj;
lean_object* v_declName_2753_ = stack[1].m_obj;
uint8_t v_leading_2754_ = stack[2].m_num;
lean_object* v_p_2755_ = stack[3].m_obj;
lean_object* v_prio_2756_ = stack[4].m_obj;
lean_object* v_res_2780_;
v_res_2780_ = l_Lean_Parser_addBuiltinParser(v_catName_2752_, v_declName_2753_, v_leading_2754_, v_p_2755_, v_prio_2756_);
stack->m_obj
 = v_res_2780_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinParser___boxed(lean_object* v_catName_2781_, lean_object* v_declName_2782_, lean_object* v_leading_2783_, lean_object* v_p_2784_, lean_object* v_prio_2785_, lean_object* v_a_2786_){
_start:
{
uint8_t v_leading_boxed_2787_; lean_object* v_res_2788_; 
v_leading_boxed_2787_ = lean_unbox(v_leading_2783_);
v_res_2788_ = l_Lean_Parser_addBuiltinParser(v_catName_2781_, v_declName_2782_, v_leading_boxed_2787_, v_p_2784_, v_prio_2785_);
return v_res_2788_;
}
}
lean_object* l_Lean_Parser_addBuiltinLeadingParser(lean_object* v_catName_2789_, lean_object* v_declName_2790_, lean_object* v_p_2791_, lean_object* v_prio_2792_){
_start:
{
uint8_t v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = 1;
v___x_2795_ = l_Lean_Parser_addBuiltinParser(v_catName_2789_, v_declName_2790_, v___x_2794_, v_p_2791_, v_prio_2792_);
return v___x_2795_;
}
}
LEAN_EXPORT void l_Lean_Parser_addBuiltinLeadingParser_0interp(lean_interpreter_value* stack)
{
lean_object* v_catName_2789_ = stack[0].m_obj;
lean_object* v_declName_2790_ = stack[1].m_obj;
lean_object* v_p_2791_ = stack[2].m_obj;
lean_object* v_prio_2792_ = stack[3].m_obj;
lean_object* v_res_2796_;
v_res_2796_ = l_Lean_Parser_addBuiltinLeadingParser(v_catName_2789_, v_declName_2790_, v_p_2791_, v_prio_2792_);
stack->m_obj
 = v_res_2796_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinLeadingParser___boxed(lean_object* v_catName_2797_, lean_object* v_declName_2798_, lean_object* v_p_2799_, lean_object* v_prio_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Parser_addBuiltinLeadingParser(v_catName_2797_, v_declName_2798_, v_p_2799_, v_prio_2800_);
return v_res_2802_;
}
}
lean_object* l_Lean_Parser_addBuiltinTrailingParser(lean_object* v_catName_2803_, lean_object* v_declName_2804_, lean_object* v_p_2805_, lean_object* v_prio_2806_){
_start:
{
uint8_t v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = 0;
v___x_2809_ = l_Lean_Parser_addBuiltinParser(v_catName_2803_, v_declName_2804_, v___x_2808_, v_p_2805_, v_prio_2806_);
return v___x_2809_;
}
}
LEAN_EXPORT void l_Lean_Parser_addBuiltinTrailingParser_0interp(lean_interpreter_value* stack)
{
lean_object* v_catName_2803_ = stack[0].m_obj;
lean_object* v_declName_2804_ = stack[1].m_obj;
lean_object* v_p_2805_ = stack[2].m_obj;
lean_object* v_prio_2806_ = stack[3].m_obj;
lean_object* v_res_2810_;
v_res_2810_ = l_Lean_Parser_addBuiltinTrailingParser(v_catName_2803_, v_declName_2804_, v_p_2805_, v_prio_2806_);
stack->m_obj
 = v_res_2810_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_addBuiltinTrailingParser___boxed(lean_object* v_catName_2811_, lean_object* v_declName_2812_, lean_object* v_p_2813_, lean_object* v_prio_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_Parser_addBuiltinTrailingParser(v_catName_2811_, v_declName_2812_, v_p_2813_, v_prio_2814_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkCategoryAntiquotParser(lean_object* v_kind_2817_){
_start:
{
uint8_t v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2818_ = 1;
lean_inc(v_kind_2817_);
v___x_2819_ = l_Lean_Name_toString(v_kind_2817_, v___x_2818_);
v___x_2820_ = l_Lean_Parser_mkAntiquot(v___x_2819_, v_kind_2817_, v___x_2818_, v___x_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_mkCategoryAntiquotParserFn(lean_object* v_kind_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v___x_2824_; lean_object* v_fn_2825_; lean_object* v___x_2826_; 
v___x_2824_ = l_Lean_Parser_mkCategoryAntiquotParser(v_kind_2821_);
v_fn_2825_ = lean_ctor_get(v___x_2824_, 1);
lean_inc_ref(v_fn_2825_);
lean_dec_ref(v___x_2824_);
v___x_2826_ = lean_apply_2(v_fn_2825_, v_a_2822_, v_a_2823_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl___lam__0(lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2830_; lean_object* v_fn_2831_; lean_object* v___x_2832_; 
v___x_2830_ = l_Lean_Parser_mkCategoryAntiquotParser(v___y_2827_);
v_fn_2831_ = lean_ctor_get(v___x_2830_, 1);
lean_inc_ref(v_fn_2831_);
lean_dec_ref(v___x_2830_);
v___x_2832_ = lean_apply_2(v_fn_2831_, v___y_2828_, v___y_2829_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFnImpl(lean_object* v_catName_2841_, lean_object* v_ctx_2842_, lean_object* v_s_2843_){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; uint8_t v___x_2847_; lean_object* v___y_2849_; 
v___x_2844_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2845_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__1));
v___x_2846_ = lean_name_eq(v_catName_2841_, v___x_2845_);
v___x_2847_ = 1;
if (v___x_2846_ == 0)
{
v___y_2849_ = v_catName_2841_;
goto v___jp_2848_;
}
else
{
lean_object* v___x_2872_; 
lean_dec(v_catName_2841_);
v___x_2872_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__5));
v___y_2849_ = v___x_2872_;
goto v___jp_2848_;
}
v___jp_2848_:
{
lean_object* v_toParserModuleContext_2850_; lean_object* v_env_2851_; lean_object* v___x_2852_; lean_object* v_ext_2853_; lean_object* v_toEnvExtension_2854_; lean_object* v_asyncMode_2855_; uint8_t v___x_2856_; lean_object* v___x_2857_; lean_object* v_categories_2858_; lean_object* v___x_2859_; 
v_toParserModuleContext_2850_ = lean_ctor_get(v_ctx_2842_, 1);
v_env_2851_ = lean_ctor_get(v_toParserModuleContext_2850_, 0);
v___x_2852_ = l_Lean_Parser_parserExtension;
v_ext_2853_ = lean_ctor_get(v___x_2852_, 1);
v_toEnvExtension_2854_ = lean_ctor_get(v_ext_2853_, 0);
v_asyncMode_2855_ = lean_ctor_get(v_toEnvExtension_2854_, 2);
v___x_2856_ = 0;
lean_inc_ref(v_env_2851_);
v___x_2857_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2844_, v___x_2852_, v_env_2851_, v_asyncMode_2855_, v___x_2856_);
v_categories_2858_ = lean_ctor_get(v___x_2857_, 2);
lean_inc_ref(v_categories_2858_);
lean_dec(v___x_2857_);
v___x_2859_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2858_, v___y_2849_);
lean_dec_ref(v_categories_2858_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
lean_dec_ref(v_ctx_2842_);
v___x_2860_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__2));
v___x_2861_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2849_, v___x_2847_);
v___x_2862_ = lean_string_append(v___x_2860_, v___x_2861_);
lean_dec_ref(v___x_2861_);
v___x_2863_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__3));
v___x_2864_ = lean_string_append(v___x_2862_, v___x_2863_);
v___x_2865_ = lean_box(0);
v___x_2866_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2843_, v___x_2864_, v___x_2865_, v___x_2847_);
return v___x_2866_;
}
else
{
lean_object* v_val_2867_; lean_object* v_tables_2868_; uint8_t v_behavior_2869_; lean_object* v___f_2870_; lean_object* v___x_2871_; 
v_val_2867_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_val_2867_);
lean_dec_ref_known(v___x_2859_, 1);
v_tables_2868_ = lean_ctor_get(v_val_2867_, 2);
lean_inc_ref(v_tables_2868_);
v_behavior_2869_ = lean_ctor_get_uint8(v_val_2867_, sizeof(void*)*3);
lean_dec(v_val_2867_);
lean_inc(v___y_2849_);
v___f_2870_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl___lam__0), 3, 1);
lean_closure_set(v___f_2870_, 0, v___y_2849_);
v___x_2871_ = l_Lean_Parser_prattParser(v___y_2849_, v_tables_2868_, v_behavior_2869_, v___f_2870_, v_ctx_2842_, v_s_2843_);
return v___x_2871_;
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2875_ = l_Lean_Parser_categoryParserFnRef;
v___x_2876_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_));
v___x_2877_ = lean_box(0);
v___x_2878_ = lean_st_ref_swap(v___x_2875_, v___x_2876_);
lean_dec(v___x_2878_);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
return v___x_2879_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2880_;
v_res_2880_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2880_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object* v_a_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
return v_res_2882_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0);
v___x_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
return v___x_2886_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object* v_ext_2887_, lean_object* v_b_2888_, uint8_t v_kind_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_toCold_2893_; lean_object* v_currNamespace_2894_; lean_object* v___x_2895_; lean_object* v_env_2896_; lean_object* v_nextMacroScope_2897_; lean_object* v_ngen_2898_; lean_object* v_auxDeclNGen_2899_; lean_object* v_traceState_2900_; lean_object* v_recordedDeps_2901_; lean_object* v_messages_2902_; lean_object* v_infoState_2903_; lean_object* v_snapshotTasks_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2916_; 
v_toCold_2893_ = lean_ctor_get(v___y_2890_, 0);
v_currNamespace_2894_ = lean_ctor_get(v_toCold_2893_, 4);
v___x_2895_ = lean_st_ref_take(v___y_2891_);
v_env_2896_ = lean_ctor_get(v___x_2895_, 0);
v_nextMacroScope_2897_ = lean_ctor_get(v___x_2895_, 1);
v_ngen_2898_ = lean_ctor_get(v___x_2895_, 2);
v_auxDeclNGen_2899_ = lean_ctor_get(v___x_2895_, 3);
v_traceState_2900_ = lean_ctor_get(v___x_2895_, 4);
v_recordedDeps_2901_ = lean_ctor_get(v___x_2895_, 6);
v_messages_2902_ = lean_ctor_get(v___x_2895_, 7);
v_infoState_2903_ = lean_ctor_get(v___x_2895_, 8);
v_snapshotTasks_2904_ = lean_ctor_get(v___x_2895_, 9);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; 
v_unused_2917_ = lean_ctor_get(v___x_2895_, 5);
lean_dec(v_unused_2917_);
v___x_2906_ = v___x_2895_;
v_isShared_2907_ = v_isSharedCheck_2916_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_snapshotTasks_2904_);
lean_inc(v_infoState_2903_);
lean_inc(v_messages_2902_);
lean_inc(v_recordedDeps_2901_);
lean_inc(v_traceState_2900_);
lean_inc(v_auxDeclNGen_2899_);
lean_inc(v_ngen_2898_);
lean_inc(v_nextMacroScope_2897_);
lean_inc(v_env_2896_);
lean_dec(v___x_2895_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2916_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2908_ = lean_box(0);
lean_inc(v_currNamespace_2894_);
v___x_2909_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2896_, v_ext_2887_, v_b_2888_, v_kind_2889_, v_currNamespace_2894_);
v___x_2910_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 5, v___x_2910_);
lean_ctor_set(v___x_2906_, 0, v___x_2909_);
v___x_2912_ = v___x_2906_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_nextMacroScope_2897_);
lean_ctor_set(v_reuseFailAlloc_2915_, 2, v_ngen_2898_);
lean_ctor_set(v_reuseFailAlloc_2915_, 3, v_auxDeclNGen_2899_);
lean_ctor_set(v_reuseFailAlloc_2915_, 4, v_traceState_2900_);
lean_ctor_set(v_reuseFailAlloc_2915_, 5, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2915_, 6, v_recordedDeps_2901_);
lean_ctor_set(v_reuseFailAlloc_2915_, 7, v_messages_2902_);
lean_ctor_set(v_reuseFailAlloc_2915_, 8, v_infoState_2903_);
lean_ctor_set(v_reuseFailAlloc_2915_, 9, v_snapshotTasks_2904_);
v___x_2912_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_st_ref_put(v___y_2891_, v___x_2912_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2908_);
return v___x_2914_;
}
}
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2887_ = stack[0].m_obj;
lean_object* v_b_2888_ = stack[1].m_obj;
uint8_t v_kind_2889_ = stack[2].m_num;
lean_object* v___y_2890_ = stack[3].m_obj;
lean_object* v___y_2891_ = stack[4].m_obj;
lean_object* v_res_2918_;
v_res_2918_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2887_, v_b_2888_, v_kind_2889_, v___y_2890_, v___y_2891_);
stack->m_obj
 = v_res_2918_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object* v_ext_2919_, lean_object* v_b_2920_, lean_object* v_kind_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
uint8_t v_kind_boxed_2925_; lean_object* v_res_2926_; 
v_kind_boxed_2925_ = lean_unbox(v_kind_2921_);
v_res_2926_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2919_, v_b_2920_, v_kind_boxed_2925_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
return v_res_2926_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object* v_00_u03b1_2927_, lean_object* v_00_u03b2_2928_, lean_object* v_00_u03c3_2929_, lean_object* v_ext_2930_, lean_object* v_b_2931_, uint8_t v_kind_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2930_, v_b_2931_, v_kind_2932_, v___y_2933_, v___y_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2930_ = stack[3].m_obj;
lean_object* v_b_2931_ = stack[4].m_obj;
uint8_t v_kind_2932_ = stack[5].m_num;
lean_object* v___y_2933_ = stack[6].m_obj;
lean_object* v___y_2934_ = stack[7].m_obj;
lean_object* v_res_2937_;
v_res_2937_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_box(0), lean_box(0), lean_box(0), v_ext_2930_, v_b_2931_, v_kind_2932_, v___y_2933_, v___y_2934_);
stack->m_obj
 = v_res_2937_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object* v_00_u03b1_2938_, lean_object* v_00_u03b2_2939_, lean_object* v_00_u03c3_2940_, lean_object* v_ext_2941_, lean_object* v_b_2942_, lean_object* v_kind_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v_kind_boxed_2947_; lean_object* v_res_2948_; 
v_kind_boxed_2947_ = lean_unbox(v_kind_2943_);
v_res_2948_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(v_00_u03b1_2938_, v_00_u03b2_2939_, v_00_u03c3_2940_, v_ext_2941_, v_b_2942_, v_kind_boxed_2947_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
return v_res_2948_;
}
}
lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object* v_x_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
if (lean_obj_tag(v_x_2949_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_a_2953_ = lean_ctor_get(v_x_2949_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v_x_2949_, 1);
v___x_2954_ = l_Lean_stringToMessageData(v_a_2953_);
v___x_2955_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2954_, v___y_2950_, v___y_2951_);
return v___x_2955_;
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
v_a_2956_ = lean_ctor_get(v_x_2949_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_x_2949_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v_x_2949_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v_x_2949_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
lean_ctor_set_tag(v___x_2958_, 0);
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2949_ = stack[0].m_obj;
lean_object* v___y_2950_ = stack[1].m_obj;
lean_object* v___y_2951_ = stack[2].m_obj;
lean_object* v_res_2964_;
v_res_2964_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2949_, v___y_2950_, v___y_2951_);
stack->m_obj
 = v_res_2964_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object* v_x_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
return v_res_2969_;
}
}
lean_object* l_Lean_Parser_addToken(lean_object* v_tk_2970_, uint8_t v_kind_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v_env_2977_; lean_object* v___x_2978_; lean_object* v_ext_2979_; lean_object* v_toEnvExtension_2980_; lean_object* v_asyncMode_2981_; uint8_t v___x_2982_; lean_object* v___x_2983_; lean_object* v_tokens_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2975_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2976_ = lean_st_ref_get(v_a_2973_);
v_env_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc_ref(v_env_2977_);
lean_dec(v___x_2976_);
v___x_2978_ = l_Lean_Parser_parserExtension;
v_ext_2979_ = lean_ctor_get(v___x_2978_, 1);
v_toEnvExtension_2980_ = lean_ctor_get(v_ext_2979_, 0);
v_asyncMode_2981_ = lean_ctor_get(v_toEnvExtension_2980_, 2);
v___x_2982_ = 0;
v___x_2983_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2975_, v___x_2978_, v_env_2977_, v_asyncMode_2981_, v___x_2982_);
v_tokens_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc_ref(v_tokens_2984_);
lean_dec(v___x_2983_);
lean_inc_ref(v_tk_2970_);
v___x_2985_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_2984_, v_tk_2970_);
v___x_2986_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v___x_2985_, v_a_2972_, v_a_2973_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
lean_dec_ref_known(v___x_2986_, 1);
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v_tk_2970_);
v___x_2988_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_2978_, v___x_2987_, v_kind_2971_, v_a_2972_, v_a_2973_);
return v___x_2988_;
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v_tk_2970_);
v_a_2989_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2986_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2986_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_addToken_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_2970_ = stack[0].m_obj;
uint8_t v_kind_2971_ = stack[1].m_num;
lean_object* v_a_2972_ = stack[2].m_obj;
lean_object* v_a_2973_ = stack[3].m_obj;
lean_object* v_res_2997_;
v_res_2997_ = l_Lean_Parser_addToken(v_tk_2970_, v_kind_2971_, v_a_2972_, v_a_2973_);
stack->m_obj
 = v_res_2997_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken___boxed(lean_object* v_tk_2998_, lean_object* v_kind_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_){
_start:
{
uint8_t v_kind_boxed_3003_; lean_object* v_res_3004_; 
v_kind_boxed_3003_ = lean_unbox(v_kind_2999_);
v_res_3004_ = l_Lean_Parser_addToken(v_tk_2998_, v_kind_boxed_3003_, v_a_3000_, v_a_3001_);
lean_dec(v_a_3001_);
lean_dec_ref(v_a_3000_);
return v_res_3004_;
}
}
lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_object* v_00_u03b1_3005_, lean_object* v_x_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_3006_, v___y_3007_, v___y_3008_);
return v___x_3010_;
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3006_ = stack[1].m_obj;
lean_object* v___y_3007_ = stack[2].m_obj;
lean_object* v___y_3008_ = stack[3].m_obj;
lean_object* v_res_3011_;
v_res_3011_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(lean_box(0), v_x_3006_, v___y_3007_, v___y_3008_);
stack->m_obj
 = v_res_3011_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___boxed(lean_object* v_00_u03b1_3012_, lean_object* v_x_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0(v_00_u03b1_3012_, v_x_3013_, v___y_3014_, v___y_3015_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addSyntaxNodeKind(lean_object* v_env_3018_, lean_object* v_k_3019_){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = l_Lean_Parser_parserExtension;
v___x_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_k_3019_);
v___x_3022_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_3020_, v_env_3018_, v___x_3021_);
return v___x_3022_;
}
}
static uint8_t _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0(void){
_start:
{
lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3023_ = lean_box(0);
v___x_3024_ = lean_internal_is_stage0(v___x_3023_);
return v___x_3024_;
}
}
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object* v_env_3025_, lean_object* v_k_3026_){
_start:
{
lean_object* v___x_3027_; lean_object* v_ext_3028_; lean_object* v_toEnvExtension_3029_; lean_object* v_asyncMode_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v_kinds_3034_; uint8_t v___x_3035_; 
v___x_3027_ = l_Lean_Parser_parserExtension;
v_ext_3028_ = lean_ctor_get(v___x_3027_, 1);
v_toEnvExtension_3029_ = lean_ctor_get(v_ext_3028_, 0);
v_asyncMode_3030_ = lean_ctor_get(v_toEnvExtension_3029_, 2);
v___x_3031_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3032_ = 0;
lean_inc_ref(v_env_3025_);
v___x_3033_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3031_, v___x_3027_, v_env_3025_, v_asyncMode_3030_, v___x_3032_);
v_kinds_3034_ = lean_ctor_get(v___x_3033_, 1);
lean_inc_ref(v_kinds_3034_);
lean_dec(v___x_3033_);
v___x_3035_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_3034_, v_k_3026_);
lean_dec_ref(v_kinds_3034_);
if (v___x_3035_ == 0)
{
uint8_t v___x_3036_; 
v___x_3036_ = lean_uint8_once(&l_Lean_Parser_isValidSyntaxNodeKind___closed__0, &l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once, _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0);
if (v___x_3036_ == 0)
{
lean_dec(v_k_3026_);
lean_dec_ref(v_env_3025_);
return v___x_3032_;
}
else
{
uint8_t v___x_3037_; 
v___x_3037_ = l_Lean_Environment_contains(v_env_3025_, v_k_3026_, v___x_3036_);
return v___x_3037_;
}
}
else
{
lean_dec(v_k_3026_);
lean_dec_ref(v_env_3025_);
return v___x_3035_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_isValidSyntaxNodeKind_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3025_ = stack[0].m_obj;
lean_object* v_k_3026_ = stack[1].m_obj;
uint8_t v_res_3038_;
v_res_3038_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_3025_, v_k_3026_);
stack->m_num = v_res_3038_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_isValidSyntaxNodeKind___boxed(lean_object* v_env_3039_, lean_object* v_k_3040_){
_start:
{
uint8_t v_res_3041_; lean_object* v_r_3042_; 
v_res_3041_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_3039_, v_k_3040_);
v_r_3042_ = lean_box(v_res_3041_);
return v_r_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds___lam__0(lean_object* v_ks_3043_, lean_object* v_k_3044_, lean_object* v_x_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3046_, 0, v_k_3044_);
lean_ctor_set(v___x_3046_, 1, v_ks_3043_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3047_, lean_object* v_keys_3048_, lean_object* v_vals_3049_, lean_object* v_i_3050_, lean_object* v_acc_3051_){
_start:
{
lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = lean_array_get_size(v_keys_3048_);
v___x_3053_ = lean_nat_dec_lt(v_i_3050_, v___x_3052_);
if (v___x_3053_ == 0)
{
lean_dec(v_i_3050_);
lean_dec(v_f_3047_);
return v_acc_3051_;
}
else
{
lean_object* v_k_3054_; lean_object* v_v_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_k_3054_ = lean_array_fget_borrowed(v_keys_3048_, v_i_3050_);
v_v_3055_ = lean_array_fget_borrowed(v_vals_3049_, v_i_3050_);
lean_inc(v_f_3047_);
lean_inc(v_v_3055_);
lean_inc(v_k_3054_);
v___x_3056_ = lean_apply_3(v_f_3047_, v_acc_3051_, v_k_3054_, v_v_3055_);
v___x_3057_ = lean_unsigned_to_nat(1u);
v___x_3058_ = lean_nat_add(v_i_3050_, v___x_3057_);
lean_dec(v_i_3050_);
v_i_3050_ = v___x_3058_;
v_acc_3051_ = v___x_3056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3060_, lean_object* v_keys_3061_, lean_object* v_vals_3062_, lean_object* v_i_3063_, lean_object* v_acc_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3060_, v_keys_3061_, v_vals_3062_, v_i_3063_, v_acc_3064_);
lean_dec_ref(v_vals_3062_);
lean_dec_ref(v_keys_3061_);
return v_res_3065_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3066_, lean_object* v_as_3067_, size_t v_i_3068_, size_t v_stop_3069_, lean_object* v_b_3070_){
_start:
{
lean_object* v___y_3072_; uint8_t v___x_3076_; 
v___x_3076_ = lean_usize_dec_eq(v_i_3068_, v_stop_3069_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; 
v___x_3077_ = lean_array_uget_borrowed(v_as_3067_, v_i_3068_);
switch(lean_obj_tag(v___x_3077_))
{
case 0:
{
lean_object* v_key_3078_; lean_object* v_val_3079_; lean_object* v___x_3080_; 
v_key_3078_ = lean_ctor_get(v___x_3077_, 0);
v_val_3079_ = lean_ctor_get(v___x_3077_, 1);
lean_inc(v_f_3066_);
lean_inc(v_val_3079_);
lean_inc(v_key_3078_);
v___x_3080_ = lean_apply_3(v_f_3066_, v_b_3070_, v_key_3078_, v_val_3079_);
v___y_3072_ = v___x_3080_;
goto v___jp_3071_;
}
case 1:
{
lean_object* v_node_3081_; lean_object* v___x_3082_; 
v_node_3081_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_f_3066_);
v___x_3082_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3066_, v_node_3081_, v_b_3070_);
v___y_3072_ = v___x_3082_;
goto v___jp_3071_;
}
default: 
{
v___y_3072_ = v_b_3070_;
goto v___jp_3071_;
}
}
}
else
{
lean_dec(v_f_3066_);
return v_b_3070_;
}
v___jp_3071_:
{
size_t v___x_3073_; size_t v___x_3074_; 
v___x_3073_ = ((size_t)1ULL);
v___x_3074_ = lean_usize_add(v_i_3068_, v___x_3073_);
v_i_3068_ = v___x_3074_;
v_b_3070_ = v___y_3072_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3066_ = stack[0].m_obj;
lean_object* v_as_3067_ = stack[1].m_obj;
size_t v_i_3068_ = stack[2].m_num;
size_t v_stop_3069_ = stack[3].m_num;
lean_object* v_b_3070_ = stack[4].m_obj;
lean_object* v_res_3083_;
v_res_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3066_, v_as_3067_, v_i_3068_, v_stop_3069_, v_b_3070_);
stack->m_obj
 = v_res_3083_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3084_, lean_object* v_x_3085_, lean_object* v_x_3086_){
_start:
{
if (lean_obj_tag(v_x_3085_) == 0)
{
lean_object* v_es_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; 
v_es_3087_ = lean_ctor_get(v_x_3085_, 0);
v___x_3088_ = lean_unsigned_to_nat(0u);
v___x_3089_ = lean_array_get_size(v_es_3087_);
v___x_3090_ = lean_nat_dec_lt(v___x_3088_, v___x_3089_);
if (v___x_3090_ == 0)
{
lean_dec(v_f_3084_);
return v_x_3086_;
}
else
{
size_t v___x_3091_; size_t v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = ((size_t)0ULL);
v___x_3092_ = lean_usize_of_nat(v___x_3089_);
v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3084_, v_es_3087_, v___x_3091_, v___x_3092_, v_x_3086_);
return v___x_3093_;
}
}
else
{
lean_object* v_ks_3094_; lean_object* v_vs_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v_ks_3094_ = lean_ctor_get(v_x_3085_, 0);
v_vs_3095_ = lean_ctor_get(v_x_3085_, 1);
v___x_3096_ = lean_unsigned_to_nat(0u);
v___x_3097_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3084_, v_ks_3094_, v_vs_3095_, v___x_3096_, v_x_3086_);
return v___x_3097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3098_, lean_object* v_x_3099_, lean_object* v_x_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3098_, v_x_3099_, v_x_3100_);
lean_dec_ref(v_x_3099_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3102_, lean_object* v_as_3103_, lean_object* v_i_3104_, lean_object* v_stop_3105_, lean_object* v_b_3106_){
_start:
{
size_t v_i_boxed_3107_; size_t v_stop_boxed_3108_; lean_object* v_res_3109_; 
v_i_boxed_3107_ = lean_unbox_usize(v_i_3104_);
lean_dec(v_i_3104_);
v_stop_boxed_3108_ = lean_unbox_usize(v_stop_3105_);
lean_dec(v_stop_3105_);
v_res_3109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3102_, v_as_3103_, v_i_boxed_3107_, v_stop_boxed_3108_, v_b_3106_);
lean_dec_ref(v_as_3103_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object* v_f_3110_, lean_object* v_x1_3111_, lean_object* v_x2_3112_, lean_object* v_x3_3113_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = lean_apply_3(v_f_3110_, v_x1_3111_, v_x2_3112_, v_x3_3113_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object* v_map_3115_, lean_object* v_f_3116_, lean_object* v_init_3117_){
_start:
{
lean_object* v___f_3118_; lean_object* v___x_3119_; 
v___f_3118_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3118_, 0, v_f_3116_);
v___x_3119_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v___f_3118_, v_map_3115_, v_init_3117_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object* v_map_3120_, lean_object* v_f_3121_, lean_object* v_init_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3120_, v_f_3121_, v_init_3122_);
lean_dec_ref(v_map_3120_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* v_env_3125_){
_start:
{
lean_object* v___x_3126_; lean_object* v_ext_3127_; lean_object* v_toEnvExtension_3128_; lean_object* v_asyncMode_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; lean_object* v___x_3132_; lean_object* v_kinds_3133_; lean_object* v___f_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3126_ = l_Lean_Parser_parserExtension;
v_ext_3127_ = lean_ctor_get(v___x_3126_, 1);
v_toEnvExtension_3128_ = lean_ctor_get(v_ext_3127_, 0);
v_asyncMode_3129_ = lean_ctor_get(v_toEnvExtension_3128_, 2);
v___x_3130_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3131_ = 0;
v___x_3132_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3130_, v___x_3126_, v_env_3125_, v_asyncMode_3129_, v___x_3131_);
v_kinds_3133_ = lean_ctor_get(v___x_3132_, 1);
lean_inc_ref(v_kinds_3133_);
lean_dec(v___x_3132_);
v___f_3134_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKinds___closed__0));
v___x_3135_ = lean_box(0);
v___x_3136_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_kinds_3133_, v___f_3134_, v___x_3135_);
lean_dec_ref(v_kinds_3133_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object* v_00_u03c3_3137_, lean_object* v_00_u03b2_3138_, lean_object* v_map_3139_, lean_object* v_f_3140_, lean_object* v_init_3141_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3139_, v_f_3140_, v_init_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object* v_00_u03c3_3143_, lean_object* v_00_u03b2_3144_, lean_object* v_map_3145_, lean_object* v_f_3146_, lean_object* v_init_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(v_00_u03c3_3143_, v_00_u03b2_3144_, v_map_3145_, v_f_3146_, v_init_3147_);
lean_dec_ref(v_map_3145_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object* v_map_3149_, lean_object* v_f_3150_, lean_object* v_init_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3150_, v_map_3149_, v_init_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object* v_map_3153_, lean_object* v_f_3154_, lean_object* v_init_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(v_map_3153_, v_f_3154_, v_init_3155_);
lean_dec_ref(v_map_3153_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object* v_00_u03c3_3157_, lean_object* v_00_u03b2_3158_, lean_object* v_map_3159_, lean_object* v_f_3160_, lean_object* v_init_3161_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3160_, v_map_3159_, v_init_3161_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3163_, lean_object* v_00_u03b2_3164_, lean_object* v_map_3165_, lean_object* v_f_3166_, lean_object* v_init_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(v_00_u03c3_3163_, v_00_u03b2_3164_, v_map_3165_, v_f_3166_, v_init_3167_);
lean_dec_ref(v_map_3165_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3169_, lean_object* v_00_u03b1_3170_, lean_object* v_00_u03b2_3171_, lean_object* v_f_3172_, lean_object* v_x_3173_, lean_object* v_x_3174_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3172_, v_x_3173_, v_x_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3176_, lean_object* v_00_u03b1_3177_, lean_object* v_00_u03b2_3178_, lean_object* v_f_3179_, lean_object* v_x_3180_, lean_object* v_x_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(v_00_u03c3_3176_, v_00_u03b1_3177_, v_00_u03b2_3178_, v_f_3179_, v_x_3180_, v_x_3181_);
lean_dec_ref(v_x_3180_);
return v_res_3182_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3183_, lean_object* v_00_u03b2_3184_, lean_object* v_00_u03c3_3185_, lean_object* v_f_3186_, lean_object* v_as_3187_, size_t v_i_3188_, size_t v_stop_3189_, lean_object* v_b_3190_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3186_, v_as_3187_, v_i_3188_, v_stop_3189_, v_b_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3186_ = stack[3].m_obj;
lean_object* v_as_3187_ = stack[4].m_obj;
size_t v_i_3188_ = stack[5].m_num;
size_t v_stop_3189_ = stack[6].m_num;
lean_object* v_b_3190_ = stack[7].m_obj;
lean_object* v_res_3192_;
v_res_3192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_box(0), lean_box(0), lean_box(0), v_f_3186_, v_as_3187_, v_i_3188_, v_stop_3189_, v_b_3190_);
stack->m_obj
 = v_res_3192_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3193_, lean_object* v_00_u03b2_3194_, lean_object* v_00_u03c3_3195_, lean_object* v_f_3196_, lean_object* v_as_3197_, lean_object* v_i_3198_, lean_object* v_stop_3199_, lean_object* v_b_3200_){
_start:
{
size_t v_i_boxed_3201_; size_t v_stop_boxed_3202_; lean_object* v_res_3203_; 
v_i_boxed_3201_ = lean_unbox_usize(v_i_3198_);
lean_dec(v_i_3198_);
v_stop_boxed_3202_ = lean_unbox_usize(v_stop_3199_);
lean_dec(v_stop_3199_);
v_res_3203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3193_, v_00_u03b2_3194_, v_00_u03c3_3195_, v_f_3196_, v_as_3197_, v_i_boxed_3201_, v_stop_boxed_3202_, v_b_3200_);
lean_dec_ref(v_as_3197_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3204_, lean_object* v_00_u03b1_3205_, lean_object* v_00_u03b2_3206_, lean_object* v_f_3207_, lean_object* v_keys_3208_, lean_object* v_vals_3209_, lean_object* v_heq_3210_, lean_object* v_i_3211_, lean_object* v_acc_3212_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3207_, v_keys_3208_, v_vals_3209_, v_i_3211_, v_acc_3212_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3214_, lean_object* v_00_u03b1_3215_, lean_object* v_00_u03b2_3216_, lean_object* v_f_3217_, lean_object* v_keys_3218_, lean_object* v_vals_3219_, lean_object* v_heq_3220_, lean_object* v_i_3221_, lean_object* v_acc_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3214_, v_00_u03b1_3215_, v_00_u03b2_3216_, v_f_3217_, v_keys_3218_, v_vals_3219_, v_heq_3220_, v_i_3221_, v_acc_3222_);
lean_dec_ref(v_vals_3219_);
lean_dec_ref(v_keys_3218_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* v_env_3224_){
_start:
{
lean_object* v___x_3225_; lean_object* v_ext_3226_; lean_object* v_toEnvExtension_3227_; lean_object* v_asyncMode_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; lean_object* v_tokens_3232_; 
v___x_3225_ = l_Lean_Parser_parserExtension;
v_ext_3226_ = lean_ctor_get(v___x_3225_, 1);
v_toEnvExtension_3227_ = lean_ctor_get(v_ext_3226_, 0);
v_asyncMode_3228_ = lean_ctor_get(v_toEnvExtension_3227_, 2);
v___x_3229_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3230_ = 0;
v___x_3231_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3229_, v___x_3225_, v_env_3224_, v_asyncMode_3228_, v___x_3230_);
v_tokens_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc_ref(v_tokens_3232_);
lean_dec(v___x_3231_);
return v_tokens_3232_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3257_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__8));
v___x_3258_ = l_Lean_mkAtom(v___x_3257_);
return v___x_3258_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3259_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__10, &l_Lean_Parser_mkInputContext___auto__1___closed__10_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__10);
v___x_3260_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3261_ = lean_array_push(v___x_3260_, v___x_3259_);
return v___x_3261_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3272_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3273_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3274_ = lean_array_push(v___x_3273_, v___x_3272_);
return v___x_3274_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3275_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__15, &l_Lean_Parser_mkInputContext___auto__1___closed__15_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__15);
v___x_3276_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__13));
v___x_3277_ = lean_box(2);
v___x_3278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
lean_ctor_set(v___x_3278_, 1, v___x_3276_);
lean_ctor_set(v___x_3278_, 2, v___x_3275_);
return v___x_3278_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3279_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__16, &l_Lean_Parser_mkInputContext___auto__1___closed__16_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__16);
v___x_3280_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__11, &l_Lean_Parser_mkInputContext___auto__1___closed__11_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__11);
v___x_3281_ = lean_array_push(v___x_3280_, v___x_3279_);
return v___x_3281_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3282_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3283_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__17, &l_Lean_Parser_mkInputContext___auto__1___closed__17_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__17);
v___x_3284_ = lean_array_push(v___x_3283_, v___x_3282_);
return v___x_3284_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3285_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3286_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__18, &l_Lean_Parser_mkInputContext___auto__1___closed__18_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__18);
v___x_3287_ = lean_array_push(v___x_3286_, v___x_3285_);
return v___x_3287_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3289_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__19, &l_Lean_Parser_mkInputContext___auto__1___closed__19_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__19);
v___x_3290_ = lean_array_push(v___x_3289_, v___x_3288_);
return v___x_3290_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3292_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__20, &l_Lean_Parser_mkInputContext___auto__1___closed__20_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__20);
v___x_3293_ = lean_array_push(v___x_3292_, v___x_3291_);
return v___x_3293_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3294_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__21, &l_Lean_Parser_mkInputContext___auto__1___closed__21_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__21);
v___x_3295_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__9));
v___x_3296_ = lean_box(2);
v___x_3297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
lean_ctor_set(v___x_3297_, 1, v___x_3295_);
lean_ctor_set(v___x_3297_, 2, v___x_3294_);
return v___x_3297_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3298_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__22, &l_Lean_Parser_mkInputContext___auto__1___closed__22_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__22);
v___x_3299_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3300_ = lean_array_push(v___x_3299_, v___x_3298_);
return v___x_3300_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3301_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__23, &l_Lean_Parser_mkInputContext___auto__1___closed__23_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__23);
v___x_3302_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3303_ = lean_box(2);
v___x_3304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
lean_ctor_set(v___x_3304_, 1, v___x_3302_);
lean_ctor_set(v___x_3304_, 2, v___x_3301_);
return v___x_3304_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__24, &l_Lean_Parser_mkInputContext___auto__1___closed__24_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__24);
v___x_3306_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3307_ = lean_array_push(v___x_3306_, v___x_3305_);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3308_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__25, &l_Lean_Parser_mkInputContext___auto__1___closed__25_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__25);
v___x_3309_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3310_ = lean_box(2);
v___x_3311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
lean_ctor_set(v___x_3311_, 1, v___x_3309_);
lean_ctor_set(v___x_3311_, 2, v___x_3308_);
return v___x_3311_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3312_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__26, &l_Lean_Parser_mkInputContext___auto__1___closed__26_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__26);
v___x_3313_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3314_ = lean_array_push(v___x_3313_, v___x_3312_);
return v___x_3314_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3315_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__27, &l_Lean_Parser_mkInputContext___auto__1___closed__27_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__27);
v___x_3316_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3317_ = lean_box(2);
v___x_3318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
lean_ctor_set(v___x_3318_, 1, v___x_3316_);
lean_ctor_set(v___x_3318_, 2, v___x_3315_);
return v___x_3318_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1(void){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__28, &l_Lean_Parser_mkInputContext___auto__1___closed__28_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__28);
return v___x_3319_;
}
}
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object* v_input_3320_, lean_object* v_fileName_3321_, uint8_t v_normalizeLineEndings_3322_, lean_object* v_endPos_3323_){
_start:
{
lean_object* v_fst_3325_; lean_object* v_snd_3326_; lean_object* v_text_3332_; 
v_text_3332_ = l_Lean_FileMap_ofString(v_input_3320_);
if (v_normalizeLineEndings_3322_ == 0)
{
v_fst_3325_ = v_text_3332_;
v_snd_3326_ = v_endPos_3323_;
goto v___jp_3324_;
}
else
{
lean_object* v_source_3333_; lean_object* v_endPos_x27_3334_; lean_object* v___x_3335_; lean_object* v_text_3336_; lean_object* v___x_3337_; 
v_source_3333_ = lean_ctor_get(v_text_3332_, 0);
lean_inc_ref(v_source_3333_);
v_endPos_x27_3334_ = l_Lean_FileMap_toPosition(v_text_3332_, v_endPos_3323_);
lean_dec(v_endPos_3323_);
v___x_3335_ = l_String_crlfToLf(v_source_3333_);
lean_dec_ref(v_source_3333_);
v_text_3336_ = l_Lean_FileMap_ofString(v___x_3335_);
v___x_3337_ = l_Lean_FileMap_ofPosition(v_text_3336_, v_endPos_x27_3334_);
v_fst_3325_ = v_text_3336_;
v_snd_3326_ = v___x_3337_;
goto v___jp_3324_;
}
v___jp_3324_:
{
lean_object* v_source_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; 
v_source_3327_ = lean_ctor_get(v_fst_3325_, 0);
lean_inc_ref(v_source_3327_);
v___x_3328_ = lean_string_utf8_byte_size(v_source_3327_);
v___x_3329_ = lean_nat_dec_le(v_snd_3326_, v___x_3328_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; 
lean_dec(v_snd_3326_);
v___x_3330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3330_, 0, v_source_3327_);
lean_ctor_set(v___x_3330_, 1, v_fileName_3321_);
lean_ctor_set(v___x_3330_, 2, v_fst_3325_);
lean_ctor_set(v___x_3330_, 3, v___x_3328_);
return v___x_3330_;
}
else
{
lean_object* v___x_3331_; 
v___x_3331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3331_, 0, v_source_3327_);
lean_ctor_set(v___x_3331_, 1, v_fileName_3321_);
lean_ctor_set(v___x_3331_, 2, v_fst_3325_);
lean_ctor_set(v___x_3331_, 3, v_snd_3326_);
return v___x_3331_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_mkInputContext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_3320_ = stack[0].m_obj;
lean_object* v_fileName_3321_ = stack[1].m_obj;
uint8_t v_normalizeLineEndings_3322_ = stack[2].m_num;
lean_object* v_endPos_3323_ = stack[3].m_obj;
lean_object* v_res_3338_;
v_res_3338_ = l_Lean_Parser_mkInputContext___redArg(v_input_3320_, v_fileName_3321_, v_normalizeLineEndings_3322_, v_endPos_3323_);
stack->m_obj
 = v_res_3338_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object* v_input_3339_, lean_object* v_fileName_3340_, lean_object* v_normalizeLineEndings_3341_, lean_object* v_endPos_3342_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3343_; lean_object* v_res_3344_; 
v_normalizeLineEndings_boxed_3343_ = lean_unbox(v_normalizeLineEndings_3341_);
v_res_3344_ = l_Lean_Parser_mkInputContext___redArg(v_input_3339_, v_fileName_3340_, v_normalizeLineEndings_boxed_3343_, v_endPos_3342_);
return v_res_3344_;
}
}
lean_object* l_Lean_Parser_mkInputContext(lean_object* v_input_3345_, lean_object* v_fileName_3346_, uint8_t v_normalizeLineEndings_3347_, lean_object* v_endPos_3348_, lean_object* v_endPos__valid_3349_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_Parser_mkInputContext___redArg(v_input_3345_, v_fileName_3346_, v_normalizeLineEndings_3347_, v_endPos_3348_);
return v___x_3350_;
}
}
LEAN_EXPORT void l_Lean_Parser_mkInputContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_3345_ = stack[0].m_obj;
lean_object* v_fileName_3346_ = stack[1].m_obj;
uint8_t v_normalizeLineEndings_3347_ = stack[2].m_num;
lean_object* v_endPos_3348_ = stack[3].m_obj;
lean_object* v_res_3351_;
v_res_3351_ = l_Lean_Parser_mkInputContext(v_input_3345_, v_fileName_3346_, v_normalizeLineEndings_3347_, v_endPos_3348_, lean_box(0));
stack->m_obj
 = v_res_3351_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object* v_input_3352_, lean_object* v_fileName_3353_, lean_object* v_normalizeLineEndings_3354_, lean_object* v_endPos_3355_, lean_object* v_endPos__valid_3356_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3357_; lean_object* v_res_3358_; 
v_normalizeLineEndings_boxed_3357_ = lean_unbox(v_normalizeLineEndings_3354_);
v_res_3358_ = l_Lean_Parser_mkInputContext(v_input_3352_, v_fileName_3353_, v_normalizeLineEndings_boxed_3357_, v_endPos_3355_, v_endPos__valid_3356_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* v_input_3361_){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3362_ = l_Lean_Parser_SyntaxStack_empty;
v___x_3363_ = lean_unsigned_to_nat(0u);
v___x_3364_ = l_Lean_Parser_initCacheForInput(v_input_3361_);
v___x_3365_ = lean_box(0);
v___x_3366_ = ((lean_object*)(l_Lean_Parser_mkParserState___closed__0));
v___x_3367_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3362_);
lean_ctor_set(v___x_3367_, 1, v___x_3363_);
lean_ctor_set(v___x_3367_, 2, v___x_3363_);
lean_ctor_set(v___x_3367_, 3, v___x_3364_);
lean_ctor_set(v___x_3367_, 4, v___x_3365_);
lean_ctor_set(v___x_3367_, 5, v___x_3366_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* v_input_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_Parser_mkParserState(v_input_3368_);
lean_dec_ref(v_input_3368_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* v_env_3372_, lean_object* v_catName_3373_, lean_object* v_input_3374_, lean_object* v_fileName_3375_){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v_p_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v_ictx_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v_s_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v___x_3376_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__0));
v___x_3377_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 1);
lean_closure_set(v___x_3377_, 0, v_catName_3373_);
v_p_3378_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_3378_, 0, v___x_3376_);
lean_closure_set(v_p_3378_, 1, v___x_3377_);
v___x_3379_ = 1;
v___x_3380_ = lean_string_utf8_byte_size(v_input_3374_);
lean_inc_ref(v_input_3374_);
v_ictx_3381_ = l_Lean_Parser_mkInputContext___redArg(v_input_3374_, v_fileName_3375_, v___x_3379_, v___x_3380_);
v___x_3382_ = l_Lean_Options_empty;
v___x_3383_ = lean_box(0);
v___x_3384_ = lean_box(0);
lean_inc_ref(v_env_3372_);
v___x_3385_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3385_, 0, v_env_3372_);
lean_ctor_set(v___x_3385_, 1, v___x_3382_);
lean_ctor_set(v___x_3385_, 2, v___x_3383_);
lean_ctor_set(v___x_3385_, 3, v___x_3384_);
v___x_3386_ = l_Lean_Parser_getTokenTable(v_env_3372_);
v___x_3387_ = l_Lean_Parser_mkParserState(v_input_3374_);
lean_dec_ref(v_input_3374_);
lean_inc_ref(v_ictx_3381_);
v_s_3388_ = l_Lean_Parser_ParserFn_run(v_p_3378_, v_ictx_3381_, v___x_3385_, v___x_3386_, v___x_3387_);
lean_inc_ref(v_s_3388_);
v___x_3389_ = l_Lean_Parser_ParserState_allErrors(v_s_3388_);
v___x_3390_ = lean_array_get_size(v___x_3389_);
lean_dec_ref(v___x_3389_);
v___x_3391_ = lean_unsigned_to_nat(0u);
v___x_3392_ = lean_nat_dec_eq(v___x_3390_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3381_, v_s_3388_);
v___x_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
return v___x_3394_;
}
else
{
lean_object* v_stxStack_3395_; lean_object* v_pos_3396_; uint8_t v___x_3397_; 
v_stxStack_3395_ = lean_ctor_get(v_s_3388_, 0);
v_pos_3396_ = lean_ctor_get(v_s_3388_, 2);
v___x_3397_ = l_Lean_Parser_InputContext_atEnd(v_ictx_3381_, v_pos_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3398_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__1));
v___x_3399_ = l_Lean_Parser_ParserState_mkError(v_s_3388_, v___x_3398_);
v___x_3400_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3381_, v___x_3399_);
v___x_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
return v___x_3401_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_inc_ref(v_stxStack_3395_);
lean_dec_ref(v_s_3388_);
lean_dec_ref(v_ictx_3381_);
v___x_3402_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3395_);
lean_dec_ref(v_stxStack_3395_);
v___x_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
return v___x_3403_;
}
}
}
}
lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* v_addFnName_3404_, lean_object* v_catName_3405_, lean_object* v_declName_3406_, lean_object* v_prio_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v_val_3423_; lean_object* v___x_3424_; 
v___x_3411_ = lean_box(0);
v___x_3412_ = l_Lean_mkConst(v_addFnName_3404_, v___x_3411_);
v___x_3413_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_catName_3405_);
lean_inc_n(v_declName_3406_, 2);
v___x_3414_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3406_);
v___x_3415_ = l_Lean_mkConst(v_declName_3406_, v___x_3411_);
v___x_3416_ = l_Lean_mkRawNatLit(v_prio_3407_);
v___x_3417_ = lean_unsigned_to_nat(4u);
v___x_3418_ = lean_mk_empty_array_with_capacity(v___x_3417_);
v___x_3419_ = lean_array_push(v___x_3418_, v___x_3413_);
v___x_3420_ = lean_array_push(v___x_3419_, v___x_3414_);
v___x_3421_ = lean_array_push(v___x_3420_, v___x_3415_);
v___x_3422_ = lean_array_push(v___x_3421_, v___x_3416_);
v_val_3423_ = l_Lean_mkAppN(v___x_3412_, v___x_3422_);
lean_dec_ref(v___x_3422_);
v___x_3424_ = l_Lean_declareBuiltin(v_declName_3406_, v_val_3423_, v_a_3408_, v_a_3409_);
return v___x_3424_;
}
}
LEAN_EXPORT void l_Lean_Parser_declareBuiltinParser_0interp(lean_interpreter_value* stack)
{
lean_object* v_addFnName_3404_ = stack[0].m_obj;
lean_object* v_catName_3405_ = stack[1].m_obj;
lean_object* v_declName_3406_ = stack[2].m_obj;
lean_object* v_prio_3407_ = stack[3].m_obj;
lean_object* v_a_3408_ = stack[4].m_obj;
lean_object* v_a_3409_ = stack[5].m_obj;
lean_object* v_res_3425_;
v_res_3425_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3404_, v_catName_3405_, v_declName_3406_, v_prio_3407_, v_a_3408_, v_a_3409_);
stack->m_obj
 = v_res_3425_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object* v_addFnName_3426_, lean_object* v_catName_3427_, lean_object* v_declName_3428_, lean_object* v_prio_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3426_, v_catName_3427_, v_declName_3428_, v_prio_3429_, v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
return v_res_3433_;
}
}
lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* v_catName_3439_, lean_object* v_declName_3440_, lean_object* v_prio_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = ((lean_object*)(l_Lean_Parser_declareLeadingBuiltinParser___closed__1));
v___x_3446_ = l_Lean_Parser_declareBuiltinParser(v___x_3445_, v_catName_3439_, v_declName_3440_, v_prio_3441_, v_a_3442_, v_a_3443_);
return v___x_3446_;
}
}
LEAN_EXPORT void l_Lean_Parser_declareLeadingBuiltinParser_0interp(lean_interpreter_value* stack)
{
lean_object* v_catName_3439_ = stack[0].m_obj;
lean_object* v_declName_3440_ = stack[1].m_obj;
lean_object* v_prio_3441_ = stack[2].m_obj;
lean_object* v_a_3442_ = stack[3].m_obj;
lean_object* v_a_3443_ = stack[4].m_obj;
lean_object* v_res_3447_;
v_res_3447_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3439_, v_declName_3440_, v_prio_3441_, v_a_3442_, v_a_3443_);
stack->m_obj
 = v_res_3447_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object* v_catName_3448_, lean_object* v_declName_3449_, lean_object* v_prio_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3448_, v_declName_3449_, v_prio_3450_, v_a_3451_, v_a_3452_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
return v_res_3454_;
}
}
lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* v_catName_3460_, lean_object* v_declName_3461_, lean_object* v_prio_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = ((lean_object*)(l_Lean_Parser_declareTrailingBuiltinParser___closed__1));
v___x_3467_ = l_Lean_Parser_declareBuiltinParser(v___x_3466_, v_catName_3460_, v_declName_3461_, v_prio_3462_, v_a_3463_, v_a_3464_);
return v___x_3467_;
}
}
LEAN_EXPORT void l_Lean_Parser_declareTrailingBuiltinParser_0interp(lean_interpreter_value* stack)
{
lean_object* v_catName_3460_ = stack[0].m_obj;
lean_object* v_declName_3461_ = stack[1].m_obj;
lean_object* v_prio_3462_ = stack[2].m_obj;
lean_object* v_a_3463_ = stack[3].m_obj;
lean_object* v_a_3464_ = stack[4].m_obj;
lean_object* v_res_3468_;
v_res_3468_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3460_, v_declName_3461_, v_prio_3462_, v_a_3463_, v_a_3464_);
stack->m_obj
 = v_res_3468_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object* v_catName_3469_, lean_object* v_declName_3470_, lean_object* v_prio_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3469_, v_declName_3470_, v_prio_3471_, v_a_3472_, v_a_3473_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* v_args_3482_){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v___x_3483_ = l_Lean_Syntax_getNumArgs(v_args_3482_);
v___x_3484_ = lean_unsigned_to_nat(0u);
v___x_3485_ = lean_nat_dec_eq(v___x_3483_, v___x_3484_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3486_ = lean_unsigned_to_nat(1u);
v___x_3487_ = lean_nat_dec_eq(v___x_3483_, v___x_3486_);
lean_dec(v___x_3483_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
v___x_3488_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__1));
return v___x_3488_;
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = l_Lean_Syntax_getArg(v_args_3482_, v___x_3484_);
v___x_3490_ = l_Lean_Syntax_isNatLit_x3f(v___x_3489_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3491_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__2));
v___x_3492_ = l_Lean_Syntax_formatStx(v___x_3489_, v___x_3490_, v___x_3485_);
v___x_3493_ = l_Std_Format_defWidth;
v___x_3494_ = l_Std_Format_pretty(v___x_3492_, v___x_3493_, v___x_3484_, v___x_3484_);
v___x_3495_ = lean_string_append(v___x_3491_, v___x_3494_);
lean_dec_ref(v___x_3494_);
v___x_3496_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3497_ = lean_string_append(v___x_3495_, v___x_3496_);
v___x_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
return v___x_3498_;
}
else
{
lean_object* v_val_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec(v___x_3489_);
v_val_3499_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3490_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_val_3499_);
lean_dec(v___x_3490_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_val_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
}
else
{
lean_object* v___x_3507_; 
lean_dec(v___x_3483_);
v___x_3507_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__3));
return v___x_3507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* v_args_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_Parser_getParserPriority(v_args_3508_);
lean_dec(v_args_3508_);
return v_res_3509_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0));
v___x_3512_ = l_Lean_stringToMessageData(v___x_3511_);
return v___x_3512_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2));
v___x_3515_ = l_Lean_stringToMessageData(v___x_3514_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3517_ = l_Lean_stringToMessageData(v___x_3516_);
return v___x_3517_;
}
}
lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object* v_name_3521_, uint8_t v_kind_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___y_3532_; 
v___x_3526_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1);
v___x_3527_ = l_Lean_MessageData_ofName(v_name_3521_);
v___x_3528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3526_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3528_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
switch(v_kind_3522_)
{
case 0:
{
lean_object* v___x_3539_; 
v___x_3539_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5));
v___y_3532_ = v___x_3539_;
goto v___jp_3531_;
}
case 1:
{
lean_object* v___x_3540_; 
v___x_3540_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6));
v___y_3532_ = v___x_3540_;
goto v___jp_3531_;
}
default: 
{
lean_object* v___x_3541_; 
v___x_3541_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7));
v___y_3532_ = v___x_3541_;
goto v___jp_3531_;
}
}
v___jp_3531_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
lean_inc_ref(v___y_3532_);
v___x_3533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3533_, 0, v___y_3532_);
v___x_3534_ = l_Lean_MessageData_ofFormat(v___x_3533_);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3530_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3535_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
v___x_3538_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3537_, v___y_3523_, v___y_3524_);
return v___x_3538_;
}
}
}
LEAN_EXPORT void l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3521_ = stack[0].m_obj;
uint8_t v_kind_3522_ = stack[1].m_num;
lean_object* v___y_3523_ = stack[2].m_obj;
lean_object* v___y_3524_ = stack[3].m_obj;
lean_object* v_res_3542_;
v_res_3542_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3521_, v_kind_3522_, v___y_3523_, v___y_3524_);
stack->m_obj
 = v_res_3542_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object* v_name_3543_, lean_object* v_kind_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
uint8_t v_kind_boxed_3548_; lean_object* v_res_3549_; 
v_kind_boxed_3548_ = lean_unbox(v_kind_3544_);
v_res_3549_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3543_, v_kind_boxed_3548_, v___y_3545_, v___y_3546_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
return v_res_3549_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3550_, lean_object* v_msg_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_toCold_3555_; lean_object* v_currRecDepth_3556_; lean_object* v_ref_3557_; uint16_t v_optionFlags_3558_; uint8_t v_suppressElabErrors_3559_; uint8_t v_isRecordingDeps_3560_; lean_object* v_ref_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v_toCold_3555_ = lean_ctor_get(v___y_3552_, 0);
v_currRecDepth_3556_ = lean_ctor_get(v___y_3552_, 1);
v_ref_3557_ = lean_ctor_get(v___y_3552_, 2);
v_optionFlags_3558_ = lean_ctor_get_uint16(v___y_3552_, sizeof(void*)*3);
v_suppressElabErrors_3559_ = lean_ctor_get_uint8(v___y_3552_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3560_ = lean_ctor_get_uint8(v___y_3552_, sizeof(void*)*3 + 3);
v_ref_3561_ = l_Lean_replaceRef(v_ref_3550_, v_ref_3557_);
lean_inc(v_currRecDepth_3556_);
lean_inc_ref(v_toCold_3555_);
v___x_3562_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3562_, 0, v_toCold_3555_);
lean_ctor_set(v___x_3562_, 1, v_currRecDepth_3556_);
lean_ctor_set(v___x_3562_, 2, v_ref_3561_);
lean_ctor_set_uint16(v___x_3562_, sizeof(void*)*3, v_optionFlags_3558_);
lean_ctor_set_uint8(v___x_3562_, sizeof(void*)*3 + 2, v_suppressElabErrors_3559_);
lean_ctor_set_uint8(v___x_3562_, sizeof(void*)*3 + 3, v_isRecordingDeps_3560_);
v___x_3563_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_3551_, v___x_3562_, v___y_3553_);
lean_dec_ref_known(v___x_3562_, 3);
return v___x_3563_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3550_ = stack[0].m_obj;
lean_object* v_msg_3551_ = stack[1].m_obj;
lean_object* v___y_3552_ = stack[2].m_obj;
lean_object* v___y_3553_ = stack[3].m_obj;
lean_object* v_res_3564_;
v_res_3564_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3550_, v_msg_3551_, v___y_3552_, v___y_3553_);
stack->m_obj
 = v_res_3564_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3565_, lean_object* v_msg_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3565_, v_msg_3566_, v___y_3567_, v___y_3568_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v_ref_3565_);
return v_res_3570_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_3573_ = l_Lean_stringToMessageData(v___x_3572_);
return v___x_3573_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_3576_ = l_Lean_stringToMessageData(v___x_3575_);
return v___x_3576_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_3579_ = l_Lean_stringToMessageData(v___x_3578_);
return v___x_3579_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_3582_ = l_Lean_stringToMessageData(v___x_3581_);
return v___x_3582_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_3585_ = l_Lean_stringToMessageData(v___x_3584_);
return v___x_3585_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_3588_ = l_Lean_stringToMessageData(v___x_3587_);
return v___x_3588_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_3591_ = l_Lean_stringToMessageData(v___x_3590_);
return v___x_3591_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_3594_ = l_Lean_stringToMessageData(v___x_3593_);
return v___x_3594_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_3597_ = l_Lean_stringToMessageData(v___x_3596_);
return v___x_3597_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_3600_ = l_Lean_stringToMessageData(v___x_3599_);
return v___x_3600_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__21(void){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__20));
v___x_3603_ = l_Lean_stringToMessageData(v___x_3602_);
return v___x_3603_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_3604_, lean_object* v_declHint_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v_env_3610_; uint8_t v___x_3611_; 
v___x_3608_ = lean_box(0);
v___x_3609_ = lean_st_ref_get(v___y_3606_);
v_env_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc_ref(v_env_3610_);
lean_dec(v___x_3609_);
v___x_3611_ = l_Lean_Name_isAnonymous(v_declHint_3605_);
if (v___x_3611_ == 0)
{
uint8_t v_isExporting_3612_; 
v_isExporting_3612_ = lean_ctor_get_uint8(v_env_3610_, sizeof(void*)*13);
if (v_isExporting_3612_ == 0)
{
lean_object* v___x_3613_; 
lean_dec_ref(v_env_3610_);
lean_dec(v_declHint_3605_);
v___x_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3613_, 0, v_msg_3604_);
return v___x_3613_;
}
else
{
lean_object* v___x_3614_; uint8_t v___x_3615_; 
lean_inc_ref(v_env_3610_);
v___x_3614_ = l_Lean_Environment_setExporting(v_env_3610_, v___x_3611_);
lean_inc(v_declHint_3605_);
lean_inc_ref(v___x_3614_);
v___x_3615_ = l_Lean_Environment_contains(v___x_3614_, v_declHint_3605_, v_isExporting_3612_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; 
lean_dec_ref(v___x_3614_);
lean_dec_ref(v_env_3610_);
lean_dec(v_declHint_3605_);
v___x_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3616_, 0, v_msg_3604_);
return v___x_3616_;
}
else
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v_c_3622_; lean_object* v___x_3623_; 
v___x_3617_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_3618_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_3619_ = l_Lean_Options_empty;
v___x_3620_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3614_);
lean_ctor_set(v___x_3620_, 1, v___x_3617_);
lean_ctor_set(v___x_3620_, 2, v___x_3618_);
lean_ctor_set(v___x_3620_, 3, v___x_3619_);
lean_inc(v_declHint_3605_);
v___x_3621_ = l_Lean_MessageData_ofConstName(v_declHint_3605_, v___x_3611_);
v_c_3622_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3622_, 0, v___x_3620_);
lean_ctor_set(v_c_3622_, 1, v___x_3621_);
v___x_3623_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3610_, v_declHint_3605_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
lean_dec_ref(v_env_3610_);
lean_dec(v_declHint_3605_);
v___x_3624_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
lean_ctor_set(v___x_3625_, 1, v_c_3622_);
v___x_3626_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_3627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3625_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = l_Lean_MessageData_note(v___x_3627_);
v___x_3629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3629_, 0, v_msg_3604_);
lean_ctor_set(v___x_3629_, 1, v___x_3628_);
v___x_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3629_);
return v___x_3630_;
}
else
{
lean_object* v_val_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3687_; 
v_val_3631_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3633_ = v___x_3623_;
v_isShared_3634_ = v_isSharedCheck_3687_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_val_3631_);
lean_dec(v___x_3623_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3687_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3635_; lean_object* v_modules_3636_; lean_object* v_moduleNames_3637_; lean_object* v_mod_3638_; uint8_t v___y_3640_; uint8_t v___x_3670_; 
v___x_3635_ = l_Lean_Environment_header(v_env_3610_);
lean_dec_ref(v_env_3610_);
v_modules_3636_ = lean_ctor_get(v___x_3635_, 3);
lean_inc_ref(v_modules_3636_);
v_moduleNames_3637_ = lean_ctor_get(v___x_3635_, 4);
lean_inc_ref(v_moduleNames_3637_);
lean_dec_ref(v___x_3635_);
v_mod_3638_ = lean_array_get(v___x_3608_, v_moduleNames_3637_, v_val_3631_);
lean_dec_ref(v_moduleNames_3637_);
v___x_3670_ = l_Lean_isPrivateName(v_declHint_3605_);
lean_dec(v_declHint_3605_);
if (v___x_3670_ == 0)
{
lean_object* v___x_3671_; uint8_t v___x_3672_; 
v___x_3671_ = lean_array_get_size(v_modules_3636_);
v___x_3672_ = lean_nat_dec_lt(v_val_3631_, v___x_3671_);
if (v___x_3672_ == 0)
{
lean_dec_ref(v_modules_3636_);
lean_dec(v_val_3631_);
v___y_3640_ = v___x_3670_;
goto v___jp_3639_;
}
else
{
lean_object* v___x_3673_; lean_object* v_toImport_3674_; uint8_t v_isExported_3675_; 
v___x_3673_ = lean_array_fget(v_modules_3636_, v_val_3631_);
lean_dec(v_val_3631_);
lean_dec_ref(v_modules_3636_);
v_toImport_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc_ref(v_toImport_3674_);
lean_dec(v___x_3673_);
v_isExported_3675_ = lean_ctor_get_uint8(v_toImport_3674_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_3674_);
v___y_3640_ = v_isExported_3675_;
goto v___jp_3639_;
}
}
else
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
lean_dec_ref(v_modules_3636_);
lean_del_object(v___x_3633_);
lean_dec(v_val_3631_);
v___x_3676_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3676_);
lean_ctor_set(v___x_3677_, 1, v_c_3622_);
v___x_3678_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_3679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3677_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = l_Lean_MessageData_ofName(v_mod_3638_);
v___x_3681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3679_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__21);
v___x_3683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3681_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = l_Lean_MessageData_note(v___x_3683_);
v___x_3685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3685_, 0, v_msg_3604_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
return v___x_3686_;
}
v___jp_3639_:
{
if (v___y_3640_ == 0)
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3652_; 
v___x_3641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_3642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
lean_ctor_set(v___x_3642_, 1, v_c_3622_);
v___x_3643_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_3644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3642_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
v___x_3645_ = l_Lean_MessageData_ofName(v_mod_3638_);
v___x_3646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3644_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_3648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3646_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = l_Lean_MessageData_note(v___x_3648_);
v___x_3650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3650_, 0, v_msg_3604_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3650_);
v___x_3652_ = v___x_3633_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3668_; 
v___x_3654_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
lean_ctor_set(v___x_3655_, 1, v_c_3622_);
v___x_3656_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = l_Lean_MessageData_ofName(v_mod_3638_);
lean_inc_ref(v___x_3658_);
v___x_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_3661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3659_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
lean_ctor_set(v___x_3662_, 1, v___x_3658_);
v___x_3663_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = l_Lean_MessageData_note(v___x_3664_);
v___x_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3666_, 0, v_msg_3604_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3666_);
v___x_3668_ = v___x_3633_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
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
lean_object* v___x_3688_; 
lean_dec_ref(v_env_3610_);
lean_dec(v_declHint_3605_);
v___x_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3688_, 0, v_msg_3604_);
return v___x_3688_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3604_ = stack[0].m_obj;
lean_object* v_declHint_3605_ = stack[1].m_obj;
lean_object* v___y_3606_ = stack[2].m_obj;
lean_object* v_res_3689_;
v_res_3689_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3604_, v_declHint_3605_, v___y_3606_);
stack->m_obj
 = v_res_3689_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_3690_, lean_object* v_declHint_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3690_, v_declHint_3691_, v___y_3692_);
lean_dec(v___y_3692_);
return v_res_3694_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_3695_, lean_object* v_declHint_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3710_; 
v___x_3700_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3695_, v_declHint_3696_, v___y_3698_);
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3703_ = v___x_3700_;
v_isShared_3704_ = v_isSharedCheck_3710_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3710_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3708_; 
v___x_3705_ = l_Lean_unknownIdentifierMessageTag;
v___x_3706_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3705_);
lean_ctor_set(v___x_3706_, 1, v_a_3701_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3706_);
v___x_3708_ = v___x_3703_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3695_ = stack[0].m_obj;
lean_object* v_declHint_3696_ = stack[1].m_obj;
lean_object* v___y_3697_ = stack[2].m_obj;
lean_object* v___y_3698_ = stack[3].m_obj;
lean_object* v_res_3711_;
v_res_3711_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3695_, v_declHint_3696_, v___y_3697_, v___y_3698_);
stack->m_obj
 = v_res_3711_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_3712_, lean_object* v_declHint_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3712_, v_declHint_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
return v_res_3717_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3718_, lean_object* v_msg_3719_, lean_object* v_declHint_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v___x_3724_; lean_object* v_a_3725_; lean_object* v___x_3726_; 
v___x_3724_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3719_, v_declHint_3720_, v___y_3721_, v___y_3722_);
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref(v___x_3724_);
v___x_3726_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3718_, v_a_3725_, v___y_3721_, v___y_3722_);
return v___x_3726_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3718_ = stack[0].m_obj;
lean_object* v_msg_3719_ = stack[1].m_obj;
lean_object* v_declHint_3720_ = stack[2].m_obj;
lean_object* v___y_3721_ = stack[3].m_obj;
lean_object* v___y_3722_ = stack[4].m_obj;
lean_object* v_res_3727_;
v_res_3727_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3718_, v_msg_3719_, v_declHint_3720_, v___y_3721_, v___y_3722_);
stack->m_obj
 = v_res_3727_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3728_, lean_object* v_msg_3729_, lean_object* v_declHint_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3728_, v_msg_3729_, v_declHint_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v_ref_3728_);
return v_res_3734_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3735_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_3736_ = l_Lean_stringToMessageData(v___x_3735_);
return v___x_3736_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3737_, lean_object* v_constName_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v___x_3742_; uint8_t v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3742_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3743_ = 0;
lean_inc(v_constName_3738_);
v___x_3744_ = l_Lean_MessageData_ofConstName(v_constName_3738_, v___x_3743_);
v___x_3745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3742_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3745_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3737_, v___x_3747_, v_constName_3738_, v___y_3739_, v___y_3740_);
return v___x_3748_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3737_ = stack[0].m_obj;
lean_object* v_constName_3738_ = stack[1].m_obj;
lean_object* v___y_3739_ = stack[2].m_obj;
lean_object* v___y_3740_ = stack[3].m_obj;
lean_object* v_res_3749_;
v_res_3749_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3737_, v_constName_3738_, v___y_3739_, v___y_3740_);
stack->m_obj
 = v_res_3749_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3750_, lean_object* v_constName_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3750_, v_constName_3751_, v___y_3752_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v_ref_3750_);
return v_res_3755_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object* v_constName_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v_ref_3760_; lean_object* v___x_3761_; 
v_ref_3760_ = lean_ctor_get(v___y_3757_, 2);
v___x_3761_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3760_, v_constName_3756_, v___y_3757_, v___y_3758_);
return v___x_3761_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3756_ = stack[0].m_obj;
lean_object* v___y_3757_ = stack[1].m_obj;
lean_object* v___y_3758_ = stack[2].m_obj;
lean_object* v_res_3762_;
v_res_3762_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3756_, v___y_3757_, v___y_3758_);
stack->m_obj
 = v_res_3762_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3763_, v___y_3764_, v___y_3765_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
return v_res_3767_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object* v_constName_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v___x_3772_; lean_object* v_env_3773_; uint8_t v___x_3774_; lean_object* v___x_3775_; 
v___x_3772_ = lean_st_ref_get(v___y_3770_);
v_env_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc_ref(v_env_3773_);
lean_dec(v___x_3772_);
v___x_3774_ = 0;
lean_inc(v_constName_3768_);
v___x_3775_ = l_Lean_Environment_find_x3f(v_env_3773_, v_constName_3768_, v___x_3774_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3768_, v___y_3769_, v___y_3770_);
return v___x_3776_;
}
else
{
lean_object* v_val_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec(v_constName_3768_);
v_val_3777_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3775_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_val_3777_);
lean_dec(v___x_3775_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set_tag(v___x_3779_, 0);
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_val_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3768_ = stack[0].m_obj;
lean_object* v___y_3769_ = stack[1].m_obj;
lean_object* v___y_3770_ = stack[2].m_obj;
lean_object* v_res_3785_;
v_res_3785_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3768_, v___y_3769_, v___y_3770_);
stack->m_obj
 = v_res_3785_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object* v_constName_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
return v_res_3790_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1(void){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3792_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0));
v___x_3793_ = l_Lean_stringToMessageData(v___x_3792_);
return v___x_3793_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2));
v___x_3796_ = l_Lean_stringToMessageData(v___x_3795_);
return v___x_3796_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* v_attrName_3797_, lean_object* v_catName_3798_, lean_object* v_declName_3799_, lean_object* v_stx_3800_, uint8_t v_kind_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_){
_start:
{
lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___x_3825_; 
v___x_3825_ = l_Lean_Attribute_Builtin_getPrio(v_stx_3800_, v_a_3802_, v_a_3803_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; lean_object* v___y_3828_; lean_object* v___y_3829_; uint8_t v___x_3857_; uint8_t v___x_3858_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref_known(v___x_3825_, 1);
v___x_3857_ = 0;
v___x_3858_ = l_Lean_instBEqAttributeKind_beq(v_kind_3801_, v___x_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; 
lean_dec(v_a_3826_);
lean_dec(v_declName_3799_);
lean_dec(v_catName_3798_);
v___x_3859_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_attrName_3797_, v_kind_3801_, v_a_3802_, v_a_3803_);
return v___x_3859_;
}
else
{
lean_dec(v_attrName_3797_);
v___y_3828_ = v_a_3802_;
v___y_3829_ = v_a_3803_;
goto v___jp_3827_;
}
v___jp_3827_:
{
lean_object* v___x_3830_; 
lean_inc(v_declName_3799_);
v___x_3830_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_declName_3799_, v___y_3828_, v___y_3829_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3832_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3830_, 1);
v___x_3832_ = l_Lean_ConstantInfo_type(v_a_3831_);
if (lean_obj_tag(v___x_3832_) == 4)
{
lean_object* v_declName_3833_; 
v_declName_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_declName_3833_);
lean_dec_ref_known(v___x_3832_, 2);
if (lean_obj_tag(v_declName_3833_) == 1)
{
lean_object* v_pre_3834_; 
v_pre_3834_ = lean_ctor_get(v_declName_3833_, 0);
lean_inc(v_pre_3834_);
if (lean_obj_tag(v_pre_3834_) == 1)
{
lean_object* v_pre_3835_; 
v_pre_3835_ = lean_ctor_get(v_pre_3834_, 0);
lean_inc(v_pre_3835_);
if (lean_obj_tag(v_pre_3835_) == 1)
{
lean_object* v_pre_3836_; 
v_pre_3836_ = lean_ctor_get(v_pre_3835_, 0);
if (lean_obj_tag(v_pre_3836_) == 0)
{
lean_object* v_str_3837_; lean_object* v_str_3838_; lean_object* v_str_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; 
v_str_3837_ = lean_ctor_get(v_declName_3833_, 1);
lean_inc_ref(v_str_3837_);
lean_dec_ref_known(v_declName_3833_, 2);
v_str_3838_ = lean_ctor_get(v_pre_3834_, 1);
lean_inc_ref(v_str_3838_);
lean_dec_ref_known(v_pre_3834_, 2);
v_str_3839_ = lean_ctor_get(v_pre_3835_, 1);
lean_inc_ref(v_str_3839_);
lean_dec_ref_known(v_pre_3835_, 2);
v___x_3840_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3841_ = lean_string_dec_eq(v_str_3839_, v___x_3840_);
lean_dec_ref(v_str_3839_);
if (v___x_3841_ == 0)
{
lean_dec_ref(v_str_3838_);
lean_dec_ref(v_str_3837_);
lean_dec(v_a_3826_);
lean_dec(v_catName_3798_);
v___y_3812_ = v_a_3831_;
v___y_3813_ = v___y_3828_;
v___y_3814_ = v___y_3829_;
goto v___jp_3811_;
}
else
{
lean_object* v___x_3842_; uint8_t v___x_3843_; 
v___x_3842_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3843_ = lean_string_dec_eq(v_str_3838_, v___x_3842_);
lean_dec_ref(v_str_3838_);
if (v___x_3843_ == 0)
{
lean_dec_ref(v_str_3837_);
lean_dec(v_a_3826_);
lean_dec(v_catName_3798_);
v___y_3812_ = v_a_3831_;
v___y_3813_ = v___y_3828_;
v___y_3814_ = v___y_3829_;
goto v___jp_3811_;
}
else
{
lean_object* v___x_3844_; uint8_t v___x_3845_; 
v___x_3844_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_3845_ = lean_string_dec_eq(v_str_3837_, v___x_3844_);
if (v___x_3845_ == 0)
{
uint8_t v___x_3846_; 
v___x_3846_ = lean_string_dec_eq(v_str_3837_, v___x_3842_);
lean_dec_ref(v_str_3837_);
if (v___x_3846_ == 0)
{
lean_dec(v_a_3826_);
lean_dec(v_catName_3798_);
v___y_3812_ = v_a_3831_;
v___y_3813_ = v___y_3828_;
v___y_3814_ = v___y_3829_;
goto v___jp_3811_;
}
else
{
lean_object* v___x_3847_; 
lean_dec(v_a_3831_);
lean_inc(v_declName_3799_);
lean_inc(v_catName_3798_);
v___x_3847_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3798_, v_declName_3799_, v_a_3826_, v___y_3828_, v___y_3829_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_dec_ref_known(v___x_3847_, 1);
v___y_3806_ = v___y_3828_;
v___y_3807_ = v___y_3829_;
goto v___jp_3805_;
}
else
{
lean_dec(v_declName_3799_);
lean_dec(v_catName_3798_);
return v___x_3847_;
}
}
}
else
{
lean_object* v___x_3848_; 
lean_dec_ref(v_str_3837_);
lean_dec(v_a_3831_);
lean_inc(v_declName_3799_);
lean_inc(v_catName_3798_);
v___x_3848_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3798_, v_declName_3799_, v_a_3826_, v___y_3828_, v___y_3829_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_dec_ref_known(v___x_3848_, 1);
v___y_3806_ = v___y_3828_;
v___y_3807_ = v___y_3829_;
goto v___jp_3805_;
}
else
{
lean_dec(v_declName_3799_);
lean_dec(v_catName_3798_);
return v___x_3848_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3835_, 2);
lean_dec_ref_known(v_pre_3834_, 2);
lean_dec_ref_known(v_declName_3833_, 2);
lean_dec(v_a_3826_);
lean_dec(v_catName_3798_);
v___y_3812_ = v_a_3831_;
v___y_3813_ = v___y_3828_;
v___y_3814_ = v___y_3829_;
goto v___jp_3811_;
}
}
else
{
lean_dec_ref_known(v_pre_3834_, 2);
lean_dec(v_pre_3835_);
lean_dec_ref_known(v_declName_3833_, 2);
lean_dec(v_a_3826_);
lean_dec(v_catName_3798_);
v___y_3812_ = v_a_3831_;
v___y_3813_ = v___y_3828_;
v___y_3814_ = v___y_3829_;
goto v___jp_3811_;
}
}
else
{
lean_dec(v_pre_3834_);
lean_dec_ref_known(v_declName_3833_, 2);
lean_dec(v_a_3826_);
lean_dec(v_catName_3798_);
v___y_3812_ = v_a_3831_;
v___y_3813_ = v___y_3828_;
v___y_3814_ = v___y_3829_;
goto v___jp_3811_;
}
}
else
{
lean_dec(v_declName_3833_);
lean_dec(v_a_3826_);
lean_dec(v_catName_3798_);
v___y_3812_ = v_a_3831_;
v___y_3813_ = v___y_3828_;
v___y_3814_ = v___y_3829_;
goto v___jp_3811_;
}
}
else
{
lean_dec_ref(v___x_3832_);
lean_dec(v_a_3826_);
lean_dec(v_catName_3798_);
v___y_3812_ = v_a_3831_;
v___y_3813_ = v___y_3828_;
v___y_3814_ = v___y_3829_;
goto v___jp_3811_;
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec(v_a_3826_);
lean_dec(v_declName_3799_);
lean_dec(v_catName_3798_);
v_a_3849_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3830_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3830_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_declName_3799_);
lean_dec(v_catName_3798_);
lean_dec(v_attrName_3797_);
v_a_3860_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3825_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3825_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
v___jp_3805_:
{
lean_object* v___x_3808_; 
lean_inc(v_declName_3799_);
v___x_3808_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_3799_, v___y_3806_, v___y_3807_);
if (lean_obj_tag(v___x_3808_) == 0)
{
uint8_t v___x_3809_; lean_object* v___x_3810_; 
lean_dec_ref_known(v___x_3808_, 1);
v___x_3809_ = 1;
v___x_3810_ = l_Lean_Parser_runParserAttributeHooks(v_catName_3798_, v_declName_3799_, v___x_3809_, v___y_3806_, v___y_3807_);
return v___x_3810_;
}
else
{
lean_dec(v_declName_3799_);
lean_dec(v_catName_3798_);
return v___x_3808_;
}
}
v___jp_3811_:
{
lean_object* v___x_3815_; uint8_t v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3815_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
v___x_3816_ = 0;
v___x_3817_ = l_Lean_MessageData_ofConstName(v_declName_3799_, v___x_3816_);
v___x_3818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3815_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
v___x_3820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3818_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = l_Lean_ConstantInfo_type(v___y_3812_);
lean_dec_ref(v___y_3812_);
v___x_3822_ = l_Lean_indentExpr(v___x_3821_);
v___x_3823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3820_);
lean_ctor_set(v___x_3823_, 1, v___x_3822_);
v___x_3824_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3823_, v___y_3813_, v___y_3814_);
return v___x_3824_;
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_3797_ = stack[0].m_obj;
lean_object* v_catName_3798_ = stack[1].m_obj;
lean_object* v_declName_3799_ = stack[2].m_obj;
lean_object* v_stx_3800_ = stack[3].m_obj;
uint8_t v_kind_3801_ = stack[4].m_num;
lean_object* v_a_3802_ = stack[5].m_obj;
lean_object* v_a_3803_ = stack[6].m_obj;
lean_object* v_res_3868_;
v_res_3868_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3797_, v_catName_3798_, v_declName_3799_, v_stx_3800_, v_kind_3801_, v_a_3802_, v_a_3803_);
stack->m_obj
 = v_res_3868_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* v_attrName_3869_, lean_object* v_catName_3870_, lean_object* v_declName_3871_, lean_object* v_stx_3872_, lean_object* v_kind_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_){
_start:
{
uint8_t v_kind_boxed_3877_; lean_object* v_res_3878_; 
v_kind_boxed_3877_ = lean_unbox(v_kind_3873_);
v_res_3878_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3869_, v_catName_3870_, v_declName_3871_, v_stx_3872_, v_kind_boxed_3877_, v_a_3874_, v_a_3875_);
lean_dec(v_a_3875_);
lean_dec_ref(v_a_3874_);
return v_res_3878_;
}
}
lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object* v_00_u03b1_3879_, lean_object* v_name_3880_, uint8_t v_kind_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3880_, v_kind_3881_, v___y_3882_, v___y_3883_);
return v___x_3885_;
}
}
LEAN_EXPORT void l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3880_ = stack[1].m_obj;
uint8_t v_kind_3881_ = stack[2].m_num;
lean_object* v___y_3882_ = stack[3].m_obj;
lean_object* v___y_3883_ = stack[4].m_obj;
lean_object* v_res_3886_;
v_res_3886_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_box(0), v_name_3880_, v_kind_3881_, v___y_3882_, v___y_3883_);
stack->m_obj
 = v_res_3886_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b1_3887_, lean_object* v_name_3888_, lean_object* v_kind_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
uint8_t v_kind_boxed_3893_; lean_object* v_res_3894_; 
v_kind_boxed_3893_ = lean_unbox(v_kind_3889_);
v_res_3894_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(v_00_u03b1_3887_, v_name_3888_, v_kind_boxed_3893_, v___y_3890_, v___y_3891_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
return v_res_3894_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object* v_00_u03b1_3895_, lean_object* v_constName_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3896_, v___y_3897_, v___y_3898_);
return v___x_3900_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3896_ = stack[1].m_obj;
lean_object* v___y_3897_ = stack[2].m_obj;
lean_object* v___y_3898_ = stack[3].m_obj;
lean_object* v_res_3901_;
v_res_3901_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_box(0), v_constName_3896_, v___y_3897_, v___y_3898_);
stack->m_obj
 = v_res_3901_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3902_, lean_object* v_constName_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(v_00_u03b1_3902_, v_constName_3903_, v___y_3904_, v___y_3905_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
return v_res_3907_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3908_, lean_object* v_ref_3909_, lean_object* v_constName_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3909_, v_constName_3910_, v___y_3911_, v___y_3912_);
return v___x_3914_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3909_ = stack[1].m_obj;
lean_object* v_constName_3910_ = stack[2].m_obj;
lean_object* v___y_3911_ = stack[3].m_obj;
lean_object* v___y_3912_ = stack[4].m_obj;
lean_object* v_res_3915_;
v_res_3915_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_box(0), v_ref_3909_, v_constName_3910_, v___y_3911_, v___y_3912_);
stack->m_obj
 = v_res_3915_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3916_, lean_object* v_ref_3917_, lean_object* v_constName_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(v_00_u03b1_3916_, v_ref_3917_, v_constName_3918_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v_ref_3917_);
return v_res_3922_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3923_, lean_object* v_ref_3924_, lean_object* v_msg_3925_, lean_object* v_declHint_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3924_, v_msg_3925_, v_declHint_3926_, v___y_3927_, v___y_3928_);
return v___x_3930_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3924_ = stack[1].m_obj;
lean_object* v_msg_3925_ = stack[2].m_obj;
lean_object* v_declHint_3926_ = stack[3].m_obj;
lean_object* v___y_3927_ = stack[4].m_obj;
lean_object* v___y_3928_ = stack[5].m_obj;
lean_object* v_res_3931_;
v_res_3931_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_ref_3924_, v_msg_3925_, v_declHint_3926_, v___y_3927_, v___y_3928_);
stack->m_obj
 = v_res_3931_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3932_, lean_object* v_ref_3933_, lean_object* v_msg_3934_, lean_object* v_declHint_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3932_, v_ref_3933_, v_msg_3934_, v_declHint_3935_, v___y_3936_, v___y_3937_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v_ref_3933_);
return v_res_3939_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_3940_, lean_object* v_declHint_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3940_, v_declHint_3941_, v___y_3943_);
return v___x_3945_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3940_ = stack[0].m_obj;
lean_object* v_declHint_3941_ = stack[1].m_obj;
lean_object* v___y_3942_ = stack[2].m_obj;
lean_object* v___y_3943_ = stack[3].m_obj;
lean_object* v_res_3946_;
v_res_3946_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_3940_, v_declHint_3941_, v___y_3942_, v___y_3943_);
stack->m_obj
 = v_res_3946_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_3947_, lean_object* v_declHint_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_3947_, v_declHint_3948_, v___y_3949_, v___y_3950_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
return v_res_3952_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3953_, lean_object* v_ref_3954_, lean_object* v_msg_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3954_, v_msg_3955_, v___y_3956_, v___y_3957_);
return v___x_3959_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3954_ = stack[1].m_obj;
lean_object* v_msg_3955_ = stack[2].m_obj;
lean_object* v___y_3956_ = stack[3].m_obj;
lean_object* v___y_3957_ = stack[4].m_obj;
lean_object* v_res_3960_;
v_res_3960_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_box(0), v_ref_3954_, v_msg_3955_, v___y_3956_, v___y_3957_);
stack->m_obj
 = v_res_3960_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3961_, lean_object* v_ref_3962_, lean_object* v_msg_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3961_, v_ref_3962_, v_msg_3963_, v___y_3964_, v___y_3965_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
lean_dec(v_ref_3962_);
return v_res_3967_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2(void){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0));
v___x_3975_ = l_Lean_mkAtom(v___x_3974_);
return v___x_3975_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3976_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2);
v___x_3977_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3978_ = lean_array_push(v___x_3977_, v___x_3976_);
return v___x_3978_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3987_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7));
v___x_3988_ = l_Lean_mkAtom(v___x_3987_);
return v___x_3988_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3989_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8);
v___x_3990_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3991_ = lean_array_push(v___x_3990_, v___x_3989_);
return v___x_3991_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3992_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9);
v___x_3993_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6));
v___x_3994_ = lean_box(2);
v___x_3995_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
lean_ctor_set(v___x_3995_, 1, v___x_3993_);
lean_ctor_set(v___x_3995_, 2, v___x_3992_);
return v___x_3995_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3996_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10);
v___x_3997_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3);
v___x_3998_ = lean_array_push(v___x_3997_, v___x_3996_);
return v___x_3998_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_3999_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11);
v___x_4000_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1));
v___x_4001_ = lean_box(2);
v___x_4002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
lean_ctor_set(v___x_4002_, 1, v___x_4000_);
lean_ctor_set(v___x_4002_, 2, v___x_3999_);
return v___x_4002_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4003_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12);
v___x_4004_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4005_ = lean_array_push(v___x_4004_, v___x_4003_);
return v___x_4005_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14(void){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4006_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13);
v___x_4007_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_4008_ = lean_box(2);
v___x_4009_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
lean_ctor_set(v___x_4009_, 1, v___x_4007_);
lean_ctor_set(v___x_4009_, 2, v___x_4006_);
return v___x_4009_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15(void){
_start:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4010_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14);
v___x_4011_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4012_ = lean_array_push(v___x_4011_, v___x_4010_);
return v___x_4012_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4013_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15);
v___x_4014_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_4015_ = lean_box(2);
v___x_4016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
lean_ctor_set(v___x_4016_, 1, v___x_4014_);
lean_ctor_set(v___x_4016_, 2, v___x_4013_);
return v___x_4016_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4017_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16);
v___x_4018_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_4019_ = lean_array_push(v___x_4018_, v___x_4017_);
return v___x_4019_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4020_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17);
v___x_4021_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_4022_ = lean_box(2);
v___x_4023_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4022_);
lean_ctor_set(v___x_4023_, 1, v___x_4021_);
lean_ctor_set(v___x_4023_, 2, v___x_4020_);
return v___x_4023_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4024_;
}
}
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object* v_attrName_4025_, lean_object* v_decl_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4030_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_4031_ = l_Lean_MessageData_ofName(v_attrName_4025_);
v___x_4032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4030_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_4034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4032_);
lean_ctor_set(v___x_4034_, 1, v___x_4033_);
v___x_4035_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4034_, v___y_4027_, v___y_4028_);
return v___x_4035_;
}
}
LEAN_EXPORT void l_Lean_Parser_registerBuiltinParserAttribute___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_4025_ = stack[0].m_obj;
lean_object* v_decl_4026_ = stack[1].m_obj;
lean_object* v___y_4027_ = stack[2].m_obj;
lean_object* v___y_4028_ = stack[3].m_obj;
lean_object* v_res_4036_;
v_res_4036_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_4025_, v_decl_4026_, v___y_4027_, v___y_4028_);
stack->m_obj
 = v_res_4036_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object* v_attrName_4037_, lean_object* v_decl_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_4037_, v_decl_4038_, v___y_4039_, v___y_4040_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v_decl_4038_);
return v_res_4042_;
}
}
lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object* v_attrName_4043_, lean_object* v_catName_4044_, lean_object* v_declName_4045_, lean_object* v_stx_4046_, uint8_t v_kind_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_4043_, v_catName_4044_, v_declName_4045_, v_stx_4046_, v_kind_4047_, v___y_4048_, v___y_4049_);
return v___x_4051_;
}
}
LEAN_EXPORT void l_Lean_Parser_registerBuiltinParserAttribute___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_4043_ = stack[0].m_obj;
lean_object* v_catName_4044_ = stack[1].m_obj;
lean_object* v_declName_4045_ = stack[2].m_obj;
lean_object* v_stx_4046_ = stack[3].m_obj;
uint8_t v_kind_4047_ = stack[4].m_num;
lean_object* v___y_4048_ = stack[5].m_obj;
lean_object* v___y_4049_ = stack[6].m_obj;
lean_object* v_res_4052_;
v_res_4052_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_4043_, v_catName_4044_, v_declName_4045_, v_stx_4046_, v_kind_4047_, v___y_4048_, v___y_4049_);
stack->m_obj
 = v_res_4052_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object* v_attrName_4053_, lean_object* v_catName_4054_, lean_object* v_declName_4055_, lean_object* v_stx_4056_, lean_object* v_kind_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
uint8_t v_kind_boxed_4061_; lean_object* v_res_4062_; 
v_kind_boxed_4061_ = lean_unbox(v_kind_4057_);
v_res_4062_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_4053_, v_catName_4054_, v_declName_4055_, v_stx_4056_, v_kind_boxed_4061_, v___y_4058_, v___y_4059_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
return v_res_4062_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1(void){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__0));
v___x_4065_ = lean_mk_io_user_error(v___x_4064_);
return v___x_4065_;
}
}
lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* v_attrName_4068_, lean_object* v_declName_4069_, uint8_t v_behavior_4070_, lean_object* v_ref_4071_){
_start:
{
if (lean_obj_tag(v_declName_4069_) == 1)
{
lean_object* v_pre_4076_; 
v_pre_4076_ = lean_ctor_get(v_declName_4069_, 0);
if (lean_obj_tag(v_pre_4076_) == 1)
{
lean_object* v_pre_4077_; 
v_pre_4077_ = lean_ctor_get(v_pre_4076_, 0);
if (lean_obj_tag(v_pre_4077_) == 1)
{
lean_object* v_pre_4078_; 
v_pre_4078_ = lean_ctor_get(v_pre_4077_, 0);
if (lean_obj_tag(v_pre_4078_) == 1)
{
lean_object* v_pre_4079_; 
v_pre_4079_ = lean_ctor_get(v_pre_4078_, 0);
if (lean_obj_tag(v_pre_4079_) == 0)
{
lean_object* v_str_4080_; lean_object* v_str_4081_; lean_object* v_str_4082_; lean_object* v_str_4083_; lean_object* v___x_4084_; uint8_t v___x_4085_; 
v_str_4080_ = lean_ctor_get(v_declName_4069_, 1);
v_str_4081_ = lean_ctor_get(v_pre_4076_, 1);
v_str_4082_ = lean_ctor_get(v_pre_4077_, 1);
v_str_4083_ = lean_ctor_get(v_pre_4078_, 1);
v___x_4084_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_4085_ = lean_string_dec_eq(v_str_4083_, v___x_4084_);
if (v___x_4085_ == 0)
{
lean_dec_ref_known(v_declName_4069_, 2);
lean_dec(v_ref_4071_);
lean_dec(v_attrName_4068_);
goto v___jp_4073_;
}
else
{
lean_object* v___x_4086_; uint8_t v___x_4087_; 
v___x_4086_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_4087_ = lean_string_dec_eq(v_str_4082_, v___x_4086_);
if (v___x_4087_ == 0)
{
lean_dec_ref_known(v_declName_4069_, 2);
lean_dec(v_ref_4071_);
lean_dec(v_attrName_4068_);
goto v___jp_4073_;
}
else
{
lean_object* v___x_4088_; uint8_t v___x_4089_; 
v___x_4088_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__2));
v___x_4089_ = lean_string_dec_eq(v_str_4081_, v___x_4088_);
if (v___x_4089_ == 0)
{
lean_dec_ref_known(v_declName_4069_, 2);
lean_dec(v_ref_4071_);
lean_dec(v_attrName_4068_);
goto v___jp_4073_;
}
else
{
lean_object* v___f_4090_; lean_object* v___x_4091_; lean_object* v_catName_4092_; lean_object* v___f_4093_; lean_object* v___x_4094_; 
lean_inc_n(v_attrName_4068_, 2);
v___f_4090_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4090_, 0, v_attrName_4068_);
v___x_4091_ = lean_box(0);
lean_inc_ref(v_str_4080_);
v_catName_4092_ = l_Lean_Name_str___override(v___x_4091_, v_str_4080_);
lean_inc(v_catName_4092_);
v___f_4093_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed), 8, 2);
lean_closure_set(v___f_4093_, 0, v_attrName_4068_);
lean_closure_set(v___f_4093_, 1, v_catName_4092_);
v___x_4094_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_4092_, v_declName_4069_, v_behavior_4070_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v___x_4095_; uint8_t v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
lean_dec_ref_known(v___x_4094_, 1);
v___x_4095_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__3));
v___x_4096_ = 1;
v___x_4097_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4097_, 0, v_ref_4071_);
lean_ctor_set(v___x_4097_, 1, v_attrName_4068_);
lean_ctor_set(v___x_4097_, 2, v___x_4095_);
lean_ctor_set_uint8(v___x_4097_, sizeof(void*)*3, v___x_4096_);
v___x_4098_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
lean_ctor_set(v___x_4098_, 1, v___f_4093_);
lean_ctor_set(v___x_4098_, 2, v___f_4090_);
v___x_4099_ = l_Lean_registerBuiltinAttribute(v___x_4098_);
return v___x_4099_;
}
else
{
lean_dec_ref(v___f_4093_);
lean_dec_ref(v___f_4090_);
lean_dec(v_ref_4071_);
lean_dec(v_attrName_4068_);
return v___x_4094_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_declName_4069_, 2);
lean_dec(v_ref_4071_);
lean_dec(v_attrName_4068_);
goto v___jp_4073_;
}
}
else
{
lean_dec_ref_known(v_declName_4069_, 2);
lean_dec(v_ref_4071_);
lean_dec(v_attrName_4068_);
goto v___jp_4073_;
}
}
else
{
lean_dec_ref_known(v_declName_4069_, 2);
lean_dec(v_ref_4071_);
lean_dec(v_attrName_4068_);
goto v___jp_4073_;
}
}
else
{
lean_dec_ref_known(v_declName_4069_, 2);
lean_dec(v_ref_4071_);
lean_dec(v_attrName_4068_);
goto v___jp_4073_;
}
}
else
{
lean_dec(v_ref_4071_);
lean_dec(v_declName_4069_);
lean_dec(v_attrName_4068_);
goto v___jp_4073_;
}
v___jp_4073_:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4074_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___closed__1, &l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
v___x_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
return v___x_4075_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_registerBuiltinParserAttribute_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_4068_ = stack[0].m_obj;
lean_object* v_declName_4069_ = stack[1].m_obj;
uint8_t v_behavior_4070_ = stack[2].m_num;
lean_object* v_ref_4071_ = stack[3].m_obj;
lean_object* v_res_4100_;
v_res_4100_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_4068_, v_declName_4069_, v_behavior_4070_, v_ref_4071_);
stack->m_obj
 = v_res_4100_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* v_attrName_4101_, lean_object* v_declName_4102_, lean_object* v_behavior_4103_, lean_object* v_ref_4104_, lean_object* v_a_4105_){
_start:
{
uint8_t v_behavior_boxed_4106_; lean_object* v_res_4107_; 
v_behavior_boxed_4106_ = lean_unbox(v_behavior_4103_);
v_res_4107_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_4101_, v_declName_4102_, v_behavior_boxed_4106_, v_ref_4104_);
return v_res_4107_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object* v_kind_4108_, lean_object* v_x_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v___x_4113_; lean_object* v_env_4114_; lean_object* v_nextMacroScope_4115_; lean_object* v_ngen_4116_; lean_object* v_auxDeclNGen_4117_; lean_object* v_traceState_4118_; lean_object* v_recordedDeps_4119_; lean_object* v_messages_4120_; lean_object* v_infoState_4121_; lean_object* v_snapshotTasks_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4134_; 
v___x_4113_ = lean_st_ref_take(v___y_4111_);
v_env_4114_ = lean_ctor_get(v___x_4113_, 0);
v_nextMacroScope_4115_ = lean_ctor_get(v___x_4113_, 1);
v_ngen_4116_ = lean_ctor_get(v___x_4113_, 2);
v_auxDeclNGen_4117_ = lean_ctor_get(v___x_4113_, 3);
v_traceState_4118_ = lean_ctor_get(v___x_4113_, 4);
v_recordedDeps_4119_ = lean_ctor_get(v___x_4113_, 6);
v_messages_4120_ = lean_ctor_get(v___x_4113_, 7);
v_infoState_4121_ = lean_ctor_get(v___x_4113_, 8);
v_snapshotTasks_4122_ = lean_ctor_get(v___x_4113_, 9);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4134_ == 0)
{
lean_object* v_unused_4135_; 
v_unused_4135_ = lean_ctor_get(v___x_4113_, 5);
lean_dec(v_unused_4135_);
v___x_4124_ = v___x_4113_;
v_isShared_4125_ = v_isSharedCheck_4134_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_snapshotTasks_4122_);
lean_inc(v_infoState_4121_);
lean_inc(v_messages_4120_);
lean_inc(v_recordedDeps_4119_);
lean_inc(v_traceState_4118_);
lean_inc(v_auxDeclNGen_4117_);
lean_inc(v_ngen_4116_);
lean_inc(v_nextMacroScope_4115_);
lean_inc(v_env_4114_);
lean_dec(v___x_4113_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4134_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4130_; 
v___x_4126_ = lean_box(0);
v___x_4127_ = l_Lean_Parser_addSyntaxNodeKind(v_env_4114_, v_kind_4108_);
v___x_4128_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 5, v___x_4128_);
lean_ctor_set(v___x_4124_, 0, v___x_4127_);
v___x_4130_ = v___x_4124_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4127_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v_nextMacroScope_4115_);
lean_ctor_set(v_reuseFailAlloc_4133_, 2, v_ngen_4116_);
lean_ctor_set(v_reuseFailAlloc_4133_, 3, v_auxDeclNGen_4117_);
lean_ctor_set(v_reuseFailAlloc_4133_, 4, v_traceState_4118_);
lean_ctor_set(v_reuseFailAlloc_4133_, 5, v___x_4128_);
lean_ctor_set(v_reuseFailAlloc_4133_, 6, v_recordedDeps_4119_);
lean_ctor_set(v_reuseFailAlloc_4133_, 7, v_messages_4120_);
lean_ctor_set(v_reuseFailAlloc_4133_, 8, v_infoState_4121_);
lean_ctor_set(v_reuseFailAlloc_4133_, 9, v_snapshotTasks_4122_);
v___x_4130_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4131_ = lean_st_ref_put(v___y_4111_, v___x_4130_);
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4126_);
return v___x_4132_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_4108_ = stack[0].m_obj;
lean_object* v_x_4109_ = stack[1].m_obj;
lean_object* v___y_4110_ = stack[2].m_obj;
lean_object* v___y_4111_ = stack[3].m_obj;
lean_object* v_res_4136_;
v_res_4136_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_4108_, v_x_4109_, v___y_4110_, v___y_4111_);
stack->m_obj
 = v_res_4136_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object* v_kind_4137_, lean_object* v_x_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_4137_, v_x_4138_, v___y_4139_, v___y_4140_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
return v_res_4142_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_4143_, lean_object* v_keys_4144_, lean_object* v_vals_4145_, lean_object* v_i_4146_, lean_object* v_acc_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v___x_4151_; uint8_t v___x_4152_; 
v___x_4151_ = lean_array_get_size(v_keys_4144_);
v___x_4152_ = lean_nat_dec_lt(v_i_4146_, v___x_4151_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4153_; 
lean_dec(v_i_4146_);
lean_dec_ref(v_f_4143_);
v___x_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4153_, 0, v_acc_4147_);
return v___x_4153_;
}
else
{
lean_object* v_k_4154_; lean_object* v_v_4155_; lean_object* v___x_4156_; 
v_k_4154_ = lean_array_fget_borrowed(v_keys_4144_, v_i_4146_);
v_v_4155_ = lean_array_fget_borrowed(v_vals_4145_, v_i_4146_);
lean_inc_ref(v_f_4143_);
lean_inc(v___y_4149_);
lean_inc_ref(v___y_4148_);
lean_inc(v_v_4155_);
lean_inc(v_k_4154_);
v___x_4156_ = lean_apply_6(v_f_4143_, v_acc_4147_, v_k_4154_, v_v_4155_, v___y_4148_, v___y_4149_, lean_box(0));
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v___x_4156_, 1);
v___x_4158_ = lean_unsigned_to_nat(1u);
v___x_4159_ = lean_nat_add(v_i_4146_, v___x_4158_);
lean_dec(v_i_4146_);
v_i_4146_ = v___x_4159_;
v_acc_4147_ = v_a_4157_;
goto _start;
}
else
{
lean_dec(v_i_4146_);
lean_dec_ref(v_f_4143_);
return v___x_4156_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4143_ = stack[0].m_obj;
lean_object* v_keys_4144_ = stack[1].m_obj;
lean_object* v_vals_4145_ = stack[2].m_obj;
lean_object* v_i_4146_ = stack[3].m_obj;
lean_object* v_acc_4147_ = stack[4].m_obj;
lean_object* v___y_4148_ = stack[5].m_obj;
lean_object* v___y_4149_ = stack[6].m_obj;
lean_object* v_res_4161_;
v_res_4161_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4143_, v_keys_4144_, v_vals_4145_, v_i_4146_, v_acc_4147_, v___y_4148_, v___y_4149_);
stack->m_obj
 = v_res_4161_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_4162_, lean_object* v_keys_4163_, lean_object* v_vals_4164_, lean_object* v_i_4165_, lean_object* v_acc_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4162_, v_keys_4163_, v_vals_4164_, v_i_4165_, v_acc_4166_, v___y_4167_, v___y_4168_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec_ref(v_vals_4164_);
lean_dec_ref(v_keys_4163_);
return v_res_4170_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_4171_, lean_object* v_as_4172_, size_t v_i_4173_, size_t v_stop_4174_, lean_object* v_b_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_a_4180_; lean_object* v___y_4185_; uint8_t v___x_4187_; 
v___x_4187_ = lean_usize_dec_eq(v_i_4173_, v_stop_4174_);
if (v___x_4187_ == 0)
{
lean_object* v___x_4188_; 
v___x_4188_ = lean_array_uget_borrowed(v_as_4172_, v_i_4173_);
switch(lean_obj_tag(v___x_4188_))
{
case 0:
{
lean_object* v_key_4189_; lean_object* v_val_4190_; lean_object* v___x_4191_; 
v_key_4189_ = lean_ctor_get(v___x_4188_, 0);
v_val_4190_ = lean_ctor_get(v___x_4188_, 1);
lean_inc_ref(v_f_4171_);
lean_inc(v___y_4177_);
lean_inc_ref(v___y_4176_);
lean_inc(v_val_4190_);
lean_inc(v_key_4189_);
v___x_4191_ = lean_apply_6(v_f_4171_, v_b_4175_, v_key_4189_, v_val_4190_, v___y_4176_, v___y_4177_, lean_box(0));
v___y_4185_ = v___x_4191_;
goto v___jp_4184_;
}
case 1:
{
lean_object* v_node_4192_; lean_object* v___x_4193_; 
v_node_4192_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_node_4192_);
lean_inc_ref(v_f_4171_);
v___x_4193_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4171_, v_node_4192_, v_b_4175_, v___y_4176_, v___y_4177_);
v___y_4185_ = v___x_4193_;
goto v___jp_4184_;
}
default: 
{
v_a_4180_ = v_b_4175_;
goto v___jp_4179_;
}
}
}
else
{
lean_object* v___x_4194_; 
lean_dec_ref(v_f_4171_);
v___x_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4194_, 0, v_b_4175_);
return v___x_4194_;
}
v___jp_4179_:
{
size_t v___x_4181_; size_t v___x_4182_; 
v___x_4181_ = ((size_t)1ULL);
v___x_4182_ = lean_usize_add(v_i_4173_, v___x_4181_);
v_i_4173_ = v___x_4182_;
v_b_4175_ = v_a_4180_;
goto _start;
}
v___jp_4184_:
{
if (lean_obj_tag(v___y_4185_) == 0)
{
lean_object* v_a_4186_; 
v_a_4186_ = lean_ctor_get(v___y_4185_, 0);
lean_inc(v_a_4186_);
lean_dec_ref_known(v___y_4185_, 1);
v_a_4180_ = v_a_4186_;
goto v___jp_4179_;
}
else
{
lean_dec_ref(v_f_4171_);
return v___y_4185_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4171_ = stack[0].m_obj;
lean_object* v_as_4172_ = stack[1].m_obj;
size_t v_i_4173_ = stack[2].m_num;
size_t v_stop_4174_ = stack[3].m_num;
lean_object* v_b_4175_ = stack[4].m_obj;
lean_object* v___y_4176_ = stack[5].m_obj;
lean_object* v___y_4177_ = stack[6].m_obj;
lean_object* v_res_4195_;
v_res_4195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4171_, v_as_4172_, v_i_4173_, v_stop_4174_, v_b_4175_, v___y_4176_, v___y_4177_);
stack->m_obj
 = v_res_4195_;
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object* v_f_4196_, lean_object* v_x_4197_, lean_object* v_x_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
if (lean_obj_tag(v_x_4197_) == 0)
{
lean_object* v_es_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4215_; 
v_es_4202_ = lean_ctor_get(v_x_4197_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v_x_4197_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4204_ = v_x_4197_;
v_isShared_4205_ = v_isSharedCheck_4215_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_es_4202_);
lean_dec(v_x_4197_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4215_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; uint8_t v___x_4208_; 
v___x_4206_ = lean_unsigned_to_nat(0u);
v___x_4207_ = lean_array_get_size(v_es_4202_);
v___x_4208_ = lean_nat_dec_lt(v___x_4206_, v___x_4207_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4210_; 
lean_dec_ref(v_es_4202_);
lean_dec_ref(v_f_4196_);
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 0, v_x_4198_);
v___x_4210_ = v___x_4204_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_x_4198_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
else
{
size_t v___x_4212_; size_t v___x_4213_; lean_object* v___x_4214_; 
lean_del_object(v___x_4204_);
v___x_4212_ = ((size_t)0ULL);
v___x_4213_ = lean_usize_of_nat(v___x_4207_);
v___x_4214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4196_, v_es_4202_, v___x_4212_, v___x_4213_, v_x_4198_, v___y_4199_, v___y_4200_);
lean_dec_ref(v_es_4202_);
return v___x_4214_;
}
}
}
else
{
lean_object* v_ks_4216_; lean_object* v_vs_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v_ks_4216_ = lean_ctor_get(v_x_4197_, 0);
lean_inc_ref(v_ks_4216_);
v_vs_4217_ = lean_ctor_get(v_x_4197_, 1);
lean_inc_ref(v_vs_4217_);
lean_dec_ref_known(v_x_4197_, 2);
v___x_4218_ = lean_unsigned_to_nat(0u);
v___x_4219_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4196_, v_ks_4216_, v_vs_4217_, v___x_4218_, v_x_4198_, v___y_4199_, v___y_4200_);
lean_dec_ref(v_vs_4217_);
lean_dec_ref(v_ks_4216_);
return v___x_4219_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4196_ = stack[0].m_obj;
lean_object* v_x_4197_ = stack[1].m_obj;
lean_object* v_x_4198_ = stack[2].m_obj;
lean_object* v___y_4199_ = stack[3].m_obj;
lean_object* v___y_4200_ = stack[4].m_obj;
lean_object* v_res_4220_;
v_res_4220_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4196_, v_x_4197_, v_x_4198_, v___y_4199_, v___y_4200_);
stack->m_obj
 = v_res_4220_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_4221_, lean_object* v_x_4222_, lean_object* v_x_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4221_, v_x_4222_, v_x_4223_, v___y_4224_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_4228_, lean_object* v_as_4229_, lean_object* v_i_4230_, lean_object* v_stop_4231_, lean_object* v_b_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
size_t v_i_boxed_4236_; size_t v_stop_boxed_4237_; lean_object* v_res_4238_; 
v_i_boxed_4236_ = lean_unbox_usize(v_i_4230_);
lean_dec(v_i_4230_);
v_stop_boxed_4237_ = lean_unbox_usize(v_stop_4231_);
lean_dec(v_stop_4231_);
v_res_4238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4228_, v_as_4229_, v_i_boxed_4236_, v_stop_boxed_4237_, v_b_4232_, v___y_4233_, v___y_4234_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec_ref(v_as_4229_);
return v_res_4238_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object* v_f_4239_, lean_object* v_x_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v___x_4246_; 
lean_inc(v___y_4244_);
lean_inc_ref(v___y_4243_);
v___x_4246_ = lean_apply_5(v_f_4239_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, lean_box(0));
return v___x_4246_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4239_ = stack[0].m_obj;
lean_object* v_x_4240_ = stack[1].m_obj;
lean_object* v___y_4241_ = stack[2].m_obj;
lean_object* v___y_4242_ = stack[3].m_obj;
lean_object* v___y_4243_ = stack[4].m_obj;
lean_object* v___y_4244_ = stack[5].m_obj;
lean_object* v_res_4247_;
v_res_4247_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4239_, v_x_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
stack->m_obj
 = v_res_4247_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object* v_f_4248_, lean_object* v_x_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4248_, v_x_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
return v_res_4255_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object* v_map_4256_, lean_object* v_f_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v___f_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___f_4261_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4261_, 0, v_f_4257_);
v___x_4262_ = lean_box(0);
v___x_4263_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v___f_4261_, v_map_4256_, v___x_4262_, v___y_4258_, v___y_4259_);
return v___x_4263_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_4256_ = stack[0].m_obj;
lean_object* v_f_4257_ = stack[1].m_obj;
lean_object* v___y_4258_ = stack[2].m_obj;
lean_object* v___y_4259_ = stack[3].m_obj;
lean_object* v_res_4264_;
v_res_4264_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4256_, v_f_4257_, v___y_4258_, v___y_4259_);
stack->m_obj
 = v_res_4264_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object* v_map_4265_, lean_object* v_f_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4265_, v_f_4266_, v___y_4267_, v___y_4268_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
return v_res_4270_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4272_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0));
v___x_4273_ = l_Lean_stringToMessageData(v___x_4272_);
return v___x_4273_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4274_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_4275_ = l_Lean_stringToMessageData(v___x_4274_);
return v___x_4275_;
}
}
lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t v_attrKind_4276_, lean_object* v_declName_4277_, lean_object* v_as_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
if (lean_obj_tag(v_as_4278_) == 0)
{
lean_object* v___x_4282_; lean_object* v___x_4283_; 
lean_dec(v_declName_4277_);
v___x_4282_ = lean_box(0);
v___x_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4282_);
return v___x_4283_;
}
else
{
lean_object* v_head_4284_; lean_object* v_tail_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4316_; 
v_head_4284_ = lean_ctor_get(v_as_4278_, 0);
v_tail_4285_ = lean_ctor_get(v_as_4278_, 1);
v_isSharedCheck_4316_ = !lean_is_exclusive(v_as_4278_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4287_ = v_as_4278_;
v_isShared_4288_ = v_isSharedCheck_4316_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_tail_4285_);
lean_inc(v_head_4284_);
lean_dec(v_as_4278_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4316_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___y_4290_; uint8_t v___x_4292_; lean_object* v___x_4293_; 
v___x_4292_ = 0;
v___x_4293_ = l_Lean_Parser_addToken(v_head_4284_, v_attrKind_4276_, v___y_4279_, v___y_4280_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_del_object(v___x_4287_);
v___y_4290_ = v___x_4293_;
goto v___jp_4289_;
}
else
{
lean_object* v_a_4294_; uint8_t v___y_4296_; uint8_t v___x_4314_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4294_);
v___x_4314_ = l_Lean_Exception_isInterrupt(v_a_4294_);
if (v___x_4314_ == 0)
{
uint8_t v___x_4315_; 
lean_inc(v_a_4294_);
v___x_4315_ = l_Lean_Exception_isRuntime(v_a_4294_);
v___y_4296_ = v___x_4315_;
goto v___jp_4295_;
}
else
{
v___y_4296_ = v___x_4314_;
goto v___jp_4295_;
}
v___jp_4295_:
{
if (v___y_4296_ == 0)
{
if (lean_obj_tag(v_a_4294_) == 0)
{
lean_object* v_msg_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4312_; 
lean_dec_ref_known(v___x_4293_, 1);
v_msg_4297_ = lean_ctor_get(v_a_4294_, 1);
v_isSharedCheck_4312_ = !lean_is_exclusive(v_a_4294_);
if (v_isSharedCheck_4312_ == 0)
{
lean_object* v_unused_4313_; 
v_unused_4313_ = lean_ctor_get(v_a_4294_, 0);
lean_dec(v_unused_4313_);
v___x_4299_ = v_a_4294_;
v_isShared_4300_ = v_isSharedCheck_4312_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_msg_4297_);
lean_dec(v_a_4294_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4312_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4304_; 
v___x_4301_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1);
lean_inc(v_declName_4277_);
v___x_4302_ = l_Lean_MessageData_ofConstName(v_declName_4277_, v___x_4292_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set_tag(v___x_4299_, 7);
lean_ctor_set(v___x_4299_, 1, v___x_4302_);
lean_ctor_set(v___x_4299_, 0, v___x_4301_);
v___x_4304_ = v___x_4299_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4301_);
lean_ctor_set(v_reuseFailAlloc_4311_, 1, v___x_4302_);
v___x_4304_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4305_; lean_object* v___x_4307_; 
v___x_4305_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2);
if (v_isShared_4288_ == 0)
{
lean_ctor_set_tag(v___x_4287_, 7);
lean_ctor_set(v___x_4287_, 1, v___x_4305_);
lean_ctor_set(v___x_4287_, 0, v___x_4304_);
v___x_4307_ = v___x_4287_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4304_);
lean_ctor_set(v_reuseFailAlloc_4310_, 1, v___x_4305_);
v___x_4307_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
lean_ctor_set(v___x_4308_, 1, v_msg_4297_);
v___x_4309_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4308_, v___y_4279_, v___y_4280_);
v___y_4290_ = v___x_4309_;
goto v___jp_4289_;
}
}
}
}
else
{
lean_dec(v_a_4294_);
lean_del_object(v___x_4287_);
v___y_4290_ = v___x_4293_;
goto v___jp_4289_;
}
}
else
{
lean_dec(v_a_4294_);
lean_del_object(v___x_4287_);
v___y_4290_ = v___x_4293_;
goto v___jp_4289_;
}
}
}
v___jp_4289_:
{
if (lean_obj_tag(v___y_4290_) == 0)
{
lean_dec_ref_known(v___y_4290_, 1);
v_as_4278_ = v_tail_4285_;
goto _start;
}
else
{
lean_dec(v_tail_4285_);
lean_dec(v_declName_4277_);
return v___y_4290_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_attrKind_4276_ = stack[0].m_num;
lean_object* v_declName_4277_ = stack[1].m_obj;
lean_object* v_as_4278_ = stack[2].m_obj;
lean_object* v___y_4279_ = stack[3].m_obj;
lean_object* v___y_4280_ = stack[4].m_obj;
lean_object* v_res_4317_;
v_res_4317_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4276_, v_declName_4277_, v_as_4278_, v___y_4279_, v___y_4280_);
stack->m_obj
 = v_res_4317_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object* v_attrKind_4318_, lean_object* v_declName_4319_, lean_object* v_as_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
uint8_t v_attrKind_boxed_4324_; lean_object* v_res_4325_; 
v_attrKind_boxed_4324_ = lean_unbox(v_attrKind_4318_);
v_res_4325_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_boxed_4324_, v_declName_4319_, v_as_4320_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
return v_res_4325_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object* v_catName_4327_, lean_object* v_declName_4328_, lean_object* v_stx_4329_, uint8_t v_attrKind_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_){
_start:
{
lean_object* v___f_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___f_4334_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0));
v___x_4335_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4336_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4329_, v_a_4331_, v_a_4332_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4338_; lean_object* v_env_4339_; lean_object* v___x_4340_; lean_object* v_ext_4341_; lean_object* v_toEnvExtension_4342_; lean_object* v_asyncMode_4343_; uint8_t v___x_4344_; lean_object* v___x_4345_; lean_object* v_categories_4346_; lean_object* v___x_4347_; lean_object* v_env_4348_; lean_object* v_ref_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4337_);
lean_dec_ref_known(v___x_4336_, 1);
v___x_4338_ = lean_st_ref_get(v_a_4332_);
v_env_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc_ref(v_env_4339_);
lean_dec(v___x_4338_);
v___x_4340_ = l_Lean_Parser_parserExtension;
v_ext_4341_ = lean_ctor_get(v___x_4340_, 1);
v_toEnvExtension_4342_ = lean_ctor_get(v_ext_4341_, 0);
v_asyncMode_4343_ = lean_ctor_get(v_toEnvExtension_4342_, 2);
v___x_4344_ = 0;
v___x_4345_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4335_, v___x_4340_, v_env_4339_, v_asyncMode_4343_, v___x_4344_);
v_categories_4346_ = lean_ctor_get(v___x_4345_, 2);
lean_inc_ref_n(v_categories_4346_, 2);
lean_dec(v___x_4345_);
v___x_4347_ = lean_st_ref_get(v_a_4332_);
v_env_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc_ref(v_env_4348_);
lean_dec(v___x_4347_);
v_ref_4349_ = lean_ctor_get(v_a_4331_, 2);
v___x_4350_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4331_);
v___x_4351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4351_, 0, v_env_4348_);
lean_ctor_set(v___x_4351_, 1, v___x_4350_);
lean_inc(v_declName_4328_);
v___x_4352_ = l_Lean_Parser_mkParserOfConstant(v_categories_4346_, v_declName_4328_, v___x_4351_);
lean_dec_ref_known(v___x_4351_, 2);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v_snd_4354_; lean_object* v_info_4355_; lean_object* v_fst_4356_; lean_object* v_collectTokens_4357_; lean_object* v_collectKinds_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
v_snd_4354_ = lean_ctor_get(v_a_4353_, 1);
lean_inc(v_snd_4354_);
v_info_4355_ = lean_ctor_get(v_snd_4354_, 0);
v_fst_4356_ = lean_ctor_get(v_a_4353_, 0);
lean_inc(v_fst_4356_);
lean_dec(v_a_4353_);
v_collectTokens_4357_ = lean_ctor_get(v_info_4355_, 0);
v_collectKinds_4358_ = lean_ctor_get(v_info_4355_, 1);
v___x_4359_ = lean_box(0);
lean_inc_ref(v_collectTokens_4357_);
v___x_4360_ = lean_apply_1(v_collectTokens_4357_, v___x_4359_);
lean_inc(v_declName_4328_);
v___x_4361_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4330_, v_declName_4328_, v___x_4360_, v_a_4331_, v_a_4332_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
lean_dec_ref_known(v___x_4361_, 1);
v___x_4362_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
lean_inc_ref(v_collectKinds_4358_);
v___x_4363_ = lean_apply_1(v_collectKinds_4358_, v___x_4362_);
v___x_4364_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v___x_4363_, v___f_4334_, v_a_4331_, v_a_4332_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v___x_4365_; uint8_t v___x_4366_; uint8_t v___x_4367_; lean_object* v___x_4368_; 
lean_dec_ref_known(v___x_4364_, 1);
lean_inc(v_a_4337_);
lean_inc(v_snd_4354_);
lean_inc_n(v_declName_4328_, 2);
lean_inc_n(v_catName_4327_, 2);
v___x_4365_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_4365_, 0, v_catName_4327_);
lean_ctor_set(v___x_4365_, 1, v_declName_4328_);
lean_ctor_set(v___x_4365_, 2, v_snd_4354_);
lean_ctor_set(v___x_4365_, 3, v_a_4337_);
v___x_4366_ = lean_unbox(v_fst_4356_);
lean_ctor_set_uint8(v___x_4365_, sizeof(void*)*4, v___x_4366_);
v___x_4367_ = lean_unbox(v_fst_4356_);
lean_dec(v_fst_4356_);
v___x_4368_ = l_Lean_Parser_addParser(v_categories_4346_, v_catName_4327_, v_declName_4328_, v___x_4367_, v_snd_4354_, v_a_4337_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4378_; 
lean_dec_ref_known(v___x_4365_, 4);
lean_dec(v_declName_4328_);
lean_dec(v_catName_4327_);
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4371_ = v___x_4368_;
v_isShared_4372_ = v_isSharedCheck_4378_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4368_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4378_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4374_; 
if (v_isShared_4372_ == 0)
{
lean_ctor_set_tag(v___x_4371_, 3);
v___x_4374_ = v___x_4371_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4369_);
v___x_4374_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4375_ = l_Lean_MessageData_ofFormat(v___x_4374_);
v___x_4376_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4375_, v_a_4331_, v_a_4332_);
return v___x_4376_;
}
}
}
else
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
lean_dec_ref_known(v___x_4368_, 1);
v___x_4379_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_4340_, v___x_4365_, v_attrKind_4330_, v_a_4331_, v_a_4332_);
lean_dec_ref(v___x_4379_);
v___x_4380_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4327_, v_declName_4328_, v___x_4344_, v_a_4331_, v_a_4332_);
return v___x_4380_;
}
}
else
{
lean_dec(v_fst_4356_);
lean_dec(v_snd_4354_);
lean_dec_ref(v_categories_4346_);
lean_dec(v_a_4337_);
lean_dec(v_declName_4328_);
lean_dec(v_catName_4327_);
return v___x_4364_;
}
}
else
{
lean_dec(v_fst_4356_);
lean_dec(v_snd_4354_);
lean_dec_ref(v_categories_4346_);
lean_dec(v_a_4337_);
lean_dec(v_declName_4328_);
lean_dec(v_catName_4327_);
return v___x_4361_;
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4392_; 
lean_dec_ref(v_categories_4346_);
lean_dec(v_a_4337_);
lean_dec(v_declName_4328_);
lean_dec(v_catName_4327_);
v_a_4381_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4383_ = v___x_4352_;
v_isShared_4384_ = v_isSharedCheck_4392_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4352_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4392_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4390_; 
v___x_4385_ = lean_io_error_to_string(v_a_4381_);
v___x_4386_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
v___x_4387_ = l_Lean_MessageData_ofFormat(v___x_4386_);
lean_inc(v_ref_4349_);
v___x_4388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4388_, 0, v_ref_4349_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 0, v___x_4388_);
v___x_4390_ = v___x_4383_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4388_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_dec(v_declName_4328_);
lean_dec(v_catName_4327_);
v_a_4393_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4336_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4336_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_catName_4327_ = stack[0].m_obj;
lean_object* v_declName_4328_ = stack[1].m_obj;
lean_object* v_stx_4329_ = stack[2].m_obj;
uint8_t v_attrKind_4330_ = stack[3].m_num;
lean_object* v_a_4331_ = stack[4].m_obj;
lean_object* v_a_4332_ = stack[5].m_obj;
lean_object* v_res_4401_;
v_res_4401_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4327_, v_declName_4328_, v_stx_4329_, v_attrKind_4330_, v_a_4331_, v_a_4332_);
stack->m_obj
 = v_res_4401_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object* v_catName_4402_, lean_object* v_declName_4403_, lean_object* v_stx_4404_, lean_object* v_attrKind_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_){
_start:
{
uint8_t v_attrKind_boxed_4409_; lean_object* v_res_4410_; 
v_attrKind_boxed_4409_ = lean_unbox(v_attrKind_4405_);
v_res_4410_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4402_, v_declName_4403_, v_stx_4404_, v_attrKind_boxed_4409_, v_a_4406_, v_a_4407_);
lean_dec(v_a_4407_);
lean_dec_ref(v_a_4406_);
return v_res_4410_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* v___attrName_4411_, lean_object* v_catName_4412_, lean_object* v_declName_4413_, lean_object* v_stx_4414_, uint8_t v_attrKind_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_){
_start:
{
lean_object* v___x_4419_; 
v___x_4419_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4412_, v_declName_4413_, v_stx_4414_, v_attrKind_4415_, v_a_4416_, v_a_4417_);
return v___x_4419_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_0interp(lean_interpreter_value* stack)
{
lean_object* v___attrName_4411_ = stack[0].m_obj;
lean_object* v_catName_4412_ = stack[1].m_obj;
lean_object* v_declName_4413_ = stack[2].m_obj;
lean_object* v_stx_4414_ = stack[3].m_obj;
uint8_t v_attrKind_4415_ = stack[4].m_num;
lean_object* v_a_4416_ = stack[5].m_obj;
lean_object* v_a_4417_ = stack[6].m_obj;
lean_object* v_res_4420_;
v_res_4420_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4411_, v_catName_4412_, v_declName_4413_, v_stx_4414_, v_attrKind_4415_, v_a_4416_, v_a_4417_);
stack->m_obj
 = v_res_4420_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* v___attrName_4421_, lean_object* v_catName_4422_, lean_object* v_declName_4423_, lean_object* v_stx_4424_, lean_object* v_attrKind_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_){
_start:
{
uint8_t v_attrKind_boxed_4429_; lean_object* v_res_4430_; 
v_attrKind_boxed_4429_ = lean_unbox(v_attrKind_4425_);
v_res_4430_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4421_, v_catName_4422_, v_declName_4423_, v_stx_4424_, v_attrKind_boxed_4429_, v_a_4426_, v_a_4427_);
lean_dec(v_a_4427_);
lean_dec_ref(v_a_4426_);
lean_dec(v___attrName_4421_);
return v_res_4430_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object* v_00_u03b2_4431_, lean_object* v_map_4432_, lean_object* v_f_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v___x_4437_; 
v___x_4437_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4432_, v_f_4433_, v___y_4434_, v___y_4435_);
return v___x_4437_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_4432_ = stack[1].m_obj;
lean_object* v_f_4433_ = stack[2].m_obj;
lean_object* v___y_4434_ = stack[3].m_obj;
lean_object* v___y_4435_ = stack[4].m_obj;
lean_object* v_res_4438_;
v_res_4438_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_box(0), v_map_4432_, v_f_4433_, v___y_4434_, v___y_4435_);
stack->m_obj
 = v_res_4438_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b2_4439_, lean_object* v_map_4440_, lean_object* v_f_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(v_00_u03b2_4439_, v_map_4440_, v_f_4441_, v___y_4442_, v___y_4443_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
return v_res_4445_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object* v_map_4446_, lean_object* v_f_4447_, lean_object* v_init_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v___x_4452_; 
v___x_4452_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4447_, v_map_4446_, v_init_4448_, v___y_4449_, v___y_4450_);
return v___x_4452_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_4446_ = stack[0].m_obj;
lean_object* v_f_4447_ = stack[1].m_obj;
lean_object* v_init_4448_ = stack[2].m_obj;
lean_object* v___y_4449_ = stack[3].m_obj;
lean_object* v___y_4450_ = stack[4].m_obj;
lean_object* v_res_4453_;
v_res_4453_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4446_, v_f_4447_, v_init_4448_, v___y_4449_, v___y_4450_);
stack->m_obj
 = v_res_4453_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object* v_map_4454_, lean_object* v_f_4455_, lean_object* v_init_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4454_, v_f_4455_, v_init_4456_, v___y_4457_, v___y_4458_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
return v_res_4460_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object* v_00_u03c3_4461_, lean_object* v_00_u03b2_4462_, lean_object* v_map_4463_, lean_object* v_f_4464_, lean_object* v_init_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v___x_4469_; 
v___x_4469_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4464_, v_map_4463_, v_init_4465_, v___y_4466_, v___y_4467_);
return v___x_4469_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_4463_ = stack[2].m_obj;
lean_object* v_f_4464_ = stack[3].m_obj;
lean_object* v_init_4465_ = stack[4].m_obj;
lean_object* v___y_4466_ = stack[5].m_obj;
lean_object* v___y_4467_ = stack[6].m_obj;
lean_object* v_res_4470_;
v_res_4470_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_box(0), lean_box(0), v_map_4463_, v_f_4464_, v_init_4465_, v___y_4466_, v___y_4467_);
stack->m_obj
 = v_res_4470_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object* v_00_u03c3_4471_, lean_object* v_00_u03b2_4472_, lean_object* v_map_4473_, lean_object* v_f_4474_, lean_object* v_init_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(v_00_u03c3_4471_, v_00_u03b2_4472_, v_map_4473_, v_f_4474_, v_init_4475_, v___y_4476_, v___y_4477_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
return v_res_4479_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_4480_, lean_object* v_00_u03b1_4481_, lean_object* v_00_u03b2_4482_, lean_object* v_f_4483_, lean_object* v_x_4484_, lean_object* v_x_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_){
_start:
{
lean_object* v___x_4489_; 
v___x_4489_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4483_, v_x_4484_, v_x_4485_, v___y_4486_, v___y_4487_);
return v___x_4489_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4483_ = stack[3].m_obj;
lean_object* v_x_4484_ = stack[4].m_obj;
lean_object* v_x_4485_ = stack[5].m_obj;
lean_object* v___y_4486_ = stack[6].m_obj;
lean_object* v___y_4487_ = stack[7].m_obj;
lean_object* v_res_4490_;
v_res_4490_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_box(0), lean_box(0), lean_box(0), v_f_4483_, v_x_4484_, v_x_4485_, v___y_4486_, v___y_4487_);
stack->m_obj
 = v_res_4490_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03c3_4491_, lean_object* v_00_u03b1_4492_, lean_object* v_00_u03b2_4493_, lean_object* v_f_4494_, lean_object* v_x_4495_, lean_object* v_x_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(v_00_u03c3_4491_, v_00_u03b1_4492_, v_00_u03b2_4493_, v_f_4494_, v_x_4495_, v_x_4496_, v___y_4497_, v___y_4498_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
return v_res_4500_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4501_, lean_object* v_00_u03b2_4502_, lean_object* v_00_u03c3_4503_, lean_object* v_f_4504_, lean_object* v_as_4505_, size_t v_i_4506_, size_t v_stop_4507_, lean_object* v_b_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v___x_4512_; 
v___x_4512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4504_, v_as_4505_, v_i_4506_, v_stop_4507_, v_b_4508_, v___y_4509_, v___y_4510_);
return v___x_4512_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4504_ = stack[3].m_obj;
lean_object* v_as_4505_ = stack[4].m_obj;
size_t v_i_4506_ = stack[5].m_num;
size_t v_stop_4507_ = stack[6].m_num;
lean_object* v_b_4508_ = stack[7].m_obj;
lean_object* v___y_4509_ = stack[8].m_obj;
lean_object* v___y_4510_ = stack[9].m_obj;
lean_object* v_res_4513_;
v_res_4513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_box(0), lean_box(0), lean_box(0), v_f_4504_, v_as_4505_, v_i_4506_, v_stop_4507_, v_b_4508_, v___y_4509_, v___y_4510_);
stack->m_obj
 = v_res_4513_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4514_, lean_object* v_00_u03b2_4515_, lean_object* v_00_u03c3_4516_, lean_object* v_f_4517_, lean_object* v_as_4518_, lean_object* v_i_4519_, lean_object* v_stop_4520_, lean_object* v_b_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
size_t v_i_boxed_4525_; size_t v_stop_boxed_4526_; lean_object* v_res_4527_; 
v_i_boxed_4525_ = lean_unbox_usize(v_i_4519_);
lean_dec(v_i_4519_);
v_stop_boxed_4526_ = lean_unbox_usize(v_stop_4520_);
lean_dec(v_stop_4520_);
v_res_4527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4514_, v_00_u03b2_4515_, v_00_u03c3_4516_, v_f_4517_, v_as_4518_, v_i_boxed_4525_, v_stop_boxed_4526_, v_b_4521_, v___y_4522_, v___y_4523_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec_ref(v_as_4518_);
return v_res_4527_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_4528_, lean_object* v_00_u03b1_4529_, lean_object* v_00_u03b2_4530_, lean_object* v_f_4531_, lean_object* v_keys_4532_, lean_object* v_vals_4533_, lean_object* v_heq_4534_, lean_object* v_i_4535_, lean_object* v_acc_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4531_, v_keys_4532_, v_vals_4533_, v_i_4535_, v_acc_4536_, v___y_4537_, v___y_4538_);
return v___x_4540_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4531_ = stack[3].m_obj;
lean_object* v_keys_4532_ = stack[4].m_obj;
lean_object* v_vals_4533_ = stack[5].m_obj;
lean_object* v_i_4535_ = stack[7].m_obj;
lean_object* v_acc_4536_ = stack[8].m_obj;
lean_object* v___y_4537_ = stack[9].m_obj;
lean_object* v___y_4538_ = stack[10].m_obj;
lean_object* v_res_4541_;
v_res_4541_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_box(0), lean_box(0), lean_box(0), v_f_4531_, v_keys_4532_, v_vals_4533_, lean_box(0), v_i_4535_, v_acc_4536_, v___y_4537_, v___y_4538_);
stack->m_obj
 = v_res_4541_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_4542_, lean_object* v_00_u03b1_4543_, lean_object* v_00_u03b2_4544_, lean_object* v_f_4545_, lean_object* v_keys_4546_, lean_object* v_vals_4547_, lean_object* v_heq_4548_, lean_object* v_i_4549_, lean_object* v_acc_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4542_, v_00_u03b1_4543_, v_00_u03b2_4544_, v_f_4545_, v_keys_4546_, v_vals_4547_, v_heq_4548_, v_i_4549_, v_acc_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec_ref(v_vals_4547_);
lean_dec_ref(v_keys_4546_);
return v_res_4554_;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___auto__1(void){
_start:
{
lean_object* v___x_4555_; 
v___x_4555_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4555_;
}
}
lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object* v_catName_4556_, lean_object* v_declName_4557_, lean_object* v_stx_4558_, uint8_t v_attrKind_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v___x_4563_; 
v___x_4563_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4556_, v_declName_4557_, v_stx_4558_, v_attrKind_4559_, v___y_4560_, v___y_4561_);
return v___x_4563_;
}
}
LEAN_EXPORT void l_Lean_Parser_mkParserAttributeImpl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_catName_4556_ = stack[0].m_obj;
lean_object* v_declName_4557_ = stack[1].m_obj;
lean_object* v_stx_4558_ = stack[2].m_obj;
uint8_t v_attrKind_4559_ = stack[3].m_num;
lean_object* v___y_4560_ = stack[4].m_obj;
lean_object* v___y_4561_ = stack[5].m_obj;
lean_object* v_res_4564_;
v_res_4564_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4556_, v_declName_4557_, v_stx_4558_, v_attrKind_4559_, v___y_4560_, v___y_4561_);
stack->m_obj
 = v_res_4564_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object* v_catName_4565_, lean_object* v_declName_4566_, lean_object* v_stx_4567_, lean_object* v_attrKind_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
uint8_t v_attrKind_boxed_4572_; lean_object* v_res_4573_; 
v_attrKind_boxed_4572_ = lean_unbox(v_attrKind_4568_);
v_res_4573_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4565_, v_declName_4566_, v_stx_4567_, v_attrKind_boxed_4572_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* v_attrName_4575_, lean_object* v_catName_4576_, lean_object* v_ref_4577_){
_start:
{
lean_object* v___f_4578_; lean_object* v___f_4579_; lean_object* v___x_4580_; uint8_t v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___f_4578_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4578_, 0, v_catName_4576_);
lean_inc(v_attrName_4575_);
v___f_4579_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4579_, 0, v_attrName_4575_);
v___x_4580_ = ((lean_object*)(l_Lean_Parser_mkParserAttributeImpl___closed__0));
v___x_4581_ = 1;
v___x_4582_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4582_, 0, v_ref_4577_);
lean_ctor_set(v___x_4582_, 1, v_attrName_4575_);
lean_ctor_set(v___x_4582_, 2, v___x_4580_);
lean_ctor_set_uint8(v___x_4582_, sizeof(void*)*3, v___x_4581_);
v___x_4583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
lean_ctor_set(v___x_4583_, 1, v___f_4578_);
lean_ctor_set(v___x_4583_, 2, v___f_4579_);
return v___x_4583_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4584_; 
v___x_4584_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4584_;
}
}
lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* v_attrName_4585_, lean_object* v_catName_4586_, lean_object* v_ref_4587_){
_start:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4589_ = l_Lean_Parser_mkParserAttributeImpl(v_attrName_4585_, v_catName_4586_, v_ref_4587_);
v___x_4590_ = l_Lean_registerBuiltinAttribute(v___x_4589_);
return v___x_4590_;
}
}
LEAN_EXPORT void l_Lean_Parser_registerBuiltinDynamicParserAttribute_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_4585_ = stack[0].m_obj;
lean_object* v_catName_4586_ = stack[1].m_obj;
lean_object* v_ref_4587_ = stack[2].m_obj;
lean_object* v_res_4591_;
v_res_4591_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4585_, v_catName_4586_, v_ref_4587_);
stack->m_obj
 = v_res_4591_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object* v_attrName_4592_, lean_object* v_catName_4593_, lean_object* v_ref_4594_, lean_object* v_a_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4592_, v_catName_4593_, v_ref_4594_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object* v_ref_4600_, lean_object* v_args_4601_){
_start:
{
if (lean_obj_tag(v_args_4601_) == 1)
{
lean_object* v_head_4604_; 
v_head_4604_ = lean_ctor_get(v_args_4601_, 0);
lean_inc(v_head_4604_);
if (lean_obj_tag(v_head_4604_) == 2)
{
lean_object* v_tail_4605_; 
v_tail_4605_ = lean_ctor_get(v_args_4601_, 1);
lean_inc(v_tail_4605_);
lean_dec_ref_known(v_args_4601_, 2);
if (lean_obj_tag(v_tail_4605_) == 1)
{
lean_object* v_head_4606_; 
v_head_4606_ = lean_ctor_get(v_tail_4605_, 0);
lean_inc(v_head_4606_);
if (lean_obj_tag(v_head_4606_) == 2)
{
lean_object* v_tail_4607_; 
v_tail_4607_ = lean_ctor_get(v_tail_4605_, 1);
lean_inc(v_tail_4607_);
lean_dec_ref_known(v_tail_4605_, 2);
if (lean_obj_tag(v_tail_4607_) == 0)
{
lean_object* v_v_4608_; lean_object* v_v_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4617_; 
v_v_4608_ = lean_ctor_get(v_head_4604_, 0);
lean_inc(v_v_4608_);
lean_dec_ref_known(v_head_4604_, 1);
v_v_4609_ = lean_ctor_get(v_head_4606_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v_head_4606_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4611_ = v_head_4606_;
v_isShared_4612_ = v_isSharedCheck_4617_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_v_4609_);
lean_dec(v_head_4606_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4617_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4613_; lean_object* v___x_4615_; 
v___x_4613_ = l_Lean_Parser_mkParserAttributeImpl(v_v_4608_, v_v_4609_, v_ref_4600_);
if (v_isShared_4612_ == 0)
{
lean_ctor_set_tag(v___x_4611_, 1);
lean_ctor_set(v___x_4611_, 0, v___x_4613_);
v___x_4615_ = v___x_4611_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4613_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
else
{
lean_dec_ref_known(v_head_4606_, 1);
lean_dec(v_tail_4607_);
lean_dec_ref_known(v_head_4604_, 1);
lean_dec(v_ref_4600_);
goto v___jp_4602_;
}
}
else
{
lean_dec(v_head_4606_);
lean_dec_ref_known(v_tail_4605_, 2);
lean_dec_ref_known(v_head_4604_, 1);
lean_dec(v_ref_4600_);
goto v___jp_4602_;
}
}
else
{
lean_dec(v_tail_4605_);
lean_dec_ref_known(v_head_4604_, 1);
lean_dec(v_ref_4600_);
goto v___jp_4602_;
}
}
else
{
lean_dec_ref_known(v_args_4601_, 2);
lean_dec(v_head_4604_);
lean_dec(v_ref_4600_);
goto v___jp_4602_;
}
}
else
{
lean_dec(v_args_4601_);
lean_dec(v_ref_4600_);
goto v___jp_4602_;
}
v___jp_4602_:
{
lean_object* v___x_4603_; 
v___x_4603_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
return v___x_4603_;
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___f_4623_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4624_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4625_ = l_Lean_registerAttributeImplBuilder(v___x_4624_, v___f_4623_);
return v___x_4625_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4626_;
v_res_4626_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4626_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object* v_a_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
return v_res_4628_;
}
}
static lean_object* _init_l_Lean_Parser_registerParserCategory___auto__1(void){
_start:
{
lean_object* v___x_4629_; 
v___x_4629_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4629_;
}
}
lean_object* l_Lean_Parser_registerParserCategory(lean_object* v_env_4630_, lean_object* v_attrName_4631_, lean_object* v_catName_4632_, uint8_t v_behavior_4633_, lean_object* v_ref_4634_){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
lean_inc(v_ref_4634_);
lean_inc(v_catName_4632_);
v___x_4636_ = l_Lean_Parser_addParserCategory(v_env_4630_, v_catName_4632_, v_ref_4634_, v_behavior_4633_);
v___x_4637_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_4636_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4651_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4640_ = v___x_4637_;
v_isShared_4641_ = v_isSharedCheck_4651_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4637_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4651_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4642_; lean_object* v___x_4644_; 
v___x_4642_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
if (v_isShared_4641_ == 0)
{
lean_ctor_set_tag(v___x_4640_, 2);
lean_ctor_set(v___x_4640_, 0, v_attrName_4631_);
v___x_4644_ = v___x_4640_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_attrName_4631_);
v___x_4644_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4645_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4645_, 0, v_catName_4632_);
v___x_4646_ = lean_box(0);
v___x_4647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4645_);
lean_ctor_set(v___x_4647_, 1, v___x_4646_);
v___x_4648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4644_);
lean_ctor_set(v___x_4648_, 1, v___x_4647_);
v___x_4649_ = l_Lean_registerAttributeOfBuilder(v_a_4638_, v___x_4642_, v_ref_4634_, v___x_4648_);
return v___x_4649_;
}
}
}
else
{
lean_dec(v_ref_4634_);
lean_dec(v_catName_4632_);
lean_dec(v_attrName_4631_);
return v___x_4637_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_registerParserCategory_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_4630_ = stack[0].m_obj;
lean_object* v_attrName_4631_ = stack[1].m_obj;
lean_object* v_catName_4632_ = stack[2].m_obj;
uint8_t v_behavior_4633_ = stack[3].m_num;
lean_object* v_ref_4634_ = stack[4].m_obj;
lean_object* v_res_4652_;
v_res_4652_ = l_Lean_Parser_registerParserCategory(v_env_4630_, v_attrName_4631_, v_catName_4632_, v_behavior_4633_, v_ref_4634_);
stack->m_obj
 = v_res_4652_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* v_env_4653_, lean_object* v_attrName_4654_, lean_object* v_catName_4655_, lean_object* v_behavior_4656_, lean_object* v_ref_4657_, lean_object* v_a_4658_){
_start:
{
uint8_t v_behavior_boxed_4659_; lean_object* v_res_4660_; 
v_behavior_boxed_4659_ = lean_unbox(v_behavior_4656_);
v_res_4660_ = l_Lean_Parser_registerParserCategory(v_env_4653_, v_attrName_4654_, v_catName_4655_, v_behavior_boxed_4659_, v_ref_4657_);
return v_res_4660_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; uint8_t v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4683_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4684_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4685_ = 0;
v___x_4686_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4687_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4683_, v___x_4684_, v___x_4685_, v___x_4686_);
return v___x_4687_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4688_;
v_res_4688_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4688_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object* v_a_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
return v_res_4690_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4696_ = lean_unsigned_to_nat(3431364690u);
v___x_4697_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4698_ = l_Lean_Name_num___override(v___x_4697_, v___x_4696_);
return v___x_4698_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4699_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4700_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4701_ = l_Lean_Name_str___override(v___x_4700_, v___x_4699_);
return v___x_4701_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4702_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4703_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4704_ = l_Lean_Name_str___override(v___x_4703_, v___x_4702_);
return v___x_4704_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4705_ = lean_unsigned_to_nat(2u);
v___x_4706_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4707_ = l_Lean_Name_num___override(v___x_4706_, v___x_4705_);
return v___x_4707_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4709_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4710_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4711_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4712_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4709_, v___x_4710_, v___x_4711_);
return v___x_4712_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4713_;
v_res_4713_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4713_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object* v_a_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
return v_res_4715_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4725_ = lean_unsigned_to_nat(2342493449u);
v___x_4726_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4727_ = l_Lean_Name_num___override(v___x_4726_, v___x_4725_);
return v___x_4727_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4728_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4729_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4730_ = l_Lean_Name_str___override(v___x_4729_, v___x_4728_);
return v___x_4730_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4731_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4732_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4733_ = l_Lean_Name_str___override(v___x_4732_, v___x_4731_);
return v___x_4733_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
v___x_4734_ = lean_unsigned_to_nat(2u);
v___x_4735_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4736_ = l_Lean_Name_num___override(v___x_4735_, v___x_4734_);
return v___x_4736_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4738_; lean_object* v___x_4739_; uint8_t v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4738_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4739_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4740_ = 0;
v___x_4741_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4742_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4738_, v___x_4739_, v___x_4740_, v___x_4741_);
return v___x_4742_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4743_;
v_res_4743_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4743_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object* v_a_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
return v_res_4745_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4751_ = lean_unsigned_to_nat(3226070615u);
v___x_4752_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4753_ = l_Lean_Name_num___override(v___x_4752_, v___x_4751_);
return v___x_4753_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4754_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4755_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4756_ = l_Lean_Name_str___override(v___x_4755_, v___x_4754_);
return v___x_4756_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___x_4757_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4758_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4759_ = l_Lean_Name_str___override(v___x_4758_, v___x_4757_);
return v___x_4759_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4760_ = lean_unsigned_to_nat(2u);
v___x_4761_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4762_ = l_Lean_Name_num___override(v___x_4761_, v___x_4760_);
return v___x_4762_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; 
v___x_4764_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4765_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4766_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4767_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4764_, v___x_4765_, v___x_4766_);
return v___x_4767_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4768_;
v_res_4768_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4768_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object* v_a_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* v_rbp_4771_){
_start:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4772_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4773_ = l_Lean_Parser_categoryParser(v___x_4772_, v_rbp_4771_);
return v___x_4773_;
}
}
lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t v_addOpenSimple_4774_, lean_object* v_x_4775_, lean_object* v_x_4776_){
_start:
{
if (lean_obj_tag(v_x_4776_) == 0)
{
return v_x_4775_;
}
else
{
lean_object* v_head_4777_; lean_object* v_tail_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4801_; 
v_head_4777_ = lean_ctor_get(v_x_4776_, 0);
v_tail_4778_ = lean_ctor_get(v_x_4776_, 1);
v_isSharedCheck_4801_ = !lean_is_exclusive(v_x_4776_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4780_ = v_x_4776_;
v_isShared_4781_ = v_isSharedCheck_4801_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_tail_4778_);
lean_inc(v_head_4777_);
lean_dec(v_x_4776_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4801_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v_fst_4782_; lean_object* v_snd_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4800_; 
v_fst_4782_ = lean_ctor_get(v_x_4775_, 0);
v_snd_4783_ = lean_ctor_get(v_x_4775_, 1);
v_isSharedCheck_4800_ = !lean_is_exclusive(v_x_4775_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4785_ = v_x_4775_;
v_isShared_4786_ = v_isSharedCheck_4800_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_snd_4783_);
lean_inc(v_fst_4782_);
lean_dec(v_x_4775_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4800_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___y_4788_; 
if (v_addOpenSimple_4774_ == 0)
{
lean_del_object(v___x_4780_);
v___y_4788_ = v_snd_4783_;
goto v___jp_4787_;
}
else
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4798_; 
v___x_4795_ = lean_box(0);
lean_inc(v_head_4777_);
v___x_4796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4796_, 0, v_head_4777_);
lean_ctor_set(v___x_4796_, 1, v___x_4795_);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 1, v_snd_4783_);
lean_ctor_set(v___x_4780_, 0, v___x_4796_);
v___x_4798_ = v___x_4780_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v___x_4796_);
lean_ctor_set(v_reuseFailAlloc_4799_, 1, v_snd_4783_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
v___y_4788_ = v___x_4798_;
goto v___jp_4787_;
}
}
v___jp_4787_:
{
lean_object* v___x_4789_; lean_object* v_env_4790_; lean_object* v___x_4792_; 
v___x_4789_ = l_Lean_Parser_parserExtension;
v_env_4790_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v___x_4789_, v_fst_4782_, v_head_4777_);
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 1, v___y_4788_);
lean_ctor_set(v___x_4785_, 0, v_env_4790_);
v___x_4792_ = v___x_4785_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_env_4790_);
lean_ctor_set(v_reuseFailAlloc_4794_, 1, v___y_4788_);
v___x_4792_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
v_x_4775_ = v___x_4792_;
v_x_4776_ = v_tail_4778_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_addOpenSimple_4774_ = stack[0].m_num;
lean_object* v_x_4775_ = stack[1].m_obj;
lean_object* v_x_4776_ = stack[2].m_obj;
lean_object* v_res_4802_;
v_res_4802_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4774_, v_x_4775_, v_x_4776_);
stack->m_obj
 = v_res_4802_;
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object* v_addOpenSimple_4803_, lean_object* v_x_4804_, lean_object* v_x_4805_){
_start:
{
uint8_t v_addOpenSimple_boxed_4806_; lean_object* v_res_4807_; 
v_addOpenSimple_boxed_4806_ = lean_unbox(v_addOpenSimple_4803_);
v_res_4807_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_boxed_4806_, v_x_4804_, v_x_4805_);
return v_res_4807_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t v_addOpenSimple_4808_, lean_object* v_as_4809_, size_t v_i_4810_, size_t v_stop_4811_, lean_object* v_b_4812_){
_start:
{
uint8_t v___x_4813_; 
v___x_4813_ = lean_usize_dec_eq(v_i_4810_, v_stop_4811_);
if (v___x_4813_ == 0)
{
lean_object* v_toParserModuleContext_4814_; lean_object* v_toInputContext_4815_; lean_object* v_toCacheableParserContext_4816_; lean_object* v_tokens_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4844_; 
v_toParserModuleContext_4814_ = lean_ctor_get(v_b_4812_, 1);
v_toInputContext_4815_ = lean_ctor_get(v_b_4812_, 0);
v_toCacheableParserContext_4816_ = lean_ctor_get(v_b_4812_, 2);
v_tokens_4817_ = lean_ctor_get(v_b_4812_, 3);
v_isSharedCheck_4844_ = !lean_is_exclusive(v_b_4812_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4819_ = v_b_4812_;
v_isShared_4820_ = v_isSharedCheck_4844_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_tokens_4817_);
lean_inc(v_toCacheableParserContext_4816_);
lean_inc(v_toParserModuleContext_4814_);
lean_inc(v_toInputContext_4815_);
lean_dec(v_b_4812_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4844_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v_env_4821_; lean_object* v_options_4822_; lean_object* v_currNamespace_4823_; lean_object* v_openDecls_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4843_; 
v_env_4821_ = lean_ctor_get(v_toParserModuleContext_4814_, 0);
v_options_4822_ = lean_ctor_get(v_toParserModuleContext_4814_, 1);
v_currNamespace_4823_ = lean_ctor_get(v_toParserModuleContext_4814_, 2);
v_openDecls_4824_ = lean_ctor_get(v_toParserModuleContext_4814_, 3);
v_isSharedCheck_4843_ = !lean_is_exclusive(v_toParserModuleContext_4814_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4826_ = v_toParserModuleContext_4814_;
v_isShared_4827_ = v_isSharedCheck_4843_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_openDecls_4824_);
lean_inc(v_currNamespace_4823_);
lean_inc(v_options_4822_);
lean_inc(v_env_4821_);
lean_dec(v_toParserModuleContext_4814_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4843_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4828_; lean_object* v_nss_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v_fst_4832_; lean_object* v_snd_4833_; lean_object* v___x_4835_; 
v___x_4828_ = lean_array_uget_borrowed(v_as_4809_, v_i_4810_);
lean_inc(v___x_4828_);
lean_inc(v_openDecls_4824_);
lean_inc(v_currNamespace_4823_);
lean_inc_ref(v_env_4821_);
v_nss_4829_ = l_Lean_ResolveName_resolveNamespace(v_env_4821_, v_currNamespace_4823_, v_openDecls_4824_, v___x_4828_);
v___x_4830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4830_, 0, v_env_4821_);
lean_ctor_set(v___x_4830_, 1, v_openDecls_4824_);
v___x_4831_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4808_, v___x_4830_, v_nss_4829_);
v_fst_4832_ = lean_ctor_get(v___x_4831_, 0);
lean_inc(v_fst_4832_);
v_snd_4833_ = lean_ctor_get(v___x_4831_, 1);
lean_inc(v_snd_4833_);
lean_dec_ref(v___x_4831_);
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 3, v_snd_4833_);
lean_ctor_set(v___x_4826_, 0, v_fst_4832_);
v___x_4835_ = v___x_4826_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v_fst_4832_);
lean_ctor_set(v_reuseFailAlloc_4842_, 1, v_options_4822_);
lean_ctor_set(v_reuseFailAlloc_4842_, 2, v_currNamespace_4823_);
lean_ctor_set(v_reuseFailAlloc_4842_, 3, v_snd_4833_);
v___x_4835_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
lean_object* v___x_4837_; 
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 1, v___x_4835_);
v___x_4837_ = v___x_4819_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_toInputContext_4815_);
lean_ctor_set(v_reuseFailAlloc_4841_, 1, v___x_4835_);
lean_ctor_set(v_reuseFailAlloc_4841_, 2, v_toCacheableParserContext_4816_);
lean_ctor_set(v_reuseFailAlloc_4841_, 3, v_tokens_4817_);
v___x_4837_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
size_t v___x_4838_; size_t v___x_4839_; 
v___x_4838_ = ((size_t)1ULL);
v___x_4839_ = lean_usize_add(v_i_4810_, v___x_4838_);
v_i_4810_ = v___x_4839_;
v_b_4812_ = v___x_4837_;
goto _start;
}
}
}
}
}
else
{
return v_b_4812_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_addOpenSimple_4808_ = stack[0].m_num;
lean_object* v_as_4809_ = stack[1].m_obj;
size_t v_i_4810_ = stack[2].m_num;
size_t v_stop_4811_ = stack[3].m_num;
lean_object* v_b_4812_ = stack[4].m_obj;
lean_object* v_res_4845_;
v_res_4845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4808_, v_as_4809_, v_i_4810_, v_stop_4811_, v_b_4812_);
stack->m_obj
 = v_res_4845_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object* v_addOpenSimple_4846_, lean_object* v_as_4847_, lean_object* v_i_4848_, lean_object* v_stop_4849_, lean_object* v_b_4850_){
_start:
{
uint8_t v_addOpenSimple_boxed_4851_; size_t v_i_boxed_4852_; size_t v_stop_boxed_4853_; lean_object* v_res_4854_; 
v_addOpenSimple_boxed_4851_ = lean_unbox(v_addOpenSimple_4846_);
v_i_boxed_4852_ = lean_unbox_usize(v_i_4848_);
lean_dec(v_i_4848_);
v_stop_boxed_4853_ = lean_unbox_usize(v_stop_4849_);
lean_dec(v_stop_4849_);
v_res_4854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_boxed_4851_, v_as_4847_, v_i_boxed_4852_, v_stop_boxed_4853_, v_b_4850_);
lean_dec_ref(v_as_4847_);
return v_res_4854_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object* v___x_4855_, lean_object* v_ids_4856_, uint8_t v_addOpenSimple_4857_, lean_object* v_c_4858_){
_start:
{
lean_object* v___y_4860_; lean_object* v___x_4880_; lean_object* v___x_4881_; uint8_t v___x_4882_; 
v___x_4880_ = lean_unsigned_to_nat(0u);
v___x_4881_ = lean_array_get_size(v_ids_4856_);
v___x_4882_ = lean_nat_dec_lt(v___x_4880_, v___x_4881_);
if (v___x_4882_ == 0)
{
v___y_4860_ = v_c_4858_;
goto v___jp_4859_;
}
else
{
uint8_t v___x_4883_; 
v___x_4883_ = lean_nat_dec_le(v___x_4881_, v___x_4881_);
if (v___x_4883_ == 0)
{
if (v___x_4882_ == 0)
{
v___y_4860_ = v_c_4858_;
goto v___jp_4859_;
}
else
{
size_t v___x_4884_; size_t v___x_4885_; lean_object* v___x_4886_; 
v___x_4884_ = ((size_t)0ULL);
v___x_4885_ = lean_usize_of_nat(v___x_4881_);
v___x_4886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4857_, v_ids_4856_, v___x_4884_, v___x_4885_, v_c_4858_);
v___y_4860_ = v___x_4886_;
goto v___jp_4859_;
}
}
else
{
size_t v___x_4887_; size_t v___x_4888_; lean_object* v___x_4889_; 
v___x_4887_ = ((size_t)0ULL);
v___x_4888_ = lean_usize_of_nat(v___x_4881_);
v___x_4889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4857_, v_ids_4856_, v___x_4887_, v___x_4888_, v_c_4858_);
v___y_4860_ = v___x_4889_;
goto v___jp_4859_;
}
}
v___jp_4859_:
{
lean_object* v_toParserModuleContext_4861_; lean_object* v_toInputContext_4862_; lean_object* v_toCacheableParserContext_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4878_; 
v_toParserModuleContext_4861_ = lean_ctor_get(v___y_4860_, 1);
v_toInputContext_4862_ = lean_ctor_get(v___y_4860_, 0);
v_toCacheableParserContext_4863_ = lean_ctor_get(v___y_4860_, 2);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___y_4860_);
if (v_isSharedCheck_4878_ == 0)
{
lean_object* v_unused_4879_; 
v_unused_4879_ = lean_ctor_get(v___y_4860_, 3);
lean_dec(v_unused_4879_);
v___x_4865_ = v___y_4860_;
v_isShared_4866_ = v_isSharedCheck_4878_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_toCacheableParserContext_4863_);
lean_inc(v_toParserModuleContext_4861_);
lean_inc(v_toInputContext_4862_);
lean_dec(v___y_4860_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4878_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v_env_4867_; lean_object* v___x_4868_; lean_object* v_ext_4869_; lean_object* v_toEnvExtension_4870_; lean_object* v_asyncMode_4871_; uint8_t v___x_4872_; lean_object* v___x_4873_; lean_object* v_tokens_4874_; lean_object* v___x_4876_; 
v_env_4867_ = lean_ctor_get(v_toParserModuleContext_4861_, 0);
v___x_4868_ = l_Lean_Parser_parserExtension;
v_ext_4869_ = lean_ctor_get(v___x_4868_, 1);
v_toEnvExtension_4870_ = lean_ctor_get(v_ext_4869_, 0);
v_asyncMode_4871_ = lean_ctor_get(v_toEnvExtension_4870_, 2);
v___x_4872_ = 0;
lean_inc_ref(v_env_4867_);
v___x_4873_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4855_, v___x_4868_, v_env_4867_, v_asyncMode_4871_, v___x_4872_);
v_tokens_4874_ = lean_ctor_get(v___x_4873_, 0);
lean_inc_ref(v_tokens_4874_);
lean_dec(v___x_4873_);
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 3, v_tokens_4874_);
v___x_4876_ = v___x_4865_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_toInputContext_4862_);
lean_ctor_set(v_reuseFailAlloc_4877_, 1, v_toParserModuleContext_4861_);
lean_ctor_set(v_reuseFailAlloc_4877_, 2, v_toCacheableParserContext_4863_);
lean_ctor_set(v_reuseFailAlloc_4877_, 3, v_tokens_4874_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4855_ = stack[0].m_obj;
lean_object* v_ids_4856_ = stack[1].m_obj;
uint8_t v_addOpenSimple_4857_ = stack[2].m_num;
lean_object* v_c_4858_ = stack[3].m_obj;
lean_object* v_res_4890_;
v_res_4890_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_4855_, v_ids_4856_, v_addOpenSimple_4857_, v_c_4858_);
stack->m_obj
 = v_res_4890_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object* v___x_4891_, lean_object* v_ids_4892_, lean_object* v_addOpenSimple_4893_, lean_object* v_c_4894_){
_start:
{
uint8_t v_addOpenSimple_boxed_4895_; lean_object* v_res_4896_; 
v_addOpenSimple_boxed_4895_ = lean_unbox(v_addOpenSimple_4893_);
v_res_4896_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_4891_, v_ids_4892_, v_addOpenSimple_boxed_4895_, v_c_4894_);
lean_dec_ref(v_ids_4892_);
lean_dec_ref(v___x_4891_);
return v_res_4896_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* v_ids_4897_, uint8_t v_addOpenSimple_4898_, lean_object* v_p_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_){
_start:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___f_4904_; lean_object* v___x_4905_; 
v___x_4902_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4903_ = lean_box(v_addOpenSimple_4898_);
v___f_4904_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4904_, 0, v___x_4902_);
lean_closure_set(v___f_4904_, 1, v_ids_4897_);
lean_closure_set(v___f_4904_, 2, v___x_4903_);
v___x_4905_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_4904_, v_p_4899_, v_a_4900_, v_a_4901_);
return v___x_4905_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_0interp(lean_interpreter_value* stack)
{
lean_object* v_ids_4897_ = stack[0].m_obj;
uint8_t v_addOpenSimple_4898_ = stack[1].m_num;
lean_object* v_p_4899_ = stack[2].m_obj;
lean_object* v_a_4900_ = stack[3].m_obj;
lean_object* v_a_4901_ = stack[4].m_obj;
lean_object* v_res_4906_;
v_res_4906_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_4897_, v_addOpenSimple_4898_, v_p_4899_, v_a_4900_, v_a_4901_);
stack->m_obj
 = v_res_4906_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* v_ids_4907_, lean_object* v_addOpenSimple_4908_, lean_object* v_p_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_){
_start:
{
uint8_t v_addOpenSimple_boxed_4912_; lean_object* v_res_4913_; 
v_addOpenSimple_boxed_4912_ = lean_unbox(v_addOpenSimple_4908_);
v_res_4913_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_4907_, v_addOpenSimple_boxed_4912_, v_p_4909_, v_a_4910_, v_a_4911_);
return v_res_4913_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t v_sz_4914_, size_t v_i_4915_, lean_object* v_bs_4916_){
_start:
{
uint8_t v___x_4917_; 
v___x_4917_ = lean_usize_dec_lt(v_i_4915_, v_sz_4914_);
if (v___x_4917_ == 0)
{
return v_bs_4916_;
}
else
{
lean_object* v_v_4918_; lean_object* v___x_4919_; lean_object* v_bs_x27_4920_; lean_object* v___x_4921_; size_t v___x_4922_; size_t v___x_4923_; lean_object* v___x_4924_; 
v_v_4918_ = lean_array_uget(v_bs_4916_, v_i_4915_);
v___x_4919_ = lean_unsigned_to_nat(0u);
v_bs_x27_4920_ = lean_array_uset(v_bs_4916_, v_i_4915_, v___x_4919_);
v___x_4921_ = l_Lean_Syntax_getId(v_v_4918_);
lean_dec(v_v_4918_);
v___x_4922_ = ((size_t)1ULL);
v___x_4923_ = lean_usize_add(v_i_4915_, v___x_4922_);
v___x_4924_ = lean_array_uset(v_bs_x27_4920_, v_i_4915_, v___x_4921_);
v_i_4915_ = v___x_4923_;
v_bs_4916_ = v___x_4924_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4914_ = stack[0].m_num;
size_t v_i_4915_ = stack[1].m_num;
lean_object* v_bs_4916_ = stack[2].m_obj;
lean_object* v_res_4926_;
v_res_4926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4914_, v_i_4915_, v_bs_4916_);
stack->m_obj
 = v_res_4926_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object* v_sz_4927_, lean_object* v_i_4928_, lean_object* v_bs_4929_){
_start:
{
size_t v_sz_boxed_4930_; size_t v_i_boxed_4931_; lean_object* v_res_4932_; 
v_sz_boxed_4930_ = lean_unbox_usize(v_sz_4927_);
lean_dec(v_sz_4927_);
v_i_boxed_4931_ = lean_unbox_usize(v_i_4928_);
lean_dec(v_i_4928_);
v_res_4932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_boxed_4930_, v_i_boxed_4931_, v_bs_4929_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* v_openDeclStx_4946_, lean_object* v_p_4947_, lean_object* v_c_4948_, lean_object* v_s_4949_){
_start:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; uint8_t v___x_4952_; 
lean_inc(v_openDeclStx_4946_);
v___x_4950_ = l_Lean_Syntax_getKind(v_openDeclStx_4946_);
v___x_4951_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__2));
v___x_4952_ = lean_name_eq(v___x_4950_, v___x_4951_);
if (v___x_4952_ == 0)
{
lean_object* v___x_4953_; uint8_t v___x_4954_; 
v___x_4953_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__4));
v___x_4954_ = lean_name_eq(v___x_4950_, v___x_4953_);
lean_dec(v___x_4950_);
if (v___x_4954_ == 0)
{
lean_object* v___x_4955_; 
lean_dec(v_openDeclStx_4946_);
v___x_4955_ = lean_apply_2(v_p_4947_, v_c_4948_, v_s_4949_);
return v___x_4955_;
}
else
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; size_t v_sz_4959_; size_t v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4956_ = lean_unsigned_to_nat(1u);
v___x_4957_ = l_Lean_Syntax_getArg(v_openDeclStx_4946_, v___x_4956_);
lean_dec(v_openDeclStx_4946_);
v___x_4958_ = l_Lean_Syntax_getArgs(v___x_4957_);
lean_dec(v___x_4957_);
v_sz_4959_ = lean_array_size(v___x_4958_);
v___x_4960_ = ((size_t)0ULL);
v___x_4961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4959_, v___x_4960_, v___x_4958_);
v___x_4962_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4961_, v___x_4952_, v_p_4947_, v_c_4948_, v_s_4949_);
return v___x_4962_;
}
}
else
{
lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; size_t v_sz_4966_; size_t v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
lean_dec(v___x_4950_);
v___x_4963_ = lean_unsigned_to_nat(0u);
v___x_4964_ = l_Lean_Syntax_getArg(v_openDeclStx_4946_, v___x_4963_);
lean_dec(v_openDeclStx_4946_);
v___x_4965_ = l_Lean_Syntax_getArgs(v___x_4964_);
lean_dec(v___x_4964_);
v_sz_4966_ = lean_array_size(v___x_4965_);
v___x_4967_ = ((size_t)0ULL);
v___x_4968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4966_, v___x_4967_, v___x_4965_);
v___x_4969_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4968_, v___x_4952_, v_p_4947_, v_c_4948_, v_s_4949_);
return v___x_4969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* v_p_4976_, lean_object* v_c_4977_, lean_object* v_s_4978_){
_start:
{
lean_object* v_stxStack_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; uint8_t v___x_4982_; 
v_stxStack_4979_ = lean_ctor_get(v_s_4978_, 0);
v___x_4980_ = lean_unsigned_to_nat(0u);
v___x_4981_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4979_);
v___x_4982_ = lean_nat_dec_lt(v___x_4980_, v___x_4981_);
lean_dec(v___x_4981_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; 
v___x_4983_ = lean_apply_2(v_p_4976_, v_c_4977_, v_s_4978_);
return v___x_4983_;
}
else
{
lean_object* v_stx_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; uint8_t v___x_4987_; 
v_stx_4984_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4979_);
lean_inc(v_stx_4984_);
v___x_4985_ = l_Lean_Syntax_getKind(v_stx_4984_);
v___x_4986_ = ((lean_object*)(l_Lean_Parser_withOpenFn___closed__1));
v___x_4987_ = lean_name_eq(v___x_4985_, v___x_4986_);
lean_dec(v___x_4985_);
if (v___x_4987_ == 0)
{
lean_object* v___x_4988_; 
lean_dec(v_stx_4984_);
v___x_4988_ = lean_apply_2(v_p_4976_, v_c_4977_, v_s_4978_);
return v___x_4988_;
}
else
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4989_ = lean_unsigned_to_nat(1u);
v___x_4990_ = l_Lean_Syntax_getArg(v_stx_4984_, v___x_4989_);
lean_dec(v_stx_4984_);
v___x_4991_ = l_Lean_Parser_withOpenDeclFnCore(v___x_4990_, v_p_4976_, v_c_4977_, v_s_4978_);
return v___x_4991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* v_p_4992_){
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
v___x_4998_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
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
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* v_p_5003_, lean_object* v_c_5004_, lean_object* v_s_5005_){
_start:
{
lean_object* v_stxStack_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; uint8_t v___x_5009_; 
v_stxStack_5006_ = lean_ctor_get(v_s_5005_, 0);
v___x_5007_ = lean_unsigned_to_nat(0u);
v___x_5008_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5006_);
v___x_5009_ = lean_nat_dec_lt(v___x_5007_, v___x_5008_);
lean_dec(v___x_5008_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; 
v___x_5010_ = lean_apply_2(v_p_5003_, v_c_5004_, v_s_5005_);
return v___x_5010_;
}
else
{
lean_object* v_stx_5011_; lean_object* v___x_5012_; 
v_stx_5011_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5006_);
v___x_5012_ = l_Lean_Parser_withOpenDeclFnCore(v_stx_5011_, v_p_5003_, v_c_5004_, v_s_5005_);
return v___x_5012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* v_p_5013_){
_start:
{
lean_object* v_info_5014_; lean_object* v_fn_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5023_; 
v_info_5014_ = lean_ctor_get(v_p_5013_, 0);
v_fn_5015_ = lean_ctor_get(v_p_5013_, 1);
v_isSharedCheck_5023_ = !lean_is_exclusive(v_p_5013_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5017_ = v_p_5013_;
v_isShared_5018_ = v_isSharedCheck_5023_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_fn_5015_);
lean_inc(v_info_5014_);
lean_dec(v_p_5013_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5023_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5019_; lean_object* v___x_5021_; 
v___x_5019_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(v___x_5019_, 0, v_fn_5015_);
if (v_isShared_5018_ == 0)
{
lean_ctor_set(v___x_5017_, 1, v___x_5019_);
v___x_5021_ = v___x_5017_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_info_5014_);
lean_ctor_set(v_reuseFailAlloc_5022_, 1, v___x_5019_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object* v_val_5030_){
_start:
{
lean_object* v___x_5038_; 
v___x_5038_ = l_Lean_Syntax_isStrLit_x3f(v_val_5030_);
if (lean_obj_tag(v___x_5038_) == 1)
{
lean_object* v_val_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5047_; 
v_val_5039_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5041_ = v___x_5038_;
v_isShared_5042_ = v_isSharedCheck_5047_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_val_5039_);
lean_dec(v___x_5038_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5047_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5043_; lean_object* v___x_5045_; 
v___x_5043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5043_, 0, v_val_5039_);
if (v_isShared_5042_ == 0)
{
lean_ctor_set(v___x_5041_, 0, v___x_5043_);
v___x_5045_ = v___x_5041_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5043_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
}
else
{
lean_object* v___x_5048_; 
lean_dec(v___x_5038_);
v___x_5048_ = l_Lean_Syntax_isNatLit_x3f(v_val_5030_);
if (lean_obj_tag(v___x_5048_) == 1)
{
lean_object* v_val_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5057_; 
v_val_5049_ = lean_ctor_get(v___x_5048_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5048_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5051_ = v___x_5048_;
v_isShared_5052_ = v_isSharedCheck_5057_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_val_5049_);
lean_dec(v___x_5048_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5057_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v___x_5053_; lean_object* v___x_5055_; 
v___x_5053_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5053_, 0, v_val_5049_);
if (v_isShared_5052_ == 0)
{
lean_ctor_set(v___x_5051_, 0, v___x_5053_);
v___x_5055_ = v___x_5051_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___x_5053_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
else
{
lean_dec(v___x_5048_);
if (lean_obj_tag(v_val_5030_) == 2)
{
lean_object* v_val_5058_; lean_object* v___x_5059_; uint8_t v___x_5060_; 
v_val_5058_ = lean_ctor_get(v_val_5030_, 1);
v___x_5059_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3));
v___x_5060_ = lean_string_dec_eq(v_val_5058_, v___x_5059_);
if (v___x_5060_ == 0)
{
goto v___jp_5031_;
}
else
{
lean_object* v___x_5061_; lean_object* v___x_5062_; 
v___x_5061_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5061_, 0, v___x_5060_);
v___x_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5061_);
return v___x_5062_;
}
}
else
{
goto v___jp_5031_;
}
}
}
v___jp_5031_:
{
if (lean_obj_tag(v_val_5030_) == 2)
{
lean_object* v_val_5032_; lean_object* v___x_5033_; uint8_t v___x_5034_; 
v_val_5032_ = lean_ctor_get(v_val_5030_, 1);
v___x_5033_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0));
v___x_5034_ = lean_string_dec_eq(v_val_5032_, v___x_5033_);
if (v___x_5034_ == 0)
{
lean_object* v___x_5035_; 
v___x_5035_ = lean_box(0);
return v___x_5035_;
}
else
{
lean_object* v___x_5036_; 
v___x_5036_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2));
return v___x_5036_;
}
}
else
{
lean_object* v___x_5037_; 
v___x_5037_ = lean_box(0);
return v___x_5037_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object* v_val_5063_){
_start:
{
lean_object* v_res_5064_; 
v_res_5064_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_val_5063_);
lean_dec(v_val_5063_);
return v_res_5064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object* v_nameStx_5065_, lean_object* v_v_5066_, lean_object* v_c_5067_){
_start:
{
lean_object* v_toParserModuleContext_5068_; lean_object* v_toInputContext_5069_; lean_object* v_toCacheableParserContext_5070_; lean_object* v_tokens_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5108_; 
v_toParserModuleContext_5068_ = lean_ctor_get(v_c_5067_, 1);
v_toInputContext_5069_ = lean_ctor_get(v_c_5067_, 0);
v_toCacheableParserContext_5070_ = lean_ctor_get(v_c_5067_, 2);
v_tokens_5071_ = lean_ctor_get(v_c_5067_, 3);
v_isSharedCheck_5108_ = !lean_is_exclusive(v_c_5067_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5073_ = v_c_5067_;
v_isShared_5074_ = v_isSharedCheck_5108_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_tokens_5071_);
lean_inc(v_toCacheableParserContext_5070_);
lean_inc(v_toParserModuleContext_5068_);
lean_inc(v_toInputContext_5069_);
lean_dec(v_c_5067_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5108_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v_env_5075_; lean_object* v_options_5076_; lean_object* v_currNamespace_5077_; lean_object* v_openDecls_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5107_; 
v_env_5075_ = lean_ctor_get(v_toParserModuleContext_5068_, 0);
v_options_5076_ = lean_ctor_get(v_toParserModuleContext_5068_, 1);
v_currNamespace_5077_ = lean_ctor_get(v_toParserModuleContext_5068_, 2);
v_openDecls_5078_ = lean_ctor_get(v_toParserModuleContext_5068_, 3);
v_isSharedCheck_5107_ = !lean_is_exclusive(v_toParserModuleContext_5068_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5080_ = v_toParserModuleContext_5068_;
v_isShared_5081_ = v_isSharedCheck_5107_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_openDecls_5078_);
lean_inc(v_currNamespace_5077_);
lean_inc(v_options_5076_);
lean_inc(v_env_5075_);
lean_dec(v_toParserModuleContext_5068_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5107_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___y_5083_; lean_object* v_map_5090_; uint8_t v_hasTrace_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5106_; 
v_map_5090_ = lean_ctor_get(v_options_5076_, 0);
v_hasTrace_5091_ = lean_ctor_get_uint8(v_options_5076_, sizeof(void*)*1);
v_isSharedCheck_5106_ = !lean_is_exclusive(v_options_5076_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_5093_ = v_options_5076_;
v_isShared_5094_ = v_isSharedCheck_5106_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_map_5090_);
lean_dec(v_options_5076_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5106_;
goto v_resetjp_5092_;
}
v___jp_5082_:
{
lean_object* v___x_5085_; 
if (v_isShared_5081_ == 0)
{
lean_ctor_set(v___x_5080_, 1, v___y_5083_);
v___x_5085_ = v___x_5080_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_env_5075_);
lean_ctor_set(v_reuseFailAlloc_5089_, 1, v___y_5083_);
lean_ctor_set(v_reuseFailAlloc_5089_, 2, v_currNamespace_5077_);
lean_ctor_set(v_reuseFailAlloc_5089_, 3, v_openDecls_5078_);
v___x_5085_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
lean_object* v___x_5087_; 
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 1, v___x_5085_);
v___x_5087_ = v___x_5073_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_toInputContext_5069_);
lean_ctor_set(v_reuseFailAlloc_5088_, 1, v___x_5085_);
lean_ctor_set(v_reuseFailAlloc_5088_, 2, v_toCacheableParserContext_5070_);
lean_ctor_set(v_reuseFailAlloc_5088_, 3, v_tokens_5071_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
v_resetjp_5092_:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5095_ = l_Lean_Syntax_getId(v_nameStx_5065_);
v___x_5096_ = l_Lean_Name_eraseMacroScopes(v___x_5095_);
lean_dec(v___x_5095_);
lean_inc(v___x_5096_);
v___x_5097_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_5096_, v_v_5066_, v_map_5090_);
if (v_hasTrace_5091_ == 0)
{
lean_object* v___x_5098_; uint8_t v___x_5099_; lean_object* v___x_5101_; 
v___x_5098_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_5099_ = l_Lean_Name_isPrefixOf(v___x_5098_, v___x_5096_);
lean_dec(v___x_5096_);
if (v_isShared_5094_ == 0)
{
lean_ctor_set(v___x_5093_, 0, v___x_5097_);
v___x_5101_ = v___x_5093_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5097_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
lean_ctor_set_uint8(v___x_5101_, sizeof(void*)*1, v___x_5099_);
v___y_5083_ = v___x_5101_;
goto v___jp_5082_;
}
}
else
{
lean_object* v___x_5104_; 
lean_dec(v___x_5096_);
if (v_isShared_5094_ == 0)
{
lean_ctor_set(v___x_5093_, 0, v___x_5097_);
v___x_5104_ = v___x_5093_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v___x_5097_);
lean_ctor_set_uint8(v_reuseFailAlloc_5105_, sizeof(void*)*1, v_hasTrace_5091_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
v___y_5083_ = v___x_5104_;
goto v___jp_5082_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object* v_nameStx_5109_, lean_object* v_v_5110_, lean_object* v_c_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(v_nameStx_5109_, v_v_5110_, v_c_5111_);
lean_dec(v_nameStx_5109_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object* v_nameStx_5113_, lean_object* v_valStx_5114_, lean_object* v_p_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_){
_start:
{
lean_object* v___x_5118_; 
v___x_5118_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_valStx_5114_);
if (lean_obj_tag(v___x_5118_) == 0)
{
lean_object* v___x_5119_; 
lean_dec(v_nameStx_5113_);
v___x_5119_ = lean_apply_2(v_p_5115_, v_a_5116_, v_a_5117_);
return v___x_5119_;
}
else
{
lean_object* v_val_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v_val_5120_ = lean_ctor_get(v___x_5118_, 0);
lean_inc(v_val_5120_);
lean_dec_ref_known(v___x_5118_, 1);
v___x_5121_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed), 3, 2);
lean_closure_set(v___x_5121_, 0, v_nameStx_5113_);
lean_closure_set(v___x_5121_, 1, v_val_5120_);
v___x_5122_ = l_Lean_Parser_adaptUncacheableContextFn(v___x_5121_, v_p_5115_, v_a_5116_, v_a_5117_);
return v___x_5122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object* v_nameStx_5123_, lean_object* v_valStx_5124_, lean_object* v_p_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v_nameStx_5123_, v_valStx_5124_, v_p_5125_, v_a_5126_, v_a_5127_);
lean_dec(v_valStx_5124_);
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object* v_p_5135_, lean_object* v_c_5136_, lean_object* v_s_5137_){
_start:
{
lean_object* v_stxStack_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; uint8_t v___x_5141_; 
v_stxStack_5138_ = lean_ctor_get(v_s_5137_, 0);
v___x_5139_ = lean_unsigned_to_nat(0u);
v___x_5140_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5138_);
v___x_5141_ = lean_nat_dec_lt(v___x_5139_, v___x_5140_);
lean_dec(v___x_5140_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; 
v___x_5142_ = lean_apply_2(v_p_5135_, v_c_5136_, v_s_5137_);
return v___x_5142_;
}
else
{
lean_object* v_stx_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; uint8_t v___x_5146_; 
v_stx_5143_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5138_);
lean_inc(v_stx_5143_);
v___x_5144_ = l_Lean_Syntax_getKind(v_stx_5143_);
v___x_5145_ = ((lean_object*)(l_Lean_Parser_withSetOptionFn___closed__1));
v___x_5146_ = lean_name_eq(v___x_5144_, v___x_5145_);
lean_dec(v___x_5144_);
if (v___x_5146_ == 0)
{
lean_object* v___x_5147_; 
lean_dec(v_stx_5143_);
v___x_5147_ = lean_apply_2(v_p_5135_, v_c_5136_, v_s_5137_);
return v___x_5147_;
}
else
{
lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
v___x_5148_ = lean_unsigned_to_nat(1u);
v___x_5149_ = l_Lean_Syntax_getArg(v_stx_5143_, v___x_5148_);
v___x_5150_ = lean_unsigned_to_nat(3u);
v___x_5151_ = l_Lean_Syntax_getArg(v_stx_5143_, v___x_5150_);
lean_dec(v_stx_5143_);
v___x_5152_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5149_, v___x_5151_, v_p_5135_, v_c_5136_, v_s_5137_);
lean_dec(v___x_5151_);
return v___x_5152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object* v_p_5153_){
_start:
{
lean_object* v_info_5154_; lean_object* v_fn_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5163_; 
v_info_5154_ = lean_ctor_get(v_p_5153_, 0);
v_fn_5155_ = lean_ctor_get(v_p_5153_, 1);
v_isSharedCheck_5163_ = !lean_is_exclusive(v_p_5153_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5157_ = v_p_5153_;
v_isShared_5158_ = v_isSharedCheck_5163_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_fn_5155_);
lean_inc(v_info_5154_);
lean_dec(v_p_5153_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5163_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
lean_object* v___x_5159_; lean_object* v___x_5161_; 
v___x_5159_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionFn), 3, 1);
lean_closure_set(v___x_5159_, 0, v_fn_5155_);
if (v_isShared_5158_ == 0)
{
lean_ctor_set(v___x_5157_, 1, v___x_5159_);
v___x_5161_ = v___x_5157_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_info_5154_);
lean_ctor_set(v_reuseFailAlloc_5162_, 1, v___x_5159_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object* v_p_5164_, lean_object* v_c_5165_, lean_object* v_s_5166_){
_start:
{
lean_object* v_stxStack_5167_; lean_object* v_sz_5168_; lean_object* v___x_5169_; uint8_t v___x_5170_; 
v_stxStack_5167_ = lean_ctor_get(v_s_5166_, 0);
v_sz_5168_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5167_);
v___x_5169_ = lean_unsigned_to_nat(3u);
v___x_5170_ = lean_nat_dec_le(v___x_5169_, v_sz_5168_);
if (v___x_5170_ == 0)
{
lean_object* v___x_5171_; 
lean_dec(v_sz_5168_);
v___x_5171_ = lean_apply_2(v_p_5164_, v_c_5165_, v_s_5166_);
return v___x_5171_;
}
else
{
lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; 
v___x_5172_ = lean_nat_sub(v_sz_5168_, v___x_5169_);
lean_dec(v_sz_5168_);
v___x_5173_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5167_, v___x_5172_);
lean_dec(v___x_5172_);
v___x_5174_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5167_);
v___x_5175_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5173_, v___x_5174_, v_p_5164_, v_c_5165_, v_s_5166_);
lean_dec(v___x_5174_);
return v___x_5175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object* v_p_5176_){
_start:
{
lean_object* v_info_5177_; lean_object* v_fn_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5186_; 
v_info_5177_ = lean_ctor_get(v_p_5176_, 0);
v_fn_5178_ = lean_ctor_get(v_p_5176_, 1);
v_isSharedCheck_5186_ = !lean_is_exclusive(v_p_5176_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5180_ = v_p_5176_;
v_isShared_5181_ = v_isSharedCheck_5186_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_fn_5178_);
lean_inc(v_info_5177_);
lean_dec(v_p_5176_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5186_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5182_; lean_object* v___x_5184_; 
v___x_5182_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionValueFn), 3, 1);
lean_closure_set(v___x_5182_, 0, v_fn_5178_);
if (v_isShared_5181_ == 0)
{
lean_ctor_set(v___x_5180_, 1, v___x_5182_);
v___x_5184_ = v___x_5180_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_info_5177_);
lean_ctor_set(v_reuseFailAlloc_5185_, 1, v___x_5182_);
v___x_5184_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
return v___x_5184_;
}
}
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object* v___x_5187_){
_start:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; 
v___x_5189_ = lean_st_ref_get(v___x_5187_);
v___x_5190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5190_, 0, v___x_5189_);
return v___x_5190_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5187_ = stack[0].m_obj;
lean_object* v_res_5191_;
v_res_5191_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_5187_);
stack->m_obj
 = v_res_5191_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v___x_5192_, lean_object* v___y_5193_){
_start:
{
lean_object* v_res_5194_; 
v_res_5194_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_5192_);
lean_dec(v___x_5192_);
return v_res_5194_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5195_; lean_object* v___f_5196_; 
v___x_5195_ = l_Lean_Parser_parserAliasesRef;
v___f_5196_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5196_, 0, v___x_5195_);
return v___f_5196_;
}
}
lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; uint8_t v___x_5207_; lean_object* v___x_5208_; 
v___f_5203_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_);
v___x_5204_ = lean_box(0);
v___x_5205_ = lean_box(2);
v___x_5206_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_));
v___x_5207_ = 0;
v___x_5208_ = l_Lean_registerEnvExtension___redArg(v___f_5203_, v___x_5204_, v___x_5205_, v___x_5206_, v___x_5207_, v___x_5207_);
return v___x_5208_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5209_;
v_res_5209_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5209_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v_a_5210_){
_start:
{
lean_object* v_res_5211_; 
v_res_5211_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_();
return v_res_5211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___impl(lean_object* v_x_5212_){
_start:
{
lean_object* v___x_5213_; 
v___x_5213_ = lean_obj_tag_nat(v_x_5212_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___impl___boxed(lean_object* v_x_5214_){
_start:
{
lean_object* v_res_5215_; 
v_res_5215_ = l_Lean_Parser_ParserResolution_ctorIdx___impl(v_x_5214_);
lean_dec_ref(v_x_5214_);
return v_res_5215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object* v_t_5216_, lean_object* v_k_5217_){
_start:
{
switch(lean_obj_tag(v_t_5216_))
{
case 0:
{
lean_object* v_cat_5218_; lean_object* v___x_5219_; 
v_cat_5218_ = lean_ctor_get(v_t_5216_, 0);
lean_inc(v_cat_5218_);
lean_dec_ref_known(v_t_5216_, 1);
v___x_5219_ = lean_apply_1(v_k_5217_, v_cat_5218_);
return v___x_5219_;
}
case 1:
{
lean_object* v_decl_5220_; uint8_t v_isDescr_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; 
v_decl_5220_ = lean_ctor_get(v_t_5216_, 0);
lean_inc(v_decl_5220_);
v_isDescr_5221_ = lean_ctor_get_uint8(v_t_5216_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5216_, 1);
v___x_5222_ = lean_box(v_isDescr_5221_);
v___x_5223_ = lean_apply_2(v_k_5217_, v_decl_5220_, v___x_5222_);
return v___x_5223_;
}
default: 
{
lean_object* v_p_5224_; lean_object* v___x_5225_; 
v_p_5224_ = lean_ctor_get(v_t_5216_, 0);
lean_inc_ref(v_p_5224_);
lean_dec_ref_known(v_t_5216_, 1);
v___x_5225_ = lean_apply_1(v_k_5217_, v_p_5224_);
return v___x_5225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object* v_motive_5226_, lean_object* v_ctorIdx_5227_, lean_object* v_t_5228_, lean_object* v_h_5229_, lean_object* v_k_5230_){
_start:
{
lean_object* v___x_5231_; 
v___x_5231_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5228_, v_k_5230_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object* v_motive_5232_, lean_object* v_ctorIdx_5233_, lean_object* v_t_5234_, lean_object* v_h_5235_, lean_object* v_k_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Lean_Parser_ParserResolution_ctorElim(v_motive_5232_, v_ctorIdx_5233_, v_t_5234_, v_h_5235_, v_k_5236_);
lean_dec(v_ctorIdx_5233_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object* v_t_5238_, lean_object* v_category_5239_){
_start:
{
lean_object* v___x_5240_; 
v___x_5240_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5238_, v_category_5239_);
return v___x_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object* v_motive_5241_, lean_object* v_t_5242_, lean_object* v_h_5243_, lean_object* v_category_5244_){
_start:
{
lean_object* v___x_5245_; 
v___x_5245_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5242_, v_category_5244_);
return v___x_5245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object* v_t_5246_, lean_object* v_parser_5247_){
_start:
{
lean_object* v___x_5248_; 
v___x_5248_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5246_, v_parser_5247_);
return v___x_5248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object* v_motive_5249_, lean_object* v_t_5250_, lean_object* v_h_5251_, lean_object* v_parser_5252_){
_start:
{
lean_object* v___x_5253_; 
v___x_5253_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5250_, v_parser_5252_);
return v___x_5253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object* v_t_5254_, lean_object* v_alias_5255_){
_start:
{
lean_object* v___x_5256_; 
v___x_5256_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5254_, v_alias_5255_);
return v___x_5256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object* v_motive_5257_, lean_object* v_t_5258_, lean_object* v_h_5259_, lean_object* v_alias_5260_){
_start:
{
lean_object* v___x_5261_; 
v___x_5261_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5258_, v_alias_5260_);
return v___x_5261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object* v_env_5265_, lean_object* v_name_5266_){
_start:
{
uint8_t v___x_5267_; lean_object* v___x_5268_; 
v___x_5267_ = 0;
v___x_5268_ = l_Lean_Environment_find_x3f(v_env_5265_, v_name_5266_, v___x_5267_);
if (lean_obj_tag(v___x_5268_) == 0)
{
lean_object* v___x_5269_; 
v___x_5269_ = lean_box(0);
return v___x_5269_;
}
else
{
lean_object* v_val_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5317_; 
v_val_5270_ = lean_ctor_get(v___x_5268_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v___x_5268_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5272_ = v___x_5268_;
v_isShared_5273_ = v_isSharedCheck_5317_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_val_5270_);
lean_dec(v___x_5268_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5317_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5274_; 
v___x_5274_ = l_Lean_ConstantInfo_type(v_val_5270_);
lean_dec(v_val_5270_);
if (lean_obj_tag(v___x_5274_) == 4)
{
lean_object* v_declName_5275_; 
v_declName_5275_ = lean_ctor_get(v___x_5274_, 0);
lean_inc(v_declName_5275_);
lean_dec_ref_known(v___x_5274_, 2);
if (lean_obj_tag(v_declName_5275_) == 1)
{
lean_object* v_pre_5276_; 
v_pre_5276_ = lean_ctor_get(v_declName_5275_, 0);
lean_inc(v_pre_5276_);
if (lean_obj_tag(v_pre_5276_) == 1)
{
lean_object* v_pre_5277_; 
v_pre_5277_ = lean_ctor_get(v_pre_5276_, 0);
switch(lean_obj_tag(v_pre_5277_))
{
case 1:
{
lean_object* v_pre_5278_; 
lean_inc_ref(v_pre_5277_);
lean_del_object(v___x_5272_);
v_pre_5278_ = lean_ctor_get(v_pre_5277_, 0);
if (lean_obj_tag(v_pre_5278_) == 0)
{
lean_object* v_str_5279_; lean_object* v_str_5280_; lean_object* v_str_5281_; lean_object* v___x_5282_; uint8_t v___x_5283_; 
v_str_5279_ = lean_ctor_get(v_declName_5275_, 1);
lean_inc_ref(v_str_5279_);
lean_dec_ref_known(v_declName_5275_, 2);
v_str_5280_ = lean_ctor_get(v_pre_5276_, 1);
lean_inc_ref(v_str_5280_);
lean_dec_ref_known(v_pre_5276_, 2);
v_str_5281_ = lean_ctor_get(v_pre_5277_, 1);
lean_inc_ref(v_str_5281_);
lean_dec_ref_known(v_pre_5277_, 2);
v___x_5282_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5283_ = lean_string_dec_eq(v_str_5281_, v___x_5282_);
lean_dec_ref(v_str_5281_);
if (v___x_5283_ == 0)
{
lean_object* v___x_5284_; 
lean_dec_ref(v_str_5280_);
lean_dec_ref(v_str_5279_);
v___x_5284_ = lean_box(0);
return v___x_5284_;
}
else
{
lean_object* v___x_5285_; uint8_t v___x_5286_; 
v___x_5285_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_5286_ = lean_string_dec_eq(v_str_5280_, v___x_5285_);
lean_dec_ref(v_str_5280_);
if (v___x_5286_ == 0)
{
lean_object* v___x_5287_; 
lean_dec_ref(v_str_5279_);
v___x_5287_ = lean_box(0);
return v___x_5287_;
}
else
{
uint8_t v___x_5288_; 
v___x_5288_ = lean_string_dec_eq(v_str_5279_, v___x_5285_);
if (v___x_5288_ == 0)
{
lean_object* v___x_5289_; uint8_t v___x_5290_; 
v___x_5289_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_5290_ = lean_string_dec_eq(v_str_5279_, v___x_5289_);
lean_dec_ref(v_str_5279_);
if (v___x_5290_ == 0)
{
lean_object* v___x_5291_; 
v___x_5291_ = lean_box(0);
return v___x_5291_;
}
else
{
lean_object* v___x_5292_; 
v___x_5292_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5292_;
}
}
else
{
lean_object* v___x_5293_; 
lean_dec_ref(v_str_5279_);
v___x_5293_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5293_;
}
}
}
}
else
{
lean_object* v___x_5294_; 
lean_dec_ref_known(v_pre_5277_, 2);
lean_dec_ref_known(v_pre_5276_, 2);
lean_dec_ref_known(v_declName_5275_, 2);
v___x_5294_ = lean_box(0);
return v___x_5294_;
}
}
case 0:
{
lean_object* v_str_5295_; lean_object* v_str_5296_; lean_object* v___x_5297_; uint8_t v___x_5298_; 
v_str_5295_ = lean_ctor_get(v_declName_5275_, 1);
lean_inc_ref(v_str_5295_);
lean_dec_ref_known(v_declName_5275_, 2);
v_str_5296_ = lean_ctor_get(v_pre_5276_, 1);
lean_inc_ref(v_str_5296_);
lean_dec_ref_known(v_pre_5276_, 2);
v___x_5297_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5298_ = lean_string_dec_eq(v_str_5296_, v___x_5297_);
lean_dec_ref(v_str_5296_);
if (v___x_5298_ == 0)
{
lean_object* v___x_5299_; 
lean_dec_ref(v_str_5295_);
lean_del_object(v___x_5272_);
v___x_5299_ = lean_box(0);
return v___x_5299_;
}
else
{
lean_object* v___x_5300_; uint8_t v___x_5301_; 
v___x_5300_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_5301_ = lean_string_dec_eq(v_str_5295_, v___x_5300_);
if (v___x_5301_ == 0)
{
lean_object* v___x_5302_; uint8_t v___x_5303_; 
v___x_5302_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_5303_ = lean_string_dec_eq(v_str_5295_, v___x_5302_);
lean_dec_ref(v_str_5295_);
if (v___x_5303_ == 0)
{
lean_object* v___x_5304_; 
lean_del_object(v___x_5272_);
v___x_5304_ = lean_box(0);
return v___x_5304_;
}
else
{
lean_object* v___x_5305_; lean_object* v___x_5307_; 
v___x_5305_ = lean_box(v___x_5298_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 0, v___x_5305_);
v___x_5307_ = v___x_5272_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v___x_5305_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
return v___x_5307_;
}
}
}
else
{
lean_object* v___x_5309_; lean_object* v___x_5311_; 
lean_dec_ref(v_str_5295_);
v___x_5309_ = lean_box(v___x_5298_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 0, v___x_5309_);
v___x_5311_ = v___x_5272_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v___x_5309_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
return v___x_5311_;
}
}
}
}
default: 
{
lean_object* v___x_5313_; 
lean_dec_ref_known(v_pre_5276_, 2);
lean_dec_ref_known(v_declName_5275_, 2);
lean_del_object(v___x_5272_);
v___x_5313_ = lean_box(0);
return v___x_5313_;
}
}
}
else
{
lean_object* v___x_5314_; 
lean_dec(v_pre_5276_);
lean_dec_ref_known(v_declName_5275_, 2);
lean_del_object(v___x_5272_);
v___x_5314_ = lean_box(0);
return v___x_5314_;
}
}
else
{
lean_object* v___x_5315_; 
lean_dec(v_declName_5275_);
lean_del_object(v___x_5272_);
v___x_5315_ = lean_box(0);
return v___x_5315_;
}
}
else
{
lean_object* v___x_5316_; 
lean_dec_ref(v___x_5274_);
lean_del_object(v___x_5272_);
v___x_5316_ = lean_box(0);
return v___x_5316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object* v_env_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_){
_start:
{
if (lean_obj_tag(v_a_5319_) == 0)
{
lean_object* v___x_5321_; 
lean_dec_ref(v_env_5318_);
v___x_5321_ = lean_array_to_list(v_a_5320_);
return v___x_5321_;
}
else
{
lean_object* v_head_5322_; lean_object* v_snd_5323_; 
v_head_5322_ = lean_ctor_get(v_a_5319_, 0);
v_snd_5323_ = lean_ctor_get(v_head_5322_, 1);
if (lean_obj_tag(v_snd_5323_) == 0)
{
lean_object* v_tail_5324_; lean_object* v_fst_5325_; lean_object* v___x_5326_; 
lean_inc(v_head_5322_);
v_tail_5324_ = lean_ctor_get(v_a_5319_, 1);
lean_inc(v_tail_5324_);
lean_dec_ref_known(v_a_5319_, 2);
v_fst_5325_ = lean_ctor_get(v_head_5322_, 0);
lean_inc_n(v_fst_5325_, 2);
lean_dec(v_head_5322_);
lean_inc_ref(v_env_5318_);
v___x_5326_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5318_, v_fst_5325_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_dec(v_fst_5325_);
v_a_5319_ = v_tail_5324_;
goto _start;
}
else
{
lean_object* v_val_5328_; lean_object* v___x_5329_; uint8_t v___x_5330_; lean_object* v___x_5331_; 
v_val_5328_ = lean_ctor_get(v___x_5326_, 0);
lean_inc(v_val_5328_);
lean_dec_ref_known(v___x_5326_, 1);
v___x_5329_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5329_, 0, v_fst_5325_);
v___x_5330_ = lean_unbox(v_val_5328_);
lean_dec(v_val_5328_);
lean_ctor_set_uint8(v___x_5329_, sizeof(void*)*1, v___x_5330_);
v___x_5331_ = lean_array_push(v_a_5320_, v___x_5329_);
v_a_5319_ = v_tail_5324_;
v_a_5320_ = v___x_5331_;
goto _start;
}
}
else
{
lean_object* v_tail_5333_; 
v_tail_5333_ = lean_ctor_get(v_a_5319_, 1);
lean_inc(v_tail_5333_);
lean_dec_ref_known(v_a_5319_, 2);
v_a_5319_ = v_tail_5333_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object* v_env_5338_, lean_object* v_as_x27_5339_, lean_object* v_b_5340_){
_start:
{
if (lean_obj_tag(v_as_x27_5339_) == 0)
{
lean_dec_ref(v_env_5338_);
lean_inc_ref(v_b_5340_);
return v_b_5340_;
}
else
{
lean_object* v_head_5341_; lean_object* v_tail_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; 
v_head_5341_ = lean_ctor_get(v_as_x27_5339_, 0);
v_tail_5342_ = lean_ctor_get(v_as_x27_5339_, 1);
v___x_5343_ = lean_box(0);
v___x_5344_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_5341_) == 1)
{
lean_object* v_fields_5345_; 
v_fields_5345_ = lean_ctor_get(v_head_5341_, 1);
if (lean_obj_tag(v_fields_5345_) == 0)
{
lean_object* v_n_5346_; lean_object* v___x_5347_; 
v_n_5346_ = lean_ctor_get(v_head_5341_, 0);
lean_inc(v_n_5346_);
lean_inc_ref(v_env_5338_);
v___x_5347_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5338_, v_n_5346_);
if (lean_obj_tag(v___x_5347_) == 1)
{
lean_object* v_val_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5360_; 
lean_dec_ref(v_env_5338_);
v_val_5348_ = lean_ctor_get(v___x_5347_, 0);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___x_5347_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5350_ = v___x_5347_;
v_isShared_5351_ = v_isSharedCheck_5360_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_val_5348_);
lean_dec(v___x_5347_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5360_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v___x_5352_; uint8_t v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5357_; 
lean_inc(v_n_5346_);
v___x_5352_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5352_, 0, v_n_5346_);
v___x_5353_ = lean_unbox(v_val_5348_);
lean_dec(v_val_5348_);
lean_ctor_set_uint8(v___x_5352_, sizeof(void*)*1, v___x_5353_);
v___x_5354_ = lean_box(0);
v___x_5355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5355_, 0, v___x_5352_);
lean_ctor_set(v___x_5355_, 1, v___x_5354_);
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 0, v___x_5355_);
v___x_5357_ = v___x_5350_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5355_);
v___x_5357_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
lean_object* v___x_5358_; 
v___x_5358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5358_, 0, v___x_5357_);
lean_ctor_set(v___x_5358_, 1, v___x_5343_);
return v___x_5358_;
}
}
}
else
{
lean_dec(v___x_5347_);
v_as_x27_5339_ = v_tail_5342_;
v_b_5340_ = v___x_5344_;
goto _start;
}
}
else
{
v_as_x27_5339_ = v_tail_5342_;
v_b_5340_ = v___x_5344_;
goto _start;
}
}
else
{
v_as_x27_5339_ = v_tail_5342_;
v_b_5340_ = v___x_5344_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object* v_env_5364_, lean_object* v_as_x27_5365_, lean_object* v_b_5366_){
_start:
{
lean_object* v_res_5367_; 
v_res_5367_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5364_, v_as_x27_5365_, v_b_5366_);
lean_dec_ref(v_b_5366_);
lean_dec(v_as_x27_5365_);
return v_res_5367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object* v_env_5370_, lean_object* v_opts_5371_, lean_object* v_currNamespace_5372_, lean_object* v_openDecls_5373_, lean_object* v_ident_5374_){
_start:
{
if (lean_obj_tag(v_ident_5374_) == 3)
{
lean_object* v_val_5375_; lean_object* v_preresolved_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v_fst_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5414_; 
v_val_5375_ = lean_ctor_get(v_ident_5374_, 2);
lean_inc(v_val_5375_);
v_preresolved_5376_ = lean_ctor_get(v_ident_5374_, 3);
lean_inc(v_preresolved_5376_);
lean_dec_ref_known(v_ident_5374_, 4);
v___x_5377_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
lean_inc_ref(v_env_5370_);
v___x_5378_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5370_, v_preresolved_5376_, v___x_5377_);
lean_dec(v_preresolved_5376_);
v_fst_5379_ = lean_ctor_get(v___x_5378_, 0);
v_isSharedCheck_5414_ = !lean_is_exclusive(v___x_5378_);
if (v_isSharedCheck_5414_ == 0)
{
lean_object* v_unused_5415_; 
v_unused_5415_ = lean_ctor_get(v___x_5378_, 1);
lean_dec(v_unused_5415_);
v___x_5381_ = v___x_5378_;
v_isShared_5382_ = v_isSharedCheck_5414_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_fst_5379_);
lean_dec(v___x_5378_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5414_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
if (lean_obj_tag(v_fst_5379_) == 0)
{
lean_object* v___x_5383_; uint8_t v___x_5384_; 
v___x_5383_ = l_Lean_Name_eraseMacroScopes(v_val_5375_);
lean_inc_ref(v_env_5370_);
v___x_5384_ = l_Lean_Parser_isParserCategory(v_env_5370_, v___x_5383_);
if (v___x_5384_ == 0)
{
lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; uint8_t v___x_5388_; 
lean_inc_ref_n(v_env_5370_, 2);
v___x_5385_ = l_Lean_ResolveName_resolveGlobalName(v_env_5370_, v_opts_5371_, v_currNamespace_5372_, v_openDecls_5373_, v_val_5375_);
v___x_5386_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0));
v___x_5387_ = l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(v_env_5370_, v___x_5385_, v___x_5386_);
v___x_5388_ = l_List_isEmpty___redArg(v___x_5387_);
if (v___x_5388_ == 0)
{
lean_dec(v___x_5383_);
lean_del_object(v___x_5381_);
lean_dec_ref(v_env_5370_);
return v___x_5387_;
}
else
{
lean_object* v___x_5389_; lean_object* v_asyncMode_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; 
lean_dec(v___x_5387_);
v___x_5389_ = l_Lean_Parser_aliasExtension;
v_asyncMode_5390_ = lean_ctor_get(v___x_5389_, 2);
v___x_5391_ = lean_box(1);
v___x_5392_ = lean_box(0);
v___x_5393_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5391_, v___x_5389_, v_env_5370_, v_asyncMode_5390_, v___x_5392_, v___x_5384_);
v___x_5394_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5393_, v___x_5383_);
lean_dec(v___x_5383_);
lean_dec(v___x_5393_);
if (lean_obj_tag(v___x_5394_) == 1)
{
lean_object* v_val_5395_; lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5406_; 
v_val_5395_ = lean_ctor_get(v___x_5394_, 0);
v_isSharedCheck_5406_ = !lean_is_exclusive(v___x_5394_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5397_ = v___x_5394_;
v_isShared_5398_ = v_isSharedCheck_5406_;
goto v_resetjp_5396_;
}
else
{
lean_inc(v_val_5395_);
lean_dec(v___x_5394_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5406_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
lean_object* v___x_5400_; 
if (v_isShared_5398_ == 0)
{
lean_ctor_set_tag(v___x_5397_, 2);
v___x_5400_ = v___x_5397_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_val_5395_);
v___x_5400_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
lean_object* v___x_5401_; lean_object* v___x_5403_; 
v___x_5401_ = lean_box(0);
if (v_isShared_5382_ == 0)
{
lean_ctor_set_tag(v___x_5381_, 1);
lean_ctor_set(v___x_5381_, 1, v___x_5401_);
lean_ctor_set(v___x_5381_, 0, v___x_5400_);
v___x_5403_ = v___x_5381_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v___x_5400_);
lean_ctor_set(v_reuseFailAlloc_5404_, 1, v___x_5401_);
v___x_5403_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
return v___x_5403_;
}
}
}
}
else
{
lean_object* v___x_5407_; 
lean_dec(v___x_5394_);
lean_del_object(v___x_5381_);
v___x_5407_ = lean_box(0);
return v___x_5407_;
}
}
}
else
{
lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5411_; 
lean_dec(v_val_5375_);
lean_dec(v_openDecls_5373_);
lean_dec(v_currNamespace_5372_);
lean_dec_ref(v_env_5370_);
v___x_5408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5408_, 0, v___x_5383_);
v___x_5409_ = lean_box(0);
if (v_isShared_5382_ == 0)
{
lean_ctor_set_tag(v___x_5381_, 1);
lean_ctor_set(v___x_5381_, 1, v___x_5409_);
lean_ctor_set(v___x_5381_, 0, v___x_5408_);
v___x_5411_ = v___x_5381_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v___x_5408_);
lean_ctor_set(v_reuseFailAlloc_5412_, 1, v___x_5409_);
v___x_5411_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
return v___x_5411_;
}
}
}
else
{
lean_object* v_val_5413_; 
lean_del_object(v___x_5381_);
lean_dec(v_val_5375_);
lean_dec(v_openDecls_5373_);
lean_dec(v_currNamespace_5372_);
lean_dec_ref(v_env_5370_);
v_val_5413_ = lean_ctor_get(v_fst_5379_, 0);
lean_inc(v_val_5413_);
lean_dec_ref_known(v_fst_5379_, 1);
return v_val_5413_;
}
}
}
else
{
lean_object* v___x_5416_; 
lean_dec(v_ident_5374_);
lean_dec(v_openDecls_5373_);
lean_dec(v_currNamespace_5372_);
lean_dec_ref(v_env_5370_);
v___x_5416_ = lean_box(0);
return v___x_5416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object* v_env_5417_, lean_object* v_opts_5418_, lean_object* v_currNamespace_5419_, lean_object* v_openDecls_5420_, lean_object* v_ident_5421_){
_start:
{
lean_object* v_res_5422_; 
v_res_5422_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5417_, v_opts_5418_, v_currNamespace_5419_, v_openDecls_5420_, v_ident_5421_);
lean_dec_ref(v_opts_5418_);
return v_res_5422_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object* v_env_5423_, lean_object* v_as_5424_, lean_object* v_as_x27_5425_, lean_object* v_b_5426_, lean_object* v_a_5427_){
_start:
{
lean_object* v___x_5428_; 
v___x_5428_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5423_, v_as_x27_5425_, v_b_5426_);
return v___x_5428_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object* v_env_5429_, lean_object* v_as_5430_, lean_object* v_as_x27_5431_, lean_object* v_b_5432_, lean_object* v_a_5433_){
_start:
{
lean_object* v_res_5434_; 
v_res_5434_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(v_env_5429_, v_as_5430_, v_as_x27_5431_, v_b_5432_, v_a_5433_);
lean_dec_ref(v_b_5432_);
lean_dec(v_as_x27_5431_);
lean_dec(v_as_5430_);
return v_res_5434_;
}
}
lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object* v_ctx_5435_, lean_object* v_id_5436_, uint8_t v_unsetExporting_5437_){
_start:
{
lean_object* v___y_5439_; 
if (v_unsetExporting_5437_ == 0)
{
lean_object* v_toParserModuleContext_5445_; lean_object* v_env_5446_; 
v_toParserModuleContext_5445_ = lean_ctor_get(v_ctx_5435_, 1);
v_env_5446_ = lean_ctor_get(v_toParserModuleContext_5445_, 0);
lean_inc_ref(v_env_5446_);
v___y_5439_ = v_env_5446_;
goto v___jp_5438_;
}
else
{
lean_object* v_toParserModuleContext_5447_; lean_object* v_env_5448_; uint8_t v___x_5449_; lean_object* v___x_5450_; 
v_toParserModuleContext_5447_ = lean_ctor_get(v_ctx_5435_, 1);
v_env_5448_ = lean_ctor_get(v_toParserModuleContext_5447_, 0);
v___x_5449_ = 0;
lean_inc_ref(v_env_5448_);
v___x_5450_ = l_Lean_Environment_setExporting(v_env_5448_, v___x_5449_);
v___y_5439_ = v___x_5450_;
goto v___jp_5438_;
}
v___jp_5438_:
{
lean_object* v_toParserModuleContext_5440_; lean_object* v_options_5441_; lean_object* v_currNamespace_5442_; lean_object* v_openDecls_5443_; lean_object* v___x_5444_; 
v_toParserModuleContext_5440_ = lean_ctor_get(v_ctx_5435_, 1);
lean_inc_ref(v_toParserModuleContext_5440_);
lean_dec_ref(v_ctx_5435_);
v_options_5441_ = lean_ctor_get(v_toParserModuleContext_5440_, 1);
lean_inc_ref(v_options_5441_);
v_currNamespace_5442_ = lean_ctor_get(v_toParserModuleContext_5440_, 2);
lean_inc(v_currNamespace_5442_);
v_openDecls_5443_ = lean_ctor_get(v_toParserModuleContext_5440_, 3);
lean_inc(v_openDecls_5443_);
lean_dec_ref(v_toParserModuleContext_5440_);
v___x_5444_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v___y_5439_, v_options_5441_, v_currNamespace_5442_, v_openDecls_5443_, v_id_5436_);
lean_dec_ref(v_options_5441_);
return v___x_5444_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_ParserContext_resolveParserName_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_5435_ = stack[0].m_obj;
lean_object* v_id_5436_ = stack[1].m_obj;
uint8_t v_unsetExporting_5437_ = stack[2].m_num;
lean_object* v_res_5451_;
v_res_5451_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5435_, v_id_5436_, v_unsetExporting_5437_);
stack->m_obj
 = v_res_5451_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object* v_ctx_5452_, lean_object* v_id_5453_, lean_object* v_unsetExporting_5454_){
_start:
{
uint8_t v_unsetExporting_boxed_5455_; lean_object* v_res_5456_; 
v_unsetExporting_boxed_5455_ = lean_unbox(v_unsetExporting_5454_);
v_res_5456_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5452_, v_id_5453_, v_unsetExporting_boxed_5455_);
return v_res_5456_;
}
}
lean_object* l_Lean_Parser_resolveParserName(lean_object* v_id_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_){
_start:
{
lean_object* v___x_5461_; lean_object* v_toCold_5462_; lean_object* v_env_5463_; lean_object* v_currNamespace_5464_; lean_object* v_openDecls_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; 
v___x_5461_ = lean_st_ref_get(v_a_5459_);
v_toCold_5462_ = lean_ctor_get(v_a_5458_, 0);
v_env_5463_ = lean_ctor_get(v___x_5461_, 0);
lean_inc_ref(v_env_5463_);
lean_dec(v___x_5461_);
v_currNamespace_5464_ = lean_ctor_get(v_toCold_5462_, 4);
v_openDecls_5465_ = lean_ctor_get(v_toCold_5462_, 5);
v___x_5466_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_5458_);
lean_inc(v_openDecls_5465_);
lean_inc(v_currNamespace_5464_);
v___x_5467_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5463_, v___x_5466_, v_currNamespace_5464_, v_openDecls_5465_, v_id_5457_);
lean_dec_ref(v___x_5466_);
v___x_5468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5468_, 0, v___x_5467_);
return v___x_5468_;
}
}
LEAN_EXPORT void l_Lean_Parser_resolveParserName_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_5457_ = stack[0].m_obj;
lean_object* v_a_5458_ = stack[1].m_obj;
lean_object* v_a_5459_ = stack[2].m_obj;
lean_object* v_res_5469_;
v_res_5469_ = l_Lean_Parser_resolveParserName(v_id_5457_, v_a_5458_, v_a_5459_);
stack->m_obj
 = v_res_5469_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object* v_id_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_){
_start:
{
lean_object* v_res_5474_; 
v_res_5474_ = l_Lean_Parser_resolveParserName(v_id_5470_, v_a_5471_, v_a_5472_);
lean_dec(v_a_5472_);
lean_dec_ref(v_a_5471_);
return v_res_5474_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object* v_x_5475_, lean_object* v_x_5476_){
_start:
{
if (lean_obj_tag(v_x_5475_) == 0)
{
if (lean_obj_tag(v_x_5476_) == 0)
{
uint8_t v___x_5477_; 
v___x_5477_ = 1;
return v___x_5477_;
}
else
{
uint8_t v___x_5478_; 
v___x_5478_ = 0;
return v___x_5478_;
}
}
else
{
if (lean_obj_tag(v_x_5476_) == 0)
{
uint8_t v___x_5479_; 
v___x_5479_ = 0;
return v___x_5479_;
}
else
{
lean_object* v_val_5480_; lean_object* v_val_5481_; uint8_t v___x_5482_; 
v_val_5480_ = lean_ctor_get(v_x_5475_, 0);
v_val_5481_ = lean_ctor_get(v_x_5476_, 0);
v___x_5482_ = l_Lean_Parser_instBEqError_beq(v_val_5480_, v_val_5481_);
return v___x_5482_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5475_ = stack[0].m_obj;
lean_object* v_x_5476_ = stack[1].m_obj;
uint8_t v_res_5483_;
v_res_5483_ = l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5475_, v_x_5476_);
stack->m_num = v_res_5483_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object* v_x_5484_, lean_object* v_x_5485_){
_start:
{
uint8_t v_res_5486_; lean_object* v_r_5487_; 
v_res_5486_ = l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5484_, v_x_5485_);
lean_dec(v_x_5485_);
lean_dec(v_x_5484_);
v_r_5487_ = lean_box(v_res_5486_);
return v_r_5487_;
}
}
lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t v___x_5488_, lean_object* v_ctx_5489_){
_start:
{
lean_object* v_toParserModuleContext_5490_; lean_object* v_toInputContext_5491_; lean_object* v_toCacheableParserContext_5492_; lean_object* v_tokens_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5518_; 
v_toParserModuleContext_5490_ = lean_ctor_get(v_ctx_5489_, 1);
v_toInputContext_5491_ = lean_ctor_get(v_ctx_5489_, 0);
v_toCacheableParserContext_5492_ = lean_ctor_get(v_ctx_5489_, 2);
v_tokens_5493_ = lean_ctor_get(v_ctx_5489_, 3);
v_isSharedCheck_5518_ = !lean_is_exclusive(v_ctx_5489_);
if (v_isSharedCheck_5518_ == 0)
{
v___x_5495_ = v_ctx_5489_;
v_isShared_5496_ = v_isSharedCheck_5518_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_tokens_5493_);
lean_inc(v_toCacheableParserContext_5492_);
lean_inc(v_toParserModuleContext_5490_);
lean_inc(v_toInputContext_5491_);
lean_dec(v_ctx_5489_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5518_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v_env_5497_; lean_object* v_options_5498_; lean_object* v_currNamespace_5499_; lean_object* v_openDecls_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5517_; 
v_env_5497_ = lean_ctor_get(v_toParserModuleContext_5490_, 0);
v_options_5498_ = lean_ctor_get(v_toParserModuleContext_5490_, 1);
v_currNamespace_5499_ = lean_ctor_get(v_toParserModuleContext_5490_, 2);
v_openDecls_5500_ = lean_ctor_get(v_toParserModuleContext_5490_, 3);
v_isSharedCheck_5517_ = !lean_is_exclusive(v_toParserModuleContext_5490_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5502_ = v_toParserModuleContext_5490_;
v_isShared_5503_ = v_isSharedCheck_5517_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_openDecls_5500_);
lean_inc(v_currNamespace_5499_);
lean_inc(v_options_5498_);
lean_inc(v_env_5497_);
lean_dec(v_toParserModuleContext_5490_);
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5517_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v___x_5504_; uint8_t v___y_5506_; lean_object* v___x_5514_; uint8_t v___x_5515_; 
v___x_5504_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_5514_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_5515_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_5498_, v___x_5514_);
if (v___x_5515_ == 0)
{
uint8_t v___x_5516_; 
v___x_5516_ = 1;
v___y_5506_ = v___x_5516_;
goto v___jp_5505_;
}
else
{
v___y_5506_ = v___x_5488_;
goto v___jp_5505_;
}
v___jp_5505_:
{
lean_object* v___x_5507_; lean_object* v___x_5509_; 
v___x_5507_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_5498_, v___x_5504_, v___y_5506_);
if (v_isShared_5503_ == 0)
{
lean_ctor_set(v___x_5502_, 1, v___x_5507_);
v___x_5509_ = v___x_5502_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_env_5497_);
lean_ctor_set(v_reuseFailAlloc_5513_, 1, v___x_5507_);
lean_ctor_set(v_reuseFailAlloc_5513_, 2, v_currNamespace_5499_);
lean_ctor_set(v_reuseFailAlloc_5513_, 3, v_openDecls_5500_);
v___x_5509_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
lean_object* v___x_5511_; 
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 1, v___x_5509_);
v___x_5511_ = v___x_5495_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_toInputContext_5491_);
lean_ctor_set(v_reuseFailAlloc_5512_, 1, v___x_5509_);
lean_ctor_set(v_reuseFailAlloc_5512_, 2, v_toCacheableParserContext_5492_);
lean_ctor_set(v_reuseFailAlloc_5512_, 3, v_tokens_5493_);
v___x_5511_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
return v___x_5511_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_parserOfStackFn___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_5488_ = stack[0].m_num;
lean_object* v_ctx_5489_ = stack[1].m_obj;
lean_object* v_res_5519_;
v_res_5519_ = l_Lean_Parser_parserOfStackFn___lam__0(v___x_5488_, v_ctx_5489_);
stack->m_obj
 = v_res_5519_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object* v___x_5520_, lean_object* v_ctx_5521_){
_start:
{
uint8_t v___x_1079__boxed_5522_; lean_object* v_res_5523_; 
v___x_1079__boxed_5522_ = lean_unbox(v___x_5520_);
v_res_5523_ = l_Lean_Parser_parserOfStackFn___lam__0(v___x_1079__boxed_5522_, v_ctx_5521_);
return v_res_5523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* v_offset_5531_, lean_object* v_ctx_5532_, lean_object* v_s_5533_){
_start:
{
lean_object* v_stxStack_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; uint8_t v___x_5538_; 
v_stxStack_5534_ = lean_ctor_get(v_s_5533_, 0);
v___x_5535_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5534_);
v___x_5536_ = lean_unsigned_to_nat(1u);
v___x_5537_ = lean_nat_add(v_offset_5531_, v___x_5536_);
v___x_5538_ = lean_nat_dec_lt(v___x_5535_, v___x_5537_);
lean_dec(v___x_5537_);
if (v___x_5538_ == 0)
{
lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; 
v___x_5539_ = lean_nat_sub(v___x_5535_, v_offset_5531_);
lean_dec(v___x_5535_);
v___x_5540_ = lean_nat_sub(v___x_5539_, v___x_5536_);
lean_dec(v___x_5539_);
v___x_5541_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5534_, v___x_5540_);
lean_dec(v___x_5540_);
if (lean_obj_tag(v___x_5541_) == 3)
{
uint8_t v___x_5553_; lean_object* v___x_5554_; 
v___x_5553_ = 1;
lean_inc_ref(v___x_5541_);
lean_inc_ref(v_ctx_5532_);
v___x_5554_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5532_, v___x_5541_, v___x_5553_);
if (lean_obj_tag(v___x_5554_) == 0)
{
lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; 
lean_dec_ref(v_ctx_5532_);
v___x_5555_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__1));
v___x_5556_ = lean_box(0);
v___x_5557_ = l_Lean_Syntax_formatStx(v___x_5541_, v___x_5556_, v___x_5538_);
v___x_5558_ = l_Std_Format_defWidth;
v___x_5559_ = lean_unsigned_to_nat(0u);
v___x_5560_ = l_Std_Format_pretty(v___x_5557_, v___x_5558_, v___x_5559_, v___x_5559_);
v___x_5561_ = lean_string_append(v___x_5555_, v___x_5560_);
lean_dec_ref(v___x_5560_);
v___x_5562_ = lean_box(0);
v___x_5563_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5533_, v___x_5561_, v___x_5562_, v___x_5553_);
return v___x_5563_;
}
else
{
lean_object* v_head_5564_; lean_object* v_tail_5565_; lean_object* v_iniSz_5566_; lean_object* v_s_5568_; 
v_head_5564_ = lean_ctor_get(v___x_5554_, 0);
lean_inc(v_head_5564_);
v_tail_5565_ = lean_ctor_get(v___x_5554_, 1);
lean_inc(v_tail_5565_);
lean_dec_ref_known(v___x_5554_, 2);
v_iniSz_5566_ = l_Lean_Parser_ParserState_stackSize(v_s_5533_);
switch(lean_obj_tag(v_head_5564_))
{
case 0:
{
if (lean_obj_tag(v_tail_5565_) == 0)
{
lean_object* v_cat_5578_; lean_object* v___x_5579_; 
lean_dec_ref_known(v___x_5541_, 4);
v_cat_5578_ = lean_ctor_get(v_head_5564_, 0);
lean_inc(v_cat_5578_);
lean_dec_ref_known(v_head_5564_, 1);
v___x_5579_ = l_Lean_Parser_categoryParserFn(v_cat_5578_, v_ctx_5532_, v_s_5533_);
v_s_5568_ = v___x_5579_;
goto v___jp_5567_;
}
else
{
lean_dec_ref_known(v_tail_5565_, 2);
lean_dec_ref_known(v_head_5564_, 1);
lean_dec(v_iniSz_5566_);
lean_dec_ref(v_ctx_5532_);
goto v___jp_5542_;
}
}
case 1:
{
if (lean_obj_tag(v_tail_5565_) == 0)
{
lean_object* v_decl_5580_; lean_object* v___x_5581_; lean_object* v___f_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; 
lean_dec_ref_known(v___x_5541_, 4);
v_decl_5580_ = lean_ctor_get(v_head_5564_, 0);
lean_inc(v_decl_5580_);
lean_dec_ref_known(v_head_5564_, 1);
v___x_5581_ = lean_box(v___x_5538_);
v___f_5582_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5582_, 0, v___x_5581_);
v___x_5583_ = lean_box(0);
v___x_5584_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_5584_, 0, v_decl_5580_);
lean_closure_set(v___x_5584_, 1, v___x_5583_);
v___x_5585_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5582_, v___x_5584_, v_ctx_5532_, v_s_5533_);
v_s_5568_ = v___x_5585_;
goto v___jp_5567_;
}
else
{
lean_dec_ref_known(v_tail_5565_, 2);
lean_dec_ref_known(v_head_5564_, 1);
lean_dec(v_iniSz_5566_);
lean_dec_ref(v_ctx_5532_);
goto v___jp_5542_;
}
}
default: 
{
if (lean_obj_tag(v_tail_5565_) == 0)
{
lean_object* v_p_5586_; 
v_p_5586_ = lean_ctor_get(v_head_5564_, 0);
lean_inc_ref(v_p_5586_);
lean_dec_ref_known(v_head_5564_, 1);
if (lean_obj_tag(v_p_5586_) == 0)
{
lean_object* v_p_5587_; lean_object* v_fn_5588_; lean_object* v___x_5589_; 
lean_dec_ref_known(v___x_5541_, 4);
v_p_5587_ = lean_ctor_get(v_p_5586_, 0);
lean_inc(v_p_5587_);
lean_dec_ref_known(v_p_5586_, 1);
v_fn_5588_ = lean_ctor_get(v_p_5587_, 1);
lean_inc_ref(v_fn_5588_);
lean_dec(v_p_5587_);
v___x_5589_ = lean_apply_2(v_fn_5588_, v_ctx_5532_, v_s_5533_);
v_s_5568_ = v___x_5589_;
goto v___jp_5567_;
}
else
{
lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; 
lean_dec_ref(v_p_5586_);
lean_dec(v_iniSz_5566_);
lean_dec_ref(v_ctx_5532_);
v___x_5590_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__3));
v___x_5591_ = lean_box(0);
v___x_5592_ = l_Lean_Syntax_formatStx(v___x_5541_, v___x_5591_, v___x_5538_);
v___x_5593_ = l_Std_Format_defWidth;
v___x_5594_ = lean_unsigned_to_nat(0u);
v___x_5595_ = l_Std_Format_pretty(v___x_5592_, v___x_5593_, v___x_5594_, v___x_5594_);
v___x_5596_ = lean_string_append(v___x_5590_, v___x_5595_);
lean_dec_ref(v___x_5595_);
v___x_5597_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__4));
v___x_5598_ = lean_string_append(v___x_5596_, v___x_5597_);
v___x_5599_ = lean_box(0);
v___x_5600_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5533_, v___x_5598_, v___x_5599_, v___x_5553_);
return v___x_5600_;
}
}
else
{
lean_dec_ref_known(v_tail_5565_, 2);
lean_dec_ref_known(v_head_5564_, 1);
lean_dec(v_iniSz_5566_);
lean_dec_ref(v_ctx_5532_);
goto v___jp_5542_;
}
}
}
v___jp_5567_:
{
lean_object* v_errorMsg_5569_; lean_object* v___x_5570_; uint8_t v___x_5571_; 
v_errorMsg_5569_ = lean_ctor_get(v_s_5568_, 4);
v___x_5570_ = lean_box(0);
v___x_5571_ = l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_errorMsg_5569_, v___x_5570_);
if (v___x_5571_ == 0)
{
lean_dec(v_iniSz_5566_);
return v_s_5568_;
}
else
{
lean_object* v___x_5572_; lean_object* v___x_5573_; uint8_t v___x_5574_; 
v___x_5572_ = l_Lean_Parser_ParserState_stackSize(v_s_5568_);
v___x_5573_ = lean_nat_add(v_iniSz_5566_, v___x_5536_);
lean_dec(v_iniSz_5566_);
v___x_5574_ = lean_nat_dec_eq(v___x_5572_, v___x_5573_);
lean_dec(v___x_5573_);
lean_dec(v___x_5572_);
if (v___x_5574_ == 0)
{
lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; 
v___x_5575_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__2));
v___x_5576_ = lean_box(0);
v___x_5577_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5568_, v___x_5575_, v___x_5576_, v___x_5571_);
return v___x_5577_;
}
else
{
return v_s_5568_;
}
}
}
}
}
else
{
lean_object* v___x_5601_; lean_object* v___x_5602_; uint8_t v___x_5603_; lean_object* v___x_5604_; 
lean_dec(v___x_5541_);
lean_dec_ref(v_ctx_5532_);
v___x_5601_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__5));
v___x_5602_ = lean_box(0);
v___x_5603_ = 1;
v___x_5604_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5533_, v___x_5601_, v___x_5602_, v___x_5603_);
return v___x_5604_;
}
v___jp_5542_:
{
lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; uint8_t v___x_5551_; lean_object* v___x_5552_; 
v___x_5543_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__0));
v___x_5544_ = lean_box(0);
v___x_5545_ = l_Lean_Syntax_formatStx(v___x_5541_, v___x_5544_, v___x_5538_);
v___x_5546_ = l_Std_Format_defWidth;
v___x_5547_ = lean_unsigned_to_nat(0u);
v___x_5548_ = l_Std_Format_pretty(v___x_5545_, v___x_5546_, v___x_5547_, v___x_5547_);
v___x_5549_ = lean_string_append(v___x_5543_, v___x_5548_);
lean_dec_ref(v___x_5548_);
v___x_5550_ = lean_box(0);
v___x_5551_ = 1;
v___x_5552_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5533_, v___x_5549_, v___x_5550_, v___x_5551_);
return v___x_5552_;
}
}
else
{
lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; 
lean_dec(v___x_5535_);
lean_dec_ref(v_ctx_5532_);
v___x_5605_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__6));
v___x_5606_ = lean_box(0);
v___x_5607_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5533_, v___x_5605_, v___x_5606_, v___x_5538_);
return v___x_5607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* v_offset_5608_, lean_object* v_ctx_5609_, lean_object* v_s_5610_){
_start:
{
lean_object* v_res_5611_; 
v_res_5611_ = l_Lean_Parser_parserOfStackFn(v_offset_5608_, v_ctx_5609_, v_s_5610_);
lean_dec(v_offset_5608_);
return v_res_5611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object* v_prec_5612_, lean_object* v_x_5613_){
_start:
{
lean_object* v_quotDepth_5614_; uint8_t v_suppressInsideQuot_5615_; lean_object* v_savedPos_x3f_5616_; lean_object* v_forbiddenTks_5617_; lean_object* v___x_5619_; uint8_t v_isShared_5620_; uint8_t v_isSharedCheck_5624_; 
v_quotDepth_5614_ = lean_ctor_get(v_x_5613_, 1);
v_suppressInsideQuot_5615_ = lean_ctor_get_uint8(v_x_5613_, sizeof(void*)*4);
v_savedPos_x3f_5616_ = lean_ctor_get(v_x_5613_, 2);
v_forbiddenTks_5617_ = lean_ctor_get(v_x_5613_, 3);
v_isSharedCheck_5624_ = !lean_is_exclusive(v_x_5613_);
if (v_isSharedCheck_5624_ == 0)
{
lean_object* v_unused_5625_; 
v_unused_5625_ = lean_ctor_get(v_x_5613_, 0);
lean_dec(v_unused_5625_);
v___x_5619_ = v_x_5613_;
v_isShared_5620_ = v_isSharedCheck_5624_;
goto v_resetjp_5618_;
}
else
{
lean_inc(v_forbiddenTks_5617_);
lean_inc(v_savedPos_x3f_5616_);
lean_inc(v_quotDepth_5614_);
lean_dec(v_x_5613_);
v___x_5619_ = lean_box(0);
v_isShared_5620_ = v_isSharedCheck_5624_;
goto v_resetjp_5618_;
}
v_resetjp_5618_:
{
lean_object* v___x_5622_; 
if (v_isShared_5620_ == 0)
{
lean_ctor_set(v___x_5619_, 0, v_prec_5612_);
v___x_5622_ = v___x_5619_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_prec_5612_);
lean_ctor_set(v_reuseFailAlloc_5623_, 1, v_quotDepth_5614_);
lean_ctor_set(v_reuseFailAlloc_5623_, 2, v_savedPos_x3f_5616_);
lean_ctor_set(v_reuseFailAlloc_5623_, 3, v_forbiddenTks_5617_);
lean_ctor_set_uint8(v_reuseFailAlloc_5623_, sizeof(void*)*4, v_suppressInsideQuot_5615_);
v___x_5622_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
return v___x_5622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object* v___y_5626_){
_start:
{
lean_inc(v___y_5626_);
return v___y_5626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object* v___y_5627_){
_start:
{
lean_object* v_res_5628_; 
v_res_5628_ = l_Lean_Parser_parserOfStack___lam__1(v___y_5627_);
lean_dec(v___y_5627_);
return v_res_5628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object* v___y_5629_){
_start:
{
lean_inc_ref(v___y_5629_);
return v___y_5629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object* v___y_5630_){
_start:
{
lean_object* v_res_5631_; 
v_res_5631_ = l_Lean_Parser_parserOfStack___lam__2(v___y_5630_);
lean_dec_ref(v___y_5630_);
return v_res_5631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* v_offset_5638_, lean_object* v_prec_5639_){
_start:
{
lean_object* v___f_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; 
v___f_5640_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___lam__0), 2, 1);
lean_closure_set(v___f_5640_, 0, v_prec_5639_);
v___x_5641_ = ((lean_object*)(l_Lean_Parser_parserOfStack___closed__2));
v___x_5642_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___boxed), 3, 1);
lean_closure_set(v___x_5642_, 0, v_offset_5638_);
v___x_5643_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5643_, 0, v___f_5640_);
lean_closure_set(v___x_5643_, 1, v___x_5642_);
v___x_5644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5644_, 0, v___x_5641_);
lean_ctor_set(v___x_5644_, 1, v___x_5643_);
return v___x_5644_;
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
