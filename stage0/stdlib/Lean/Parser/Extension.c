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
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory(lean_object* v_env_2409_, lean_object* v_catName_2410_, lean_object* v_declName_2411_, uint8_t v_behavior_2412_){
_start:
{
uint8_t v___x_2413_; 
lean_inc_ref(v_env_2409_);
v___x_2413_ = l_Lean_Parser_isParserCategory(v_env_2409_, v_catName_2410_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2414_ = l_Lean_Parser_parserExtension;
v___x_2415_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_2415_, 0, v_catName_2410_);
lean_ctor_set(v___x_2415_, 1, v_declName_2411_);
lean_ctor_set_uint8(v___x_2415_, sizeof(void*)*2, v_behavior_2412_);
v___x_2416_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_2414_, v_env_2409_, v___x_2415_);
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
return v___x_2417_;
}
else
{
lean_object* v___x_2418_; 
lean_dec(v_declName_2411_);
lean_dec_ref(v_env_2409_);
v___x_2418_ = l___private_Lean_Parser_Extension_0__Lean_Parser_throwParserCategoryAlreadyDefined___redArg(v_catName_2410_);
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addParserCategory___boxed(lean_object* v_env_2419_, lean_object* v_catName_2420_, lean_object* v_declName_2421_, lean_object* v_behavior_2422_){
_start:
{
uint8_t v_behavior_boxed_2423_; lean_object* v_res_2424_; 
v_behavior_boxed_2423_ = lean_unbox(v_behavior_2422_);
v_res_2424_ = l_Lean_Parser_addParserCategory(v_env_2419_, v_catName_2420_, v_declName_2421_, v_behavior_boxed_2423_);
return v_res_2424_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_leadingIdentBehavior(lean_object* v_env_2425_, lean_object* v_catName_2426_){
_start:
{
lean_object* v___x_2427_; lean_object* v_ext_2428_; lean_object* v_toEnvExtension_2429_; lean_object* v_asyncMode_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v_categories_2434_; lean_object* v___x_2435_; 
v___x_2427_ = l_Lean_Parser_parserExtension;
v_ext_2428_ = lean_ctor_get(v___x_2427_, 1);
v_toEnvExtension_2429_ = lean_ctor_get(v_ext_2428_, 0);
v_asyncMode_2430_ = lean_ctor_get(v_toEnvExtension_2429_, 2);
v___x_2431_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2432_ = 0;
v___x_2433_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2431_, v___x_2427_, v_env_2425_, v_asyncMode_2430_, v___x_2432_);
v_categories_2434_ = lean_ctor_get(v___x_2433_, 2);
lean_inc_ref(v_categories_2434_);
lean_dec(v___x_2433_);
v___x_2435_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2434_, v_catName_2426_);
lean_dec_ref(v_categories_2434_);
if (lean_obj_tag(v___x_2435_) == 0)
{
uint8_t v___x_2436_; 
v___x_2436_ = 0;
return v___x_2436_;
}
else
{
lean_object* v_val_2437_; uint8_t v_behavior_2438_; 
v_val_2437_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_val_2437_);
lean_dec_ref_known(v___x_2435_, 1);
v_behavior_2438_ = lean_ctor_get_uint8(v_val_2437_, sizeof(void*)*3);
lean_dec(v_val_2437_);
return v_behavior_2438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingIdentBehavior___boxed(lean_object* v_env_2439_, lean_object* v_catName_2440_){
_start:
{
uint8_t v_res_2441_; lean_object* v_r_2442_; 
v_res_2441_ = l_Lean_Parser_leadingIdentBehavior(v_env_2439_, v_catName_2440_);
lean_dec(v_catName_2440_);
v_r_2442_ = lean_box(v_res_2441_);
return v_r_2442_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(lean_object* v_x_2443_, lean_object* v_x_2444_){
_start:
{
if (lean_obj_tag(v_x_2444_) == 0)
{
return v_x_2443_;
}
else
{
lean_object* v_head_2445_; lean_object* v_tail_2446_; lean_object* v___x_2447_; 
v_head_2445_ = lean_ctor_get(v_x_2444_, 0);
lean_inc_n(v_head_2445_, 2);
v_tail_2446_ = lean_ctor_get(v_x_2444_, 1);
lean_inc(v_tail_2446_);
lean_dec_ref_known(v_x_2444_, 2);
v___x_2447_ = l_Lean_Data_Trie_insert___redArg(v_x_2443_, v_head_2445_, v_head_2445_);
lean_dec(v_head_2445_);
v_x_2443_ = v___x_2447_;
v_x_2444_ = v_tail_2446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__0(lean_object* v_info_2449_, lean_object* v_ctx_2450_){
_start:
{
lean_object* v_toInputContext_2451_; lean_object* v_toParserModuleContext_2452_; lean_object* v_toCacheableParserContext_2453_; lean_object* v_tokens_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2465_; 
v_toInputContext_2451_ = lean_ctor_get(v_ctx_2450_, 0);
v_toParserModuleContext_2452_ = lean_ctor_get(v_ctx_2450_, 1);
v_toCacheableParserContext_2453_ = lean_ctor_get(v_ctx_2450_, 2);
v_tokens_2454_ = lean_ctor_get(v_ctx_2450_, 3);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_ctx_2450_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2456_ = v_ctx_2450_;
v_isShared_2457_ = v_isSharedCheck_2465_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_tokens_2454_);
lean_inc(v_toCacheableParserContext_2453_);
lean_inc(v_toParserModuleContext_2452_);
lean_inc(v_toInputContext_2451_);
lean_dec(v_ctx_2450_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2465_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v_collectTokens_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2463_; 
v_collectTokens_2458_ = lean_ctor_get(v_info_2449_, 0);
lean_inc_ref(v_collectTokens_2458_);
lean_dec_ref(v_info_2449_);
v___x_2459_ = lean_box(0);
v___x_2460_ = lean_apply_1(v_collectTokens_2458_, v___x_2459_);
v___x_2461_ = l_List_foldl___at___00Lean_Parser_evalParserConstUnsafe_spec__0(v_tokens_2454_, v___x_2460_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 3, v___x_2461_);
v___x_2463_ = v___x_2456_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_toInputContext_2451_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_toParserModuleContext_2452_);
lean_ctor_set(v_reuseFailAlloc_2464_, 2, v_toCacheableParserContext_2453_);
lean_ctor_set(v_reuseFailAlloc_2464_, 3, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1(lean_object* v_categories_2466_, lean_object* v_declName_2467_, lean_object* v___x_2468_, lean_object* v_ctx_2469_, lean_object* v_s_2470_, lean_object* v_evalFallback_x3f_2471_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_Parser_mkParserOfConstant(v_categories_2466_, v_declName_2467_, v___x_2468_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v_snd_2475_; lean_object* v_info_2476_; lean_object* v_fn_2477_; lean_object* v___f_2478_; lean_object* v___x_2479_; 
lean_dec(v_evalFallback_x3f_2471_);
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v_snd_2475_ = lean_ctor_get(v_a_2474_, 1);
lean_inc(v_snd_2475_);
lean_dec(v_a_2474_);
v_info_2476_ = lean_ctor_get(v_snd_2475_, 0);
lean_inc_ref(v_info_2476_);
v_fn_2477_ = lean_ctor_get(v_snd_2475_, 1);
lean_inc_ref(v_fn_2477_);
lean_dec(v_snd_2475_);
v___f_2478_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__0), 2, 1);
lean_closure_set(v___f_2478_, 0, v_info_2476_);
v___x_2479_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2478_, v_fn_2477_, v_ctx_2469_, v_s_2470_);
return v___x_2479_;
}
else
{
if (lean_obj_tag(v_evalFallback_x3f_2471_) == 1)
{
lean_object* v_val_2480_; lean_object* v___x_2481_; 
lean_dec_ref_known(v___x_2473_, 1);
v_val_2480_ = lean_ctor_get(v_evalFallback_x3f_2471_, 0);
lean_inc(v_val_2480_);
lean_dec_ref_known(v_evalFallback_x3f_2471_, 1);
v___x_2481_ = lean_apply_2(v_val_2480_, v_ctx_2469_, v_s_2470_);
return v___x_2481_;
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; 
lean_dec(v_evalFallback_x3f_2471_);
lean_dec_ref(v_ctx_2469_);
v_a_2482_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2483_ = lean_io_error_to_string(v_a_2482_);
v___x_2484_ = lean_box(0);
v___x_2485_ = 1;
v___x_2486_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2470_, v___x_2483_, v___x_2484_, v___x_2485_);
return v___x_2486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed(lean_object* v_categories_2487_, lean_object* v_declName_2488_, lean_object* v___x_2489_, lean_object* v_ctx_2490_, lean_object* v_s_2491_, lean_object* v_evalFallback_x3f_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_Parser_evalParserConstUnsafe___lam__1(v_categories_2487_, v_declName_2488_, v___x_2489_, v_ctx_2490_, v_s_2491_, v_evalFallback_x3f_2492_);
lean_dec_ref(v___x_2489_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_evalParserConstUnsafe(lean_object* v_declName_2495_, lean_object* v_evalFallback_x3f_2496_, lean_object* v_ctx_2497_, lean_object* v_s_2498_){
_start:
{
lean_object* v_toParserModuleContext_2499_; lean_object* v_env_2500_; lean_object* v_options_2501_; lean_object* v___x_2502_; lean_object* v_ext_2503_; lean_object* v_toEnvExtension_2504_; lean_object* v_asyncMode_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; lean_object* v_categories_2509_; lean_object* v___x_2510_; lean_object* v___f_2511_; lean_object* v___x_2512_; 
v_toParserModuleContext_2499_ = lean_ctor_get(v_ctx_2497_, 1);
v_env_2500_ = lean_ctor_get(v_toParserModuleContext_2499_, 0);
v_options_2501_ = lean_ctor_get(v_toParserModuleContext_2499_, 1);
v___x_2502_ = l_Lean_Parser_parserExtension;
v_ext_2503_ = lean_ctor_get(v___x_2502_, 1);
v_toEnvExtension_2504_ = lean_ctor_get(v_ext_2503_, 0);
v_asyncMode_2505_ = lean_ctor_get(v_toEnvExtension_2504_, 2);
v___x_2506_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2507_ = 0;
lean_inc_ref_n(v_env_2500_, 2);
v___x_2508_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2506_, v___x_2502_, v_env_2500_, v_asyncMode_2505_, v___x_2507_);
v_categories_2509_ = lean_ctor_get(v___x_2508_, 2);
lean_inc_ref(v_categories_2509_);
lean_dec(v___x_2508_);
lean_inc_ref(v_options_2501_);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v_env_2500_);
lean_ctor_set(v___x_2510_, 1, v_options_2501_);
v___f_2511_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe___lam__1___boxed), 7, 6);
lean_closure_set(v___f_2511_, 0, v_categories_2509_);
lean_closure_set(v___f_2511_, 1, v_declName_2495_);
lean_closure_set(v___f_2511_, 2, v___x_2510_);
lean_closure_set(v___f_2511_, 3, v_ctx_2497_);
lean_closure_set(v___f_2511_, 4, v_s_2498_);
lean_closure_set(v___f_2511_, 5, v_evalFallback_x3f_2496_);
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
lean_object* v___x_2798_; 
lean_dec(v_catName_2767_);
v___x_2798_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__5));
v___y_2775_ = v___x_2798_;
goto v___jp_2774_;
}
v___jp_2774_:
{
lean_object* v_toParserModuleContext_2776_; lean_object* v_env_2777_; lean_object* v___x_2778_; lean_object* v_ext_2779_; lean_object* v_toEnvExtension_2780_; lean_object* v_asyncMode_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v_categories_2784_; lean_object* v___x_2785_; 
v_toParserModuleContext_2776_ = lean_ctor_get(v_ctx_2768_, 1);
v_env_2777_ = lean_ctor_get(v_toParserModuleContext_2776_, 0);
v___x_2778_ = l_Lean_Parser_parserExtension;
v_ext_2779_ = lean_ctor_get(v___x_2778_, 1);
v_toEnvExtension_2780_ = lean_ctor_get(v_ext_2779_, 0);
v_asyncMode_2781_ = lean_ctor_get(v_toEnvExtension_2780_, 2);
v___x_2782_ = 0;
lean_inc_ref(v_env_2777_);
v___x_2783_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2770_, v___x_2778_, v_env_2777_, v_asyncMode_2781_, v___x_2782_);
v_categories_2784_ = lean_ctor_get(v___x_2783_, 2);
lean_inc_ref(v_categories_2784_);
lean_dec(v___x_2783_);
v___x_2785_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Parser_addLeadingParser_spec__0___redArg(v_categories_2784_, v___y_2775_);
lean_dec_ref(v_categories_2784_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
lean_dec_ref(v_ctx_2768_);
v___x_2786_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__2));
v___x_2787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2775_, v___x_2773_);
v___x_2788_ = lean_string_append(v___x_2786_, v___x_2787_);
lean_dec_ref(v___x_2787_);
v___x_2789_ = ((lean_object*)(l_Lean_Parser_categoryParserFnImpl___closed__3));
v___x_2790_ = lean_string_append(v___x_2788_, v___x_2789_);
v___x_2791_ = lean_box(0);
v___x_2792_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2769_, v___x_2790_, v___x_2791_, v___x_2773_);
return v___x_2792_;
}
else
{
lean_object* v_val_2793_; lean_object* v_tables_2794_; uint8_t v_behavior_2795_; lean_object* v___f_2796_; lean_object* v___x_2797_; 
v_val_2793_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_val_2793_);
lean_dec_ref_known(v___x_2785_, 1);
v_tables_2794_ = lean_ctor_get(v_val_2793_, 2);
lean_inc_ref(v_tables_2794_);
v_behavior_2795_ = lean_ctor_get_uint8(v_val_2793_, sizeof(void*)*3);
lean_dec(v_val_2793_);
lean_inc(v___y_2775_);
v___f_2796_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl___lam__0), 3, 1);
lean_closure_set(v___f_2796_, 0, v___y_2775_);
v___x_2797_ = l_Lean_Parser_prattParser(v___y_2775_, v_tables_2794_, v_behavior_2795_, v___f_2796_, v_ctx_2768_, v_s_2769_);
return v___x_2797_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2801_ = l_Lean_Parser_categoryParserFnRef;
v___x_2802_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_));
v___x_2803_ = lean_box(0);
v___x_2804_ = lean_st_ref_swap(v___x_2801_, v___x_2802_);
lean_dec(v___x_2804_);
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2____boxed(lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_767730617____hygCtx___hyg_2_();
return v_res_2807_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
v___x_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
return v___x_2809_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__0);
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2810_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(lean_object* v_ext_2812_, lean_object* v_b_2813_, uint8_t v_kind_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_toCold_2818_; lean_object* v_currNamespace_2819_; lean_object* v___x_2820_; lean_object* v_env_2821_; lean_object* v_nextMacroScope_2822_; lean_object* v_ngen_2823_; lean_object* v_auxDeclNGen_2824_; lean_object* v_traceState_2825_; lean_object* v_recordedDeps_2826_; lean_object* v_messages_2827_; lean_object* v_infoState_2828_; lean_object* v_snapshotTasks_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2841_; 
v_toCold_2818_ = lean_ctor_get(v___y_2815_, 0);
v_currNamespace_2819_ = lean_ctor_get(v_toCold_2818_, 4);
v___x_2820_ = lean_st_ref_take(v___y_2816_);
v_env_2821_ = lean_ctor_get(v___x_2820_, 0);
v_nextMacroScope_2822_ = lean_ctor_get(v___x_2820_, 1);
v_ngen_2823_ = lean_ctor_get(v___x_2820_, 2);
v_auxDeclNGen_2824_ = lean_ctor_get(v___x_2820_, 3);
v_traceState_2825_ = lean_ctor_get(v___x_2820_, 4);
v_recordedDeps_2826_ = lean_ctor_get(v___x_2820_, 6);
v_messages_2827_ = lean_ctor_get(v___x_2820_, 7);
v_infoState_2828_ = lean_ctor_get(v___x_2820_, 8);
v_snapshotTasks_2829_ = lean_ctor_get(v___x_2820_, 9);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v___x_2820_, 5);
lean_dec(v_unused_2842_);
v___x_2831_ = v___x_2820_;
v_isShared_2832_ = v_isSharedCheck_2841_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_snapshotTasks_2829_);
lean_inc(v_infoState_2828_);
lean_inc(v_messages_2827_);
lean_inc(v_recordedDeps_2826_);
lean_inc(v_traceState_2825_);
lean_inc(v_auxDeclNGen_2824_);
lean_inc(v_ngen_2823_);
lean_inc(v_nextMacroScope_2822_);
lean_inc(v_env_2821_);
lean_dec(v___x_2820_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2841_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
v___x_2833_ = lean_box(0);
lean_inc(v_currNamespace_2819_);
v___x_2834_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2821_, v_ext_2812_, v_b_2813_, v_kind_2814_, v_currNamespace_2819_);
v___x_2835_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 5, v___x_2835_);
lean_ctor_set(v___x_2831_, 0, v___x_2834_);
v___x_2837_ = v___x_2831_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_nextMacroScope_2822_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_ngen_2823_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_auxDeclNGen_2824_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_traceState_2825_);
lean_ctor_set(v_reuseFailAlloc_2840_, 5, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2840_, 6, v_recordedDeps_2826_);
lean_ctor_set(v_reuseFailAlloc_2840_, 7, v_messages_2827_);
lean_ctor_set(v_reuseFailAlloc_2840_, 8, v_infoState_2828_);
lean_ctor_set(v_reuseFailAlloc_2840_, 9, v_snapshotTasks_2829_);
v___x_2837_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = lean_st_ref_put(v___y_2816_, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2833_);
return v___x_2839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___boxed(lean_object* v_ext_2843_, lean_object* v_b_2844_, lean_object* v_kind_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
uint8_t v_kind_boxed_2849_; lean_object* v_res_2850_; 
v_kind_boxed_2849_ = lean_unbox(v_kind_2845_);
v_res_2850_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2843_, v_b_2844_, v_kind_boxed_2849_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(lean_object* v_00_u03b1_2851_, lean_object* v_00_u03b2_2852_, lean_object* v_00_u03c3_2853_, lean_object* v_ext_2854_, lean_object* v_b_2855_, uint8_t v_kind_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v_ext_2854_, v_b_2855_, v_kind_2856_, v___y_2857_, v___y_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___boxed(lean_object* v_00_u03b1_2861_, lean_object* v_00_u03b2_2862_, lean_object* v_00_u03c3_2863_, lean_object* v_ext_2864_, lean_object* v_b_2865_, lean_object* v_kind_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
uint8_t v_kind_boxed_2870_; lean_object* v_res_2871_; 
v_kind_boxed_2870_ = lean_unbox(v_kind_2866_);
v_res_2871_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1(v_00_u03b1_2861_, v_00_u03b2_2862_, v_00_u03c3_2863_, v_ext_2864_, v_b_2865_, v_kind_boxed_2870_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(lean_object* v_x_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
if (lean_obj_tag(v_x_2872_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v_a_2876_ = lean_ctor_get(v_x_2872_, 0);
lean_inc(v_a_2876_);
lean_dec_ref_known(v_x_2872_, 1);
v___x_2877_ = l_Lean_stringToMessageData(v_a_2876_);
v___x_2878_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_2877_, v___y_2873_, v___y_2874_);
return v___x_2878_;
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
v_a_2879_ = lean_ctor_get(v_x_2872_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v_x_2872_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v_x_2872_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v_x_2872_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
lean_ctor_set_tag(v___x_2881_, 0);
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg___boxed(lean_object* v_x_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v_x_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_addToken(lean_object* v_tk_2892_, uint8_t v_kind_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v_env_2899_; lean_object* v___x_2900_; lean_object* v_ext_2901_; lean_object* v_toEnvExtension_2902_; lean_object* v_asyncMode_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; lean_object* v_tokens_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2897_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2898_ = lean_st_ref_get(v_a_2895_);
v_env_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc_ref(v_env_2899_);
lean_dec(v___x_2898_);
v___x_2900_ = l_Lean_Parser_parserExtension;
v_ext_2901_ = lean_ctor_get(v___x_2900_, 1);
v_toEnvExtension_2902_ = lean_ctor_get(v_ext_2901_, 0);
v_asyncMode_2903_ = lean_ctor_get(v_toEnvExtension_2902_, 2);
v___x_2904_ = 0;
v___x_2905_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2897_, v___x_2900_, v_env_2899_, v_asyncMode_2903_, v___x_2904_);
v_tokens_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc_ref(v_tokens_2906_);
lean_dec(v___x_2905_);
lean_inc_ref(v_tk_2892_);
v___x_2907_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addTokenConfig(v_tokens_2906_, v_tk_2892_);
v___x_2908_ = l_Lean_ofExcept___at___00Lean_Parser_addToken_spec__0___redArg(v___x_2907_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_dec_ref_known(v___x_2908_, 1);
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_tk_2892_);
v___x_2910_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_2900_, v___x_2909_, v_kind_2893_, v_a_2894_, v_a_2895_);
return v___x_2910_;
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec_ref(v_tk_2892_);
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
lean_object* v___x_2947_; lean_object* v_ext_2948_; lean_object* v_toEnvExtension_2949_; lean_object* v_asyncMode_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; lean_object* v___x_2953_; lean_object* v_kinds_2954_; uint8_t v___x_2955_; 
v___x_2947_ = l_Lean_Parser_parserExtension;
v_ext_2948_ = lean_ctor_get(v___x_2947_, 1);
v_toEnvExtension_2949_ = lean_ctor_get(v_ext_2948_, 0);
v_asyncMode_2950_ = lean_ctor_get(v_toEnvExtension_2949_, 2);
v___x_2951_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2952_ = 0;
lean_inc_ref(v_env_2945_);
v___x_2953_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2951_, v___x_2947_, v_env_2945_, v_asyncMode_2950_, v___x_2952_);
v_kinds_2954_ = lean_ctor_get(v___x_2953_, 1);
lean_inc_ref(v_kinds_2954_);
lean_dec(v___x_2953_);
v___x_2955_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addParserCategoryCore_spec__0___redArg(v_kinds_2954_, v_k_2946_);
lean_dec_ref(v_kinds_2954_);
if (v___x_2955_ == 0)
{
uint8_t v___x_2956_; 
v___x_2956_ = lean_uint8_once(&l_Lean_Parser_isValidSyntaxNodeKind___closed__0, &l_Lean_Parser_isValidSyntaxNodeKind___closed__0_once, _init_l_Lean_Parser_isValidSyntaxNodeKind___closed__0);
if (v___x_2956_ == 0)
{
lean_dec(v_k_2946_);
lean_dec_ref(v_env_2945_);
return v___x_2952_;
}
else
{
uint8_t v___x_2957_; 
v___x_2957_ = l_Lean_Environment_contains(v_env_2945_, v_k_2946_, v___x_2956_);
return v___x_2957_;
}
}
else
{
lean_dec(v_k_2946_);
lean_dec_ref(v_env_2945_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_2985_, lean_object* v_as_2986_, size_t v_i_2987_, size_t v_stop_2988_, lean_object* v_b_2989_){
_start:
{
lean_object* v___y_2991_; uint8_t v___x_2995_; 
v___x_2995_ = lean_usize_dec_eq(v_i_2987_, v_stop_2988_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
v___x_2996_ = lean_array_uget_borrowed(v_as_2986_, v_i_2987_);
switch(lean_obj_tag(v___x_2996_))
{
case 0:
{
lean_object* v_key_2997_; lean_object* v_val_2998_; lean_object* v___x_2999_; 
v_key_2997_ = lean_ctor_get(v___x_2996_, 0);
v_val_2998_ = lean_ctor_get(v___x_2996_, 1);
lean_inc(v_f_2985_);
lean_inc(v_val_2998_);
lean_inc(v_key_2997_);
v___x_2999_ = lean_apply_3(v_f_2985_, v_b_2989_, v_key_2997_, v_val_2998_);
v___y_2991_ = v___x_2999_;
goto v___jp_2990_;
}
case 1:
{
lean_object* v_node_3000_; lean_object* v___x_3001_; 
v_node_3000_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_f_2985_);
v___x_3001_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_2985_, v_node_3000_, v_b_2989_);
v___y_2991_ = v___x_3001_;
goto v___jp_2990_;
}
default: 
{
v___y_2991_ = v_b_2989_;
goto v___jp_2990_;
}
}
}
else
{
lean_dec(v_f_2985_);
return v_b_2989_;
}
v___jp_2990_:
{
size_t v___x_2992_; size_t v___x_2993_; 
v___x_2992_ = ((size_t)1ULL);
v___x_2993_ = lean_usize_add(v_i_2987_, v___x_2992_);
v_i_2987_ = v___x_2993_;
v_b_2989_ = v___y_2991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3002_, lean_object* v_x_3003_, lean_object* v_x_3004_){
_start:
{
if (lean_obj_tag(v_x_3003_) == 0)
{
lean_object* v_es_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v_es_3005_ = lean_ctor_get(v_x_3003_, 0);
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = lean_array_get_size(v_es_3005_);
v___x_3008_ = lean_nat_dec_lt(v___x_3006_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_dec(v_f_3002_);
return v_x_3004_;
}
else
{
size_t v___x_3009_; size_t v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = ((size_t)0ULL);
v___x_3010_ = lean_usize_of_nat(v___x_3007_);
v___x_3011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3002_, v_es_3005_, v___x_3009_, v___x_3010_, v_x_3004_);
return v___x_3011_;
}
}
else
{
lean_object* v_ks_3012_; lean_object* v_vs_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_ks_3012_ = lean_ctor_get(v_x_3003_, 0);
v_vs_3013_ = lean_ctor_get(v_x_3003_, 1);
v___x_3014_ = lean_unsigned_to_nat(0u);
v___x_3015_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3002_, v_ks_3012_, v_vs_3013_, v___x_3014_, v_x_3004_);
return v___x_3015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3016_, lean_object* v_x_3017_, lean_object* v_x_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3016_, v_x_3017_, v_x_3018_);
lean_dec_ref(v_x_3017_);
return v_res_3019_;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0(lean_object* v_f_3028_, lean_object* v_x1_3029_, lean_object* v_x2_3030_, lean_object* v_x3_3031_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = lean_apply_3(v_f_3028_, v_x1_3029_, v_x2_3030_, v_x3_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(lean_object* v_map_3033_, lean_object* v_f_3034_, lean_object* v_init_3035_){
_start:
{
lean_object* v___f_3036_; lean_object* v___x_3037_; 
v___f_3036_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3036_, 0, v_f_3034_);
v___x_3037_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v___f_3036_, v_map_3033_, v_init_3035_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg___boxed(lean_object* v_map_3038_, lean_object* v_f_3039_, lean_object* v_init_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3038_, v_f_3039_, v_init_3040_);
lean_dec_ref(v_map_3038_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getSyntaxNodeKinds(lean_object* v_env_3043_){
_start:
{
lean_object* v___x_3044_; lean_object* v_ext_3045_; lean_object* v_toEnvExtension_3046_; lean_object* v_asyncMode_3047_; lean_object* v___x_3048_; uint8_t v___x_3049_; lean_object* v___x_3050_; lean_object* v_kinds_3051_; lean_object* v___f_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3044_ = l_Lean_Parser_parserExtension;
v_ext_3045_ = lean_ctor_get(v___x_3044_, 1);
v_toEnvExtension_3046_ = lean_ctor_get(v_ext_3045_, 0);
v_asyncMode_3047_ = lean_ctor_get(v_toEnvExtension_3046_, 2);
v___x_3048_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3049_ = 0;
v___x_3050_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3048_, v___x_3044_, v_env_3043_, v_asyncMode_3047_, v___x_3049_);
v_kinds_3051_ = lean_ctor_get(v___x_3050_, 1);
lean_inc_ref(v_kinds_3051_);
lean_dec(v___x_3050_);
v___f_3052_ = ((lean_object*)(l_Lean_Parser_getSyntaxNodeKinds___closed__0));
v___x_3053_ = lean_box(0);
v___x_3054_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_kinds_3051_, v___f_3052_, v___x_3053_);
lean_dec_ref(v_kinds_3051_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(lean_object* v_00_u03c3_3055_, lean_object* v_00_u03b2_3056_, lean_object* v_map_3057_, lean_object* v_f_3058_, lean_object* v_init_3059_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___redArg(v_map_3057_, v_f_3058_, v_init_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0___boxed(lean_object* v_00_u03c3_3061_, lean_object* v_00_u03b2_3062_, lean_object* v_map_3063_, lean_object* v_f_3064_, lean_object* v_init_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0(v_00_u03c3_3061_, v_00_u03b2_3062_, v_map_3063_, v_f_3064_, v_init_3065_);
lean_dec_ref(v_map_3063_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(lean_object* v_map_3067_, lean_object* v_f_3068_, lean_object* v_init_3069_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3068_, v_map_3067_, v_init_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg___boxed(lean_object* v_map_3071_, lean_object* v_f_3072_, lean_object* v_init_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___redArg(v_map_3071_, v_f_3072_, v_init_3073_);
lean_dec_ref(v_map_3071_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(lean_object* v_00_u03c3_3075_, lean_object* v_00_u03b2_3076_, lean_object* v_map_3077_, lean_object* v_f_3078_, lean_object* v_init_3079_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3078_, v_map_3077_, v_init_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3081_, lean_object* v_00_u03b2_3082_, lean_object* v_map_3083_, lean_object* v_f_3084_, lean_object* v_init_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0(v_00_u03c3_3081_, v_00_u03b2_3082_, v_map_3083_, v_f_3084_, v_init_3085_);
lean_dec_ref(v_map_3083_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3087_, lean_object* v_00_u03b1_3088_, lean_object* v_00_u03b2_3089_, lean_object* v_f_3090_, lean_object* v_x_3091_, lean_object* v_x_3092_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___redArg(v_f_3090_, v_x_3091_, v_x_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3094_, lean_object* v_00_u03b1_3095_, lean_object* v_00_u03b2_3096_, lean_object* v_f_3097_, lean_object* v_x_3098_, lean_object* v_x_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1(v_00_u03c3_3094_, v_00_u03b1_3095_, v_00_u03b2_3096_, v_f_3097_, v_x_3098_, v_x_3099_);
lean_dec_ref(v_x_3098_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3101_, lean_object* v_00_u03b2_3102_, lean_object* v_00_u03c3_3103_, lean_object* v_f_3104_, lean_object* v_as_3105_, size_t v_i_3106_, size_t v_stop_3107_, lean_object* v_b_3108_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3104_, v_as_3105_, v_i_3106_, v_stop_3107_, v_b_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3110_, lean_object* v_00_u03b2_3111_, lean_object* v_00_u03c3_3112_, lean_object* v_f_3113_, lean_object* v_as_3114_, lean_object* v_i_3115_, lean_object* v_stop_3116_, lean_object* v_b_3117_){
_start:
{
size_t v_i_boxed_3118_; size_t v_stop_boxed_3119_; lean_object* v_res_3120_; 
v_i_boxed_3118_ = lean_unbox_usize(v_i_3115_);
lean_dec(v_i_3115_);
v_stop_boxed_3119_ = lean_unbox_usize(v_stop_3116_);
lean_dec(v_stop_3116_);
v_res_3120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3110_, v_00_u03b2_3111_, v_00_u03c3_3112_, v_f_3113_, v_as_3114_, v_i_boxed_3118_, v_stop_boxed_3119_, v_b_3117_);
lean_dec_ref(v_as_3114_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3121_, lean_object* v_00_u03b1_3122_, lean_object* v_00_u03b2_3123_, lean_object* v_f_3124_, lean_object* v_keys_3125_, lean_object* v_vals_3126_, lean_object* v_heq_3127_, lean_object* v_i_3128_, lean_object* v_acc_3129_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3124_, v_keys_3125_, v_vals_3126_, v_i_3128_, v_acc_3129_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3131_, lean_object* v_00_u03b1_3132_, lean_object* v_00_u03b2_3133_, lean_object* v_f_3134_, lean_object* v_keys_3135_, lean_object* v_vals_3136_, lean_object* v_heq_3137_, lean_object* v_i_3138_, lean_object* v_acc_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Parser_getSyntaxNodeKinds_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3131_, v_00_u03b1_3132_, v_00_u03b2_3133_, v_f_3134_, v_keys_3135_, v_vals_3136_, v_heq_3137_, v_i_3138_, v_acc_3139_);
lean_dec_ref(v_vals_3136_);
lean_dec_ref(v_keys_3135_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getTokenTable(lean_object* v_env_3141_){
_start:
{
lean_object* v___x_3142_; lean_object* v_ext_3143_; lean_object* v_toEnvExtension_3144_; lean_object* v_asyncMode_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; lean_object* v___x_3148_; lean_object* v_tokens_3149_; 
v___x_3142_ = l_Lean_Parser_parserExtension;
v_ext_3143_ = lean_ctor_get(v___x_3142_, 1);
v_toEnvExtension_3144_ = lean_ctor_get(v_ext_3143_, 0);
v_asyncMode_3145_ = lean_ctor_get(v_toEnvExtension_3144_, 2);
v___x_3146_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3147_ = 0;
v___x_3148_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3146_, v___x_3142_, v_env_3141_, v_asyncMode_3145_, v___x_3147_);
v_tokens_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc_ref(v_tokens_3149_);
lean_dec(v___x_3148_);
return v_tokens_3149_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__8));
v___x_3175_ = l_Lean_mkAtom(v___x_3174_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3176_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__10, &l_Lean_Parser_mkInputContext___auto__1___closed__10_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__10);
v___x_3177_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3178_ = lean_array_push(v___x_3177_, v___x_3176_);
return v___x_3178_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3190_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3191_ = lean_array_push(v___x_3190_, v___x_3189_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3192_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__15, &l_Lean_Parser_mkInputContext___auto__1___closed__15_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__15);
v___x_3193_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__13));
v___x_3194_ = lean_box(2);
v___x_3195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
lean_ctor_set(v___x_3195_, 1, v___x_3193_);
lean_ctor_set(v___x_3195_, 2, v___x_3192_);
return v___x_3195_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3196_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__16, &l_Lean_Parser_mkInputContext___auto__1___closed__16_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__16);
v___x_3197_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__11, &l_Lean_Parser_mkInputContext___auto__1___closed__11_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__11);
v___x_3198_ = lean_array_push(v___x_3197_, v___x_3196_);
return v___x_3198_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3199_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3200_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__17, &l_Lean_Parser_mkInputContext___auto__1___closed__17_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__17);
v___x_3201_ = lean_array_push(v___x_3200_, v___x_3199_);
return v___x_3201_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3202_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3203_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__18, &l_Lean_Parser_mkInputContext___auto__1___closed__18_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__18);
v___x_3204_ = lean_array_push(v___x_3203_, v___x_3202_);
return v___x_3204_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3206_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__19, &l_Lean_Parser_mkInputContext___auto__1___closed__19_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__19);
v___x_3207_ = lean_array_push(v___x_3206_, v___x_3205_);
return v___x_3207_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__21(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3208_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__14));
v___x_3209_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__20, &l_Lean_Parser_mkInputContext___auto__1___closed__20_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__20);
v___x_3210_ = lean_array_push(v___x_3209_, v___x_3208_);
return v___x_3210_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__22(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3211_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__21, &l_Lean_Parser_mkInputContext___auto__1___closed__21_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__21);
v___x_3212_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__9));
v___x_3213_ = lean_box(2);
v___x_3214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
lean_ctor_set(v___x_3214_, 1, v___x_3212_);
lean_ctor_set(v___x_3214_, 2, v___x_3211_);
return v___x_3214_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__23(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3215_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__22, &l_Lean_Parser_mkInputContext___auto__1___closed__22_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__22);
v___x_3216_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3217_ = lean_array_push(v___x_3216_, v___x_3215_);
return v___x_3217_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__24(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3218_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__23, &l_Lean_Parser_mkInputContext___auto__1___closed__23_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__23);
v___x_3219_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3220_ = lean_box(2);
v___x_3221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_ctor_set(v___x_3221_, 1, v___x_3219_);
lean_ctor_set(v___x_3221_, 2, v___x_3218_);
return v___x_3221_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3222_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__24, &l_Lean_Parser_mkInputContext___auto__1___closed__24_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__24);
v___x_3223_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3224_ = lean_array_push(v___x_3223_, v___x_3222_);
return v___x_3224_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3225_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__25, &l_Lean_Parser_mkInputContext___auto__1___closed__25_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__25);
v___x_3226_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3227_ = lean_box(2);
v___x_3228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set(v___x_3228_, 1, v___x_3226_);
lean_ctor_set(v___x_3228_, 2, v___x_3225_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__26, &l_Lean_Parser_mkInputContext___auto__1___closed__26_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__26);
v___x_3230_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3231_ = lean_array_push(v___x_3230_, v___x_3229_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3232_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__27, &l_Lean_Parser_mkInputContext___auto__1___closed__27_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__27);
v___x_3233_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3234_ = lean_box(2);
v___x_3235_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3234_);
lean_ctor_set(v___x_3235_, 1, v___x_3233_);
lean_ctor_set(v___x_3235_, 2, v___x_3232_);
return v___x_3235_;
}
}
static lean_object* _init_l_Lean_Parser_mkInputContext___auto__1(void){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = lean_obj_once(&l_Lean_Parser_mkInputContext___auto__1___closed__28, &l_Lean_Parser_mkInputContext___auto__1___closed__28_once, _init_l_Lean_Parser_mkInputContext___auto__1___closed__28);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object* v_input_3237_, lean_object* v_fileName_3238_, uint8_t v_normalizeLineEndings_3239_, lean_object* v_endPos_3240_){
_start:
{
lean_object* v_fst_3242_; lean_object* v_snd_3243_; lean_object* v_text_3249_; 
v_text_3249_ = l_Lean_FileMap_ofString(v_input_3237_);
if (v_normalizeLineEndings_3239_ == 0)
{
v_fst_3242_ = v_text_3249_;
v_snd_3243_ = v_endPos_3240_;
goto v___jp_3241_;
}
else
{
lean_object* v_source_3250_; lean_object* v_endPos_x27_3251_; lean_object* v___x_3252_; lean_object* v_text_3253_; lean_object* v___x_3254_; 
v_source_3250_ = lean_ctor_get(v_text_3249_, 0);
lean_inc_ref(v_source_3250_);
v_endPos_x27_3251_ = l_Lean_FileMap_toPosition(v_text_3249_, v_endPos_3240_);
lean_dec(v_endPos_3240_);
v___x_3252_ = l_String_crlfToLf(v_source_3250_);
lean_dec_ref(v_source_3250_);
v_text_3253_ = l_Lean_FileMap_ofString(v___x_3252_);
v___x_3254_ = l_Lean_FileMap_ofPosition(v_text_3253_, v_endPos_x27_3251_);
v_fst_3242_ = v_text_3253_;
v_snd_3243_ = v___x_3254_;
goto v___jp_3241_;
}
v___jp_3241_:
{
lean_object* v_source_3244_; lean_object* v___x_3245_; uint8_t v___x_3246_; 
v_source_3244_ = lean_ctor_get(v_fst_3242_, 0);
lean_inc_ref(v_source_3244_);
v___x_3245_ = lean_string_utf8_byte_size(v_source_3244_);
v___x_3246_ = lean_nat_dec_le(v_snd_3243_, v___x_3245_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; 
lean_dec(v_snd_3243_);
v___x_3247_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3247_, 0, v_source_3244_);
lean_ctor_set(v___x_3247_, 1, v_fileName_3238_);
lean_ctor_set(v___x_3247_, 2, v_fst_3242_);
lean_ctor_set(v___x_3247_, 3, v___x_3245_);
return v___x_3247_;
}
else
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3248_, 0, v_source_3244_);
lean_ctor_set(v___x_3248_, 1, v_fileName_3238_);
lean_ctor_set(v___x_3248_, 2, v_fst_3242_);
lean_ctor_set(v___x_3248_, 3, v_snd_3243_);
return v___x_3248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___redArg___boxed(lean_object* v_input_3255_, lean_object* v_fileName_3256_, lean_object* v_normalizeLineEndings_3257_, lean_object* v_endPos_3258_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3259_; lean_object* v_res_3260_; 
v_normalizeLineEndings_boxed_3259_ = lean_unbox(v_normalizeLineEndings_3257_);
v_res_3260_ = l_Lean_Parser_mkInputContext___redArg(v_input_3255_, v_fileName_3256_, v_normalizeLineEndings_boxed_3259_, v_endPos_3258_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext(lean_object* v_input_3261_, lean_object* v_fileName_3262_, uint8_t v_normalizeLineEndings_3263_, lean_object* v_endPos_3264_, lean_object* v_endPos__valid_3265_){
_start:
{
lean_object* v___x_3266_; 
v___x_3266_ = l_Lean_Parser_mkInputContext___redArg(v_input_3261_, v_fileName_3262_, v_normalizeLineEndings_3263_, v_endPos_3264_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkInputContext___boxed(lean_object* v_input_3267_, lean_object* v_fileName_3268_, lean_object* v_normalizeLineEndings_3269_, lean_object* v_endPos_3270_, lean_object* v_endPos__valid_3271_){
_start:
{
uint8_t v_normalizeLineEndings_boxed_3272_; lean_object* v_res_3273_; 
v_normalizeLineEndings_boxed_3272_ = lean_unbox(v_normalizeLineEndings_3269_);
v_res_3273_ = l_Lean_Parser_mkInputContext(v_input_3267_, v_fileName_3268_, v_normalizeLineEndings_boxed_3272_, v_endPos_3270_, v_endPos__valid_3271_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState(lean_object* v_input_3276_){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3277_ = l_Lean_Parser_SyntaxStack_empty;
v___x_3278_ = lean_unsigned_to_nat(0u);
v___x_3279_ = l_Lean_Parser_initCacheForInput(v_input_3276_);
v___x_3280_ = lean_box(0);
v___x_3281_ = ((lean_object*)(l_Lean_Parser_mkParserState___closed__0));
v___x_3282_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3277_);
lean_ctor_set(v___x_3282_, 1, v___x_3278_);
lean_ctor_set(v___x_3282_, 2, v___x_3278_);
lean_ctor_set(v___x_3282_, 3, v___x_3279_);
lean_ctor_set(v___x_3282_, 4, v___x_3280_);
lean_ctor_set(v___x_3282_, 5, v___x_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserState___boxed(lean_object* v_input_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_Parser_mkParserState(v_input_3283_);
lean_dec_ref(v_input_3283_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_runParserCategory(lean_object* v_env_3287_, lean_object* v_catName_3288_, lean_object* v_input_3289_, lean_object* v_fileName_3290_){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v_p_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v_ictx_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v_s_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3291_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__0));
v___x_3292_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFnImpl), 3, 1);
lean_closure_set(v___x_3292_, 0, v_catName_3288_);
v_p_3293_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v_p_3293_, 0, v___x_3291_);
lean_closure_set(v_p_3293_, 1, v___x_3292_);
v___x_3294_ = 1;
v___x_3295_ = lean_string_utf8_byte_size(v_input_3289_);
lean_inc_ref(v_input_3289_);
v_ictx_3296_ = l_Lean_Parser_mkInputContext___redArg(v_input_3289_, v_fileName_3290_, v___x_3294_, v___x_3295_);
v___x_3297_ = l_Lean_Options_empty;
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_box(0);
lean_inc_ref(v_env_3287_);
v___x_3300_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3300_, 0, v_env_3287_);
lean_ctor_set(v___x_3300_, 1, v___x_3297_);
lean_ctor_set(v___x_3300_, 2, v___x_3298_);
lean_ctor_set(v___x_3300_, 3, v___x_3299_);
v___x_3301_ = l_Lean_Parser_getTokenTable(v_env_3287_);
v___x_3302_ = l_Lean_Parser_mkParserState(v_input_3289_);
lean_dec_ref(v_input_3289_);
lean_inc_ref(v_ictx_3296_);
v_s_3303_ = l_Lean_Parser_ParserFn_run(v_p_3293_, v_ictx_3296_, v___x_3300_, v___x_3301_, v___x_3302_);
lean_inc_ref(v_s_3303_);
v___x_3304_ = l_Lean_Parser_ParserState_allErrors(v_s_3303_);
v___x_3305_ = lean_array_get_size(v___x_3304_);
lean_dec_ref(v___x_3304_);
v___x_3306_ = lean_unsigned_to_nat(0u);
v___x_3307_ = lean_nat_dec_eq(v___x_3305_, v___x_3306_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3296_, v_s_3303_);
v___x_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
return v___x_3309_;
}
else
{
lean_object* v_stxStack_3310_; lean_object* v_pos_3311_; uint8_t v___x_3312_; 
v_stxStack_3310_ = lean_ctor_get(v_s_3303_, 0);
v_pos_3311_ = lean_ctor_get(v_s_3303_, 2);
v___x_3312_ = l_Lean_Parser_InputContext_atEnd(v_ictx_3296_, v_pos_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3313_ = ((lean_object*)(l_Lean_Parser_runParserCategory___closed__1));
v___x_3314_ = l_Lean_Parser_ParserState_mkError(v_s_3303_, v___x_3313_);
v___x_3315_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_3296_, v___x_3314_);
v___x_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
return v___x_3316_;
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_inc_ref(v_stxStack_3310_);
lean_dec_ref(v_s_3303_);
lean_dec_ref(v_ictx_3296_);
v___x_3317_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3310_);
lean_dec_ref(v_stxStack_3310_);
v___x_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
return v___x_3318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser(lean_object* v_addFnName_3319_, lean_object* v_catName_3320_, lean_object* v_declName_3321_, lean_object* v_prio_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v_val_3338_; lean_object* v___x_3339_; 
v___x_3326_ = lean_box(0);
v___x_3327_ = l_Lean_mkConst(v_addFnName_3319_, v___x_3326_);
v___x_3328_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_catName_3320_);
lean_inc_n(v_declName_3321_, 2);
v___x_3329_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3321_);
v___x_3330_ = l_Lean_mkConst(v_declName_3321_, v___x_3326_);
v___x_3331_ = l_Lean_mkRawNatLit(v_prio_3322_);
v___x_3332_ = lean_unsigned_to_nat(4u);
v___x_3333_ = lean_mk_empty_array_with_capacity(v___x_3332_);
v___x_3334_ = lean_array_push(v___x_3333_, v___x_3328_);
v___x_3335_ = lean_array_push(v___x_3334_, v___x_3329_);
v___x_3336_ = lean_array_push(v___x_3335_, v___x_3330_);
v___x_3337_ = lean_array_push(v___x_3336_, v___x_3331_);
v_val_3338_ = l_Lean_mkAppN(v___x_3327_, v___x_3337_);
lean_dec_ref(v___x_3337_);
v___x_3339_ = l_Lean_declareBuiltin(v_declName_3321_, v_val_3338_, v_a_3323_, v_a_3324_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareBuiltinParser___boxed(lean_object* v_addFnName_3340_, lean_object* v_catName_3341_, lean_object* v_declName_3342_, lean_object* v_prio_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_Parser_declareBuiltinParser(v_addFnName_3340_, v_catName_3341_, v_declName_3342_, v_prio_3343_, v_a_3344_, v_a_3345_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser(lean_object* v_catName_3353_, lean_object* v_declName_3354_, lean_object* v_prio_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = ((lean_object*)(l_Lean_Parser_declareLeadingBuiltinParser___closed__1));
v___x_3360_ = l_Lean_Parser_declareBuiltinParser(v___x_3359_, v_catName_3353_, v_declName_3354_, v_prio_3355_, v_a_3356_, v_a_3357_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareLeadingBuiltinParser___boxed(lean_object* v_catName_3361_, lean_object* v_declName_3362_, lean_object* v_prio_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3361_, v_declName_3362_, v_prio_3363_, v_a_3364_, v_a_3365_);
lean_dec(v_a_3365_);
lean_dec_ref(v_a_3364_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser(lean_object* v_catName_3373_, lean_object* v_declName_3374_, lean_object* v_prio_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = ((lean_object*)(l_Lean_Parser_declareTrailingBuiltinParser___closed__1));
v___x_3380_ = l_Lean_Parser_declareBuiltinParser(v___x_3379_, v_catName_3373_, v_declName_3374_, v_prio_3375_, v_a_3376_, v_a_3377_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_declareTrailingBuiltinParser___boxed(lean_object* v_catName_3381_, lean_object* v_declName_3382_, lean_object* v_prio_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3381_, v_declName_3382_, v_prio_3383_, v_a_3384_, v_a_3385_);
lean_dec(v_a_3385_);
lean_dec_ref(v_a_3384_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority(lean_object* v_args_3394_){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_3395_ = l_Lean_Syntax_getNumArgs(v_args_3394_);
v___x_3396_ = lean_unsigned_to_nat(0u);
v___x_3397_ = lean_nat_dec_eq(v___x_3395_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; uint8_t v___x_3399_; 
v___x_3398_ = lean_unsigned_to_nat(1u);
v___x_3399_ = lean_nat_dec_eq(v___x_3395_, v___x_3398_);
lean_dec(v___x_3395_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; 
v___x_3400_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__1));
return v___x_3400_;
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = l_Lean_Syntax_getArg(v_args_3394_, v___x_3396_);
v___x_3402_ = l_Lean_Syntax_isNatLit_x3f(v___x_3401_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3403_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__2));
v___x_3404_ = l_Lean_Syntax_formatStx(v___x_3401_, v___x_3402_, v___x_3397_);
v___x_3405_ = l_Std_Format_defWidth;
v___x_3406_ = l_Std_Format_pretty(v___x_3404_, v___x_3405_, v___x_3396_, v___x_3396_);
v___x_3407_ = lean_string_append(v___x_3403_, v___x_3406_);
lean_dec_ref(v___x_3406_);
v___x_3408_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3409_ = lean_string_append(v___x_3407_, v___x_3408_);
v___x_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
return v___x_3410_;
}
else
{
lean_object* v_val_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v___x_3401_);
v_val_3411_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3402_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_val_3411_);
lean_dec(v___x_3402_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_val_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
else
{
lean_object* v___x_3419_; 
lean_dec(v___x_3395_);
v___x_3419_ = ((lean_object*)(l_Lean_Parser_getParserPriority___closed__3));
return v___x_3419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getParserPriority___boxed(lean_object* v_args_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_Lean_Parser_getParserPriority(v_args_3420_);
lean_dec(v_args_3420_);
return v_res_3421_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__0));
v___x_3424_ = l_Lean_stringToMessageData(v___x_3423_);
return v___x_3424_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__2));
v___x_3427_ = l_Lean_stringToMessageData(v___x_3426_);
return v___x_3427_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = ((lean_object*)(l_Lean_Parser_throwUnknownParserCategory___redArg___closed__1));
v___x_3429_ = l_Lean_stringToMessageData(v___x_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(lean_object* v_name_3433_, uint8_t v_kind_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___y_3444_; 
v___x_3438_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__1);
v___x_3439_ = l_Lean_MessageData_ofName(v_name_3433_);
v___x_3440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3438_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
v___x_3441_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__3);
v___x_3442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3440_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
switch(v_kind_3434_)
{
case 0:
{
lean_object* v___x_3451_; 
v___x_3451_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__5));
v___y_3444_ = v___x_3451_;
goto v___jp_3443_;
}
case 1:
{
lean_object* v___x_3452_; 
v___x_3452_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__6));
v___y_3444_ = v___x_3452_;
goto v___jp_3443_;
}
default: 
{
lean_object* v___x_3453_; 
v___x_3453_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__7));
v___y_3444_ = v___x_3453_;
goto v___jp_3443_;
}
}
v___jp_3443_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
lean_inc_ref(v___y_3444_);
v___x_3445_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3445_, 0, v___y_3444_);
v___x_3446_ = l_Lean_MessageData_ofFormat(v___x_3445_);
v___x_3447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3442_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3447_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3449_, v___y_3435_, v___y_3436_);
return v___x_3450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___boxed(lean_object* v_name_3454_, lean_object* v_kind_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
uint8_t v_kind_boxed_3459_; lean_object* v_res_3460_; 
v_kind_boxed_3459_ = lean_unbox(v_kind_3455_);
v_res_3460_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3454_, v_kind_boxed_3459_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3461_, lean_object* v_msg_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v_toCold_3466_; lean_object* v_currRecDepth_3467_; lean_object* v_ref_3468_; uint16_t v_optionFlags_3469_; uint8_t v_suppressElabErrors_3470_; uint8_t v_isRecordingDeps_3471_; lean_object* v_ref_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_toCold_3466_ = lean_ctor_get(v___y_3463_, 0);
v_currRecDepth_3467_ = lean_ctor_get(v___y_3463_, 1);
v_ref_3468_ = lean_ctor_get(v___y_3463_, 2);
v_optionFlags_3469_ = lean_ctor_get_uint16(v___y_3463_, sizeof(void*)*3);
v_suppressElabErrors_3470_ = lean_ctor_get_uint8(v___y_3463_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3471_ = lean_ctor_get_uint8(v___y_3463_, sizeof(void*)*3 + 3);
v_ref_3472_ = l_Lean_replaceRef(v_ref_3461_, v_ref_3468_);
lean_inc(v_currRecDepth_3467_);
lean_inc_ref(v_toCold_3466_);
v___x_3473_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3473_, 0, v_toCold_3466_);
lean_ctor_set(v___x_3473_, 1, v_currRecDepth_3467_);
lean_ctor_set(v___x_3473_, 2, v_ref_3472_);
lean_ctor_set_uint16(v___x_3473_, sizeof(void*)*3, v_optionFlags_3469_);
lean_ctor_set_uint8(v___x_3473_, sizeof(void*)*3 + 2, v_suppressElabErrors_3470_);
lean_ctor_set_uint8(v___x_3473_, sizeof(void*)*3 + 3, v_isRecordingDeps_3471_);
v___x_3474_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v_msg_3462_, v___x_3473_, v___y_3464_);
lean_dec_ref_known(v___x_3473_, 3);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3475_, lean_object* v_msg_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3475_, v_msg_3476_, v___y_3477_, v___y_3478_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v_ref_3475_);
return v_res_3480_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3482_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_3483_ = l_Lean_stringToMessageData(v___x_3482_);
return v___x_3483_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_3486_ = l_Lean_stringToMessageData(v___x_3485_);
return v___x_3486_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_3489_ = l_Lean_stringToMessageData(v___x_3488_);
return v___x_3489_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_3492_ = l_Lean_stringToMessageData(v___x_3491_);
return v___x_3492_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_3495_ = l_Lean_stringToMessageData(v___x_3494_);
return v___x_3495_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_3498_ = l_Lean_stringToMessageData(v___x_3497_);
return v___x_3498_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_3501_ = l_Lean_stringToMessageData(v___x_3500_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_3502_, lean_object* v_declHint_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v_env_3508_; uint8_t v___x_3509_; 
v___x_3506_ = lean_box(0);
v___x_3507_ = lean_st_ref_get(v___y_3504_);
v_env_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc_ref(v_env_3508_);
lean_dec(v___x_3507_);
v___x_3509_ = l_Lean_Name_isAnonymous(v_declHint_3503_);
if (v___x_3509_ == 0)
{
uint8_t v_isExporting_3510_; 
v_isExporting_3510_ = lean_ctor_get_uint8(v_env_3508_, sizeof(void*)*13);
if (v_isExporting_3510_ == 0)
{
lean_object* v___x_3511_; 
lean_dec_ref(v_env_3508_);
lean_dec(v_declHint_3503_);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v_msg_3502_);
return v___x_3511_;
}
else
{
lean_object* v___x_3512_; uint8_t v___x_3513_; 
lean_inc_ref(v_env_3508_);
v___x_3512_ = l_Lean_Environment_setExporting(v_env_3508_, v___x_3509_);
lean_inc(v_declHint_3503_);
lean_inc_ref(v___x_3512_);
v___x_3513_ = l_Lean_Environment_contains(v___x_3512_, v_declHint_3503_, v_isExporting_3510_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; 
lean_dec_ref(v___x_3512_);
lean_dec_ref(v_env_3508_);
lean_dec(v_declHint_3503_);
v___x_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3514_, 0, v_msg_3502_);
return v___x_3514_;
}
else
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v_c_3520_; lean_object* v___x_3521_; 
v___x_3515_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_3516_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_3517_ = l_Lean_Options_empty;
v___x_3518_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3512_);
lean_ctor_set(v___x_3518_, 1, v___x_3515_);
lean_ctor_set(v___x_3518_, 2, v___x_3516_);
lean_ctor_set(v___x_3518_, 3, v___x_3517_);
lean_inc(v_declHint_3503_);
v___x_3519_ = l_Lean_MessageData_ofConstName(v_declHint_3503_, v___x_3509_);
v_c_3520_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3520_, 0, v___x_3518_);
lean_ctor_set(v_c_3520_, 1, v___x_3519_);
v___x_3521_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3508_, v_declHint_3503_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
lean_dec_ref(v_env_3508_);
lean_dec(v_declHint_3503_);
v___x_3522_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
lean_ctor_set(v___x_3523_, 1, v_c_3520_);
v___x_3524_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_3525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3523_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = l_Lean_MessageData_note(v___x_3525_);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v_msg_3502_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
return v___x_3528_;
}
else
{
lean_object* v_val_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3563_; 
v_val_3529_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3531_ = v___x_3521_;
v_isShared_3532_ = v_isSharedCheck_3563_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_val_3529_);
lean_dec(v___x_3521_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3563_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; lean_object* v_moduleNames_3534_; lean_object* v_mod_3535_; uint8_t v___x_3536_; 
v___x_3533_ = l_Lean_Environment_header(v_env_3508_);
lean_dec_ref(v_env_3508_);
v_moduleNames_3534_ = lean_ctor_get(v___x_3533_, 4);
lean_inc_ref(v_moduleNames_3534_);
lean_dec_ref(v___x_3533_);
v_mod_3535_ = lean_array_get(v___x_3506_, v_moduleNames_3534_, v_val_3529_);
lean_dec(v_val_3529_);
lean_dec_ref(v_moduleNames_3534_);
v___x_3536_ = l_Lean_isPrivateName(v_declHint_3503_);
lean_dec(v_declHint_3503_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3537_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_3538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
lean_ctor_set(v___x_3538_, 1, v_c_3520_);
v___x_3539_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_3540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3538_);
lean_ctor_set(v___x_3540_, 1, v___x_3539_);
v___x_3541_ = l_Lean_MessageData_ofName(v_mod_3535_);
v___x_3542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3540_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_3544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3542_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = l_Lean_MessageData_note(v___x_3544_);
v___x_3546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3546_, 0, v_msg_3502_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set_tag(v___x_3531_, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3546_);
v___x_3548_ = v___x_3531_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
else
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_3551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
lean_ctor_set(v___x_3551_, 1, v_c_3520_);
v___x_3552_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_3553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3551_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
v___x_3554_ = l_Lean_MessageData_ofName(v_mod_3535_);
v___x_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3553_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
v___x_3556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_3557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3555_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = l_Lean_MessageData_note(v___x_3557_);
v___x_3559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3559_, 0, v_msg_3502_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set_tag(v___x_3531_, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3559_);
v___x_3561_ = v___x_3531_;
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
}
}
}
}
}
else
{
lean_object* v___x_3564_; 
lean_dec_ref(v_env_3508_);
lean_dec(v_declHint_3503_);
v___x_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3564_, 0, v_msg_3502_);
return v___x_3564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_3565_, lean_object* v_declHint_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3565_, v_declHint_3566_, v___y_3567_);
lean_dec(v___y_3567_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_3570_, lean_object* v_declHint_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v___x_3575_; lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3585_; 
v___x_3575_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3570_, v_declHint_3571_, v___y_3573_);
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3585_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3585_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3580_ = l_Lean_unknownIdentifierMessageTag;
v___x_3581_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
lean_ctor_set(v___x_3581_, 1, v_a_3576_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v___x_3581_);
v___x_3583_ = v___x_3578_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_3586_, lean_object* v_declHint_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3586_, v_declHint_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3592_, lean_object* v_msg_3593_, lean_object* v_declHint_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v___x_3598_; lean_object* v_a_3599_; lean_object* v___x_3600_; 
v___x_3598_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_3593_, v_declHint_3594_, v___y_3595_, v___y_3596_);
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref(v___x_3598_);
v___x_3600_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3592_, v_a_3599_, v___y_3595_, v___y_3596_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3601_, lean_object* v_msg_3602_, lean_object* v_declHint_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3601_, v_msg_3602_, v_declHint_3603_, v___y_3604_, v___y_3605_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v_ref_3601_);
return v_res_3607_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__2));
v___x_3609_ = l_Lean_stringToMessageData(v___x_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3610_, lean_object* v_constName_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v___x_3615_; uint8_t v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3615_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3616_ = 0;
lean_inc(v_constName_3611_);
v___x_3617_ = l_Lean_MessageData_ofConstName(v_constName_3611_, v___x_3616_);
v___x_3618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3615_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg___closed__4);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3610_, v___x_3620_, v_constName_3611_, v___y_3612_, v___y_3613_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3622_, lean_object* v_constName_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3622_, v_constName_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v_ref_3622_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(lean_object* v_constName_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_ref_3632_; lean_object* v___x_3633_; 
v_ref_3632_ = lean_ctor_get(v___y_3629_, 2);
v___x_3633_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3632_, v_constName_3628_, v___y_3629_, v___y_3630_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(lean_object* v_constName_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v___x_3643_; lean_object* v_env_3644_; uint8_t v___x_3645_; lean_object* v___x_3646_; 
v___x_3643_ = lean_st_ref_get(v___y_3641_);
v_env_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc_ref(v_env_3644_);
lean_dec(v___x_3643_);
v___x_3645_ = 0;
lean_inc(v_constName_3639_);
v___x_3646_ = l_Lean_Environment_find_x3f(v_env_3644_, v_constName_3639_, v___x_3645_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3639_, v___y_3640_, v___y_3641_);
return v___x_3647_;
}
else
{
lean_object* v_val_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec(v_constName_3639_);
v_val_3648_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3646_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_val_3648_);
lean_dec(v___x_3646_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
lean_ctor_set_tag(v___x_3650_, 0);
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_val_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0___boxed(lean_object* v_constName_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_constName_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
return v_res_3660_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1(void){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__0));
v___x_3663_ = l_Lean_stringToMessageData(v___x_3662_);
return v___x_3663_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__2));
v___x_3666_ = l_Lean_stringToMessageData(v___x_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(lean_object* v_attrName_3667_, lean_object* v_catName_3668_, lean_object* v_declName_3669_, lean_object* v_stx_3670_, uint8_t v_kind_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___x_3695_; 
v___x_3695_ = l_Lean_Attribute_Builtin_getPrio(v_stx_3670_, v_a_3672_, v_a_3673_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___y_3698_; lean_object* v___y_3699_; uint8_t v___x_3727_; uint8_t v___x_3728_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___x_3695_, 1);
v___x_3727_ = 0;
v___x_3728_ = l_Lean_instBEqAttributeKind_beq(v_kind_3671_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; 
lean_dec(v_a_3696_);
lean_dec(v_declName_3669_);
lean_dec(v_catName_3668_);
v___x_3729_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_attrName_3667_, v_kind_3671_, v_a_3672_, v_a_3673_);
return v___x_3729_;
}
else
{
lean_dec(v_attrName_3667_);
v___y_3698_ = v_a_3672_;
v___y_3699_ = v_a_3673_;
goto v___jp_3697_;
}
v___jp_3697_:
{
lean_object* v___x_3700_; 
lean_inc(v_declName_3669_);
v___x_3700_ = l_Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0(v_declName_3669_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3702_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3700_, 1);
v___x_3702_ = l_Lean_ConstantInfo_type(v_a_3701_);
if (lean_obj_tag(v___x_3702_) == 4)
{
lean_object* v_declName_3703_; 
v_declName_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_declName_3703_);
lean_dec_ref_known(v___x_3702_, 2);
if (lean_obj_tag(v_declName_3703_) == 1)
{
lean_object* v_pre_3704_; 
v_pre_3704_ = lean_ctor_get(v_declName_3703_, 0);
lean_inc(v_pre_3704_);
if (lean_obj_tag(v_pre_3704_) == 1)
{
lean_object* v_pre_3705_; 
v_pre_3705_ = lean_ctor_get(v_pre_3704_, 0);
lean_inc(v_pre_3705_);
if (lean_obj_tag(v_pre_3705_) == 1)
{
lean_object* v_pre_3706_; 
v_pre_3706_ = lean_ctor_get(v_pre_3705_, 0);
if (lean_obj_tag(v_pre_3706_) == 0)
{
lean_object* v_str_3707_; lean_object* v_str_3708_; lean_object* v_str_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; 
v_str_3707_ = lean_ctor_get(v_declName_3703_, 1);
lean_inc_ref(v_str_3707_);
lean_dec_ref_known(v_declName_3703_, 2);
v_str_3708_ = lean_ctor_get(v_pre_3704_, 1);
lean_inc_ref(v_str_3708_);
lean_dec_ref_known(v_pre_3704_, 2);
v_str_3709_ = lean_ctor_get(v_pre_3705_, 1);
lean_inc_ref(v_str_3709_);
lean_dec_ref_known(v_pre_3705_, 2);
v___x_3710_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3711_ = lean_string_dec_eq(v_str_3709_, v___x_3710_);
lean_dec_ref(v_str_3709_);
if (v___x_3711_ == 0)
{
lean_dec_ref(v_str_3708_);
lean_dec_ref(v_str_3707_);
lean_dec(v_a_3696_);
lean_dec(v_catName_3668_);
v___y_3682_ = v_a_3701_;
v___y_3683_ = v___y_3698_;
v___y_3684_ = v___y_3699_;
goto v___jp_3681_;
}
else
{
lean_object* v___x_3712_; uint8_t v___x_3713_; 
v___x_3712_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3713_ = lean_string_dec_eq(v_str_3708_, v___x_3712_);
lean_dec_ref(v_str_3708_);
if (v___x_3713_ == 0)
{
lean_dec_ref(v_str_3707_);
lean_dec(v_a_3696_);
lean_dec(v_catName_3668_);
v___y_3682_ = v_a_3701_;
v___y_3683_ = v___y_3698_;
v___y_3684_ = v___y_3699_;
goto v___jp_3681_;
}
else
{
lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3714_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_3715_ = lean_string_dec_eq(v_str_3707_, v___x_3714_);
if (v___x_3715_ == 0)
{
uint8_t v___x_3716_; 
v___x_3716_ = lean_string_dec_eq(v_str_3707_, v___x_3712_);
lean_dec_ref(v_str_3707_);
if (v___x_3716_ == 0)
{
lean_dec(v_a_3696_);
lean_dec(v_catName_3668_);
v___y_3682_ = v_a_3701_;
v___y_3683_ = v___y_3698_;
v___y_3684_ = v___y_3699_;
goto v___jp_3681_;
}
else
{
lean_object* v___x_3717_; 
lean_dec(v_a_3701_);
lean_inc(v_declName_3669_);
lean_inc(v_catName_3668_);
v___x_3717_ = l_Lean_Parser_declareLeadingBuiltinParser(v_catName_3668_, v_declName_3669_, v_a_3696_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_dec_ref_known(v___x_3717_, 1);
v___y_3676_ = v___y_3698_;
v___y_3677_ = v___y_3699_;
goto v___jp_3675_;
}
else
{
lean_dec(v_declName_3669_);
lean_dec(v_catName_3668_);
return v___x_3717_;
}
}
}
else
{
lean_object* v___x_3718_; 
lean_dec_ref(v_str_3707_);
lean_dec(v_a_3701_);
lean_inc(v_declName_3669_);
lean_inc(v_catName_3668_);
v___x_3718_ = l_Lean_Parser_declareTrailingBuiltinParser(v_catName_3668_, v_declName_3669_, v_a_3696_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_dec_ref_known(v___x_3718_, 1);
v___y_3676_ = v___y_3698_;
v___y_3677_ = v___y_3699_;
goto v___jp_3675_;
}
else
{
lean_dec(v_declName_3669_);
lean_dec(v_catName_3668_);
return v___x_3718_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3705_, 2);
lean_dec_ref_known(v_pre_3704_, 2);
lean_dec_ref_known(v_declName_3703_, 2);
lean_dec(v_a_3696_);
lean_dec(v_catName_3668_);
v___y_3682_ = v_a_3701_;
v___y_3683_ = v___y_3698_;
v___y_3684_ = v___y_3699_;
goto v___jp_3681_;
}
}
else
{
lean_dec_ref_known(v_pre_3704_, 2);
lean_dec(v_pre_3705_);
lean_dec_ref_known(v_declName_3703_, 2);
lean_dec(v_a_3696_);
lean_dec(v_catName_3668_);
v___y_3682_ = v_a_3701_;
v___y_3683_ = v___y_3698_;
v___y_3684_ = v___y_3699_;
goto v___jp_3681_;
}
}
else
{
lean_dec(v_pre_3704_);
lean_dec_ref_known(v_declName_3703_, 2);
lean_dec(v_a_3696_);
lean_dec(v_catName_3668_);
v___y_3682_ = v_a_3701_;
v___y_3683_ = v___y_3698_;
v___y_3684_ = v___y_3699_;
goto v___jp_3681_;
}
}
else
{
lean_dec(v_declName_3703_);
lean_dec(v_a_3696_);
lean_dec(v_catName_3668_);
v___y_3682_ = v_a_3701_;
v___y_3683_ = v___y_3698_;
v___y_3684_ = v___y_3699_;
goto v___jp_3681_;
}
}
else
{
lean_dec_ref(v___x_3702_);
lean_dec(v_a_3696_);
lean_dec(v_catName_3668_);
v___y_3682_ = v_a_3701_;
v___y_3683_ = v___y_3698_;
v___y_3684_ = v___y_3699_;
goto v___jp_3681_;
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_dec(v_a_3696_);
lean_dec(v_declName_3669_);
lean_dec(v_catName_3668_);
v_a_3719_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3700_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3700_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec(v_declName_3669_);
lean_dec(v_catName_3668_);
lean_dec(v_attrName_3667_);
v_a_3730_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3695_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3695_);
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
v___jp_3675_:
{
lean_object* v___x_3678_; 
lean_inc(v_declName_3669_);
v___x_3678_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_3669_, v___y_3676_, v___y_3677_);
if (lean_obj_tag(v___x_3678_) == 0)
{
uint8_t v___x_3679_; lean_object* v___x_3680_; 
lean_dec_ref_known(v___x_3678_, 1);
v___x_3679_ = 1;
v___x_3680_ = l_Lean_Parser_runParserAttributeHooks(v_catName_3668_, v_declName_3669_, v___x_3679_, v___y_3676_, v___y_3677_);
return v___x_3680_;
}
else
{
lean_dec(v_declName_3669_);
lean_dec(v_catName_3668_);
return v___x_3678_;
}
}
v___jp_3681_:
{
lean_object* v___x_3685_; uint8_t v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3685_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__1);
v___x_3686_ = 0;
v___x_3687_ = l_Lean_MessageData_ofConstName(v_declName_3669_, v___x_3686_);
v___x_3688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3685_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3, &l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3_once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___closed__3);
v___x_3690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = l_Lean_ConstantInfo_type(v___y_3682_);
lean_dec_ref(v___y_3682_);
v___x_3692_ = l_Lean_indentExpr(v___x_3691_);
v___x_3693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3690_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
v___x_3694_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3693_, v___y_3683_, v___y_3684_);
return v___x_3694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add___boxed(lean_object* v_attrName_3738_, lean_object* v_catName_3739_, lean_object* v_declName_3740_, lean_object* v_stx_3741_, lean_object* v_kind_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_){
_start:
{
uint8_t v_kind_boxed_3746_; lean_object* v_res_3747_; 
v_kind_boxed_3746_ = lean_unbox(v_kind_3742_);
v_res_3747_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3738_, v_catName_3739_, v_declName_3740_, v_stx_3741_, v_kind_boxed_3746_, v_a_3743_, v_a_3744_);
lean_dec(v_a_3744_);
lean_dec_ref(v_a_3743_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(lean_object* v_00_u03b1_3748_, lean_object* v_name_3749_, uint8_t v_kind_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___redArg(v_name_3749_, v_kind_3750_, v___y_3751_, v___y_3752_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b1_3755_, lean_object* v_name_3756_, lean_object* v_kind_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
uint8_t v_kind_boxed_3761_; lean_object* v_res_3762_; 
v_kind_boxed_3761_ = lean_unbox(v_kind_3757_);
v_res_3762_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__1(v_00_u03b1_3755_, v_name_3756_, v_kind_boxed_3761_, v___y_3758_, v___y_3759_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(lean_object* v_00_u03b1_3763_, lean_object* v_constName_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v___x_3768_; 
v___x_3768_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___redArg(v_constName_3764_, v___y_3765_, v___y_3766_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3769_, lean_object* v_constName_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0(v_00_u03b1_3769_, v_constName_3770_, v___y_3771_, v___y_3772_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3775_, lean_object* v_ref_3776_, lean_object* v_constName_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___redArg(v_ref_3776_, v_constName_3777_, v___y_3778_, v___y_3779_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3782_, lean_object* v_ref_3783_, lean_object* v_constName_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1(v_00_u03b1_3782_, v_ref_3783_, v_constName_3784_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v_ref_3783_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3789_, lean_object* v_ref_3790_, lean_object* v_msg_3791_, lean_object* v_declHint_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3790_, v_msg_3791_, v_declHint_3792_, v___y_3793_, v___y_3794_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3797_, lean_object* v_ref_3798_, lean_object* v_msg_3799_, lean_object* v_declHint_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3797_, v_ref_3798_, v_msg_3799_, v_declHint_3800_, v___y_3801_, v___y_3802_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v_ref_3798_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_3805_, lean_object* v_declHint_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_3805_, v_declHint_3806_, v___y_3808_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_3811_, lean_object* v_declHint_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_3811_, v_declHint_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_3817_, lean_object* v_ref_3818_, lean_object* v_msg_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3818_, v_msg_3819_, v___y_3820_, v___y_3821_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3824_, lean_object* v_ref_3825_, lean_object* v_msg_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_3824_, v_ref_3825_, v_msg_3826_, v___y_3827_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v_ref_3825_);
return v_res_3830_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2(void){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3837_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__0));
v___x_3838_ = l_Lean_mkAtom(v___x_3837_);
return v___x_3838_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3839_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__2);
v___x_3840_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3841_ = lean_array_push(v___x_3840_, v___x_3839_);
return v___x_3841_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3850_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__7));
v___x_3851_ = l_Lean_mkAtom(v___x_3850_);
return v___x_3851_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3852_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__8);
v___x_3853_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3854_ = lean_array_push(v___x_3853_, v___x_3852_);
return v___x_3854_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10(void){
_start:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3855_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__9);
v___x_3856_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__6));
v___x_3857_ = lean_box(2);
v___x_3858_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3857_);
lean_ctor_set(v___x_3858_, 1, v___x_3856_);
lean_ctor_set(v___x_3858_, 2, v___x_3855_);
return v___x_3858_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11(void){
_start:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__10);
v___x_3860_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__3);
v___x_3861_ = lean_array_push(v___x_3860_, v___x_3859_);
return v___x_3861_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3862_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__11);
v___x_3863_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__1));
v___x_3864_ = lean_box(2);
v___x_3865_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
lean_ctor_set(v___x_3865_, 1, v___x_3863_);
lean_ctor_set(v___x_3865_, 2, v___x_3862_);
return v___x_3865_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3866_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__12);
v___x_3867_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3868_ = lean_array_push(v___x_3867_, v___x_3866_);
return v___x_3868_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14(void){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3869_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__13);
v___x_3870_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__7));
v___x_3871_ = lean_box(2);
v___x_3872_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3871_);
lean_ctor_set(v___x_3872_, 1, v___x_3870_);
lean_ctor_set(v___x_3872_, 2, v___x_3869_);
return v___x_3872_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3873_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__14);
v___x_3874_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3875_ = lean_array_push(v___x_3874_, v___x_3873_);
return v___x_3875_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3876_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__15);
v___x_3877_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__5));
v___x_3878_ = lean_box(2);
v___x_3879_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
lean_ctor_set(v___x_3879_, 1, v___x_3877_);
lean_ctor_set(v___x_3879_, 2, v___x_3876_);
return v___x_3879_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__16);
v___x_3881_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__3));
v___x_3882_ = lean_array_push(v___x_3881_, v___x_3880_);
return v___x_3882_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3883_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__17);
v___x_3884_ = ((lean_object*)(l_Lean_Parser_mkInputContext___auto__1___closed__2));
v___x_3885_ = lean_box(2);
v___x_3886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
lean_ctor_set(v___x_3886_, 1, v___x_3884_);
lean_ctor_set(v___x_3886_, 2, v___x_3883_);
return v___x_3886_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0(lean_object* v_attrName_3888_, lean_object* v_decl_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3893_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__1_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3894_ = l_Lean_MessageData_ofName(v_attrName_3888_);
v___x_3895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3893_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
v___x_3896_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__1___closed__3_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_);
v___x_3897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3895_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___x_3898_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_3897_, v___y_3890_, v___y_3891_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed(lean_object* v_attrName_3899_, lean_object* v_decl_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__0(v_attrName_3899_, v_decl_3900_, v___y_3901_, v___y_3902_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v_decl_3900_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1(lean_object* v_attrName_3905_, lean_object* v_catName_3906_, lean_object* v_declName_3907_, lean_object* v_stx_3908_, uint8_t v_kind_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l___private_Lean_Parser_Extension_0__Lean_Parser_BuiltinParserAttribute_add(v_attrName_3905_, v_catName_3906_, v_declName_3907_, v_stx_3908_, v_kind_3909_, v___y_3910_, v___y_3911_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed(lean_object* v_attrName_3914_, lean_object* v_catName_3915_, lean_object* v_declName_3916_, lean_object* v_stx_3917_, lean_object* v_kind_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
uint8_t v_kind_boxed_3922_; lean_object* v_res_3923_; 
v_kind_boxed_3922_ = lean_unbox(v_kind_3918_);
v_res_3923_ = l_Lean_Parser_registerBuiltinParserAttribute___lam__1(v_attrName_3914_, v_catName_3915_, v_declName_3916_, v_stx_3917_, v_kind_boxed_3922_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
return v_res_3923_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1(void){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__0));
v___x_3926_ = lean_mk_io_user_error(v___x_3925_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute(lean_object* v_attrName_3929_, lean_object* v_declName_3930_, uint8_t v_behavior_3931_, lean_object* v_ref_3932_){
_start:
{
if (lean_obj_tag(v_declName_3930_) == 1)
{
lean_object* v_pre_3937_; 
v_pre_3937_ = lean_ctor_get(v_declName_3930_, 0);
if (lean_obj_tag(v_pre_3937_) == 1)
{
lean_object* v_pre_3938_; 
v_pre_3938_ = lean_ctor_get(v_pre_3937_, 0);
if (lean_obj_tag(v_pre_3938_) == 1)
{
lean_object* v_pre_3939_; 
v_pre_3939_ = lean_ctor_get(v_pre_3938_, 0);
if (lean_obj_tag(v_pre_3939_) == 1)
{
lean_object* v_pre_3940_; 
v_pre_3940_ = lean_ctor_get(v_pre_3939_, 0);
if (lean_obj_tag(v_pre_3940_) == 0)
{
lean_object* v_str_3941_; lean_object* v_str_3942_; lean_object* v_str_3943_; lean_object* v_str_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; 
v_str_3941_ = lean_ctor_get(v_declName_3930_, 1);
v_str_3942_ = lean_ctor_get(v_pre_3937_, 1);
v_str_3943_ = lean_ctor_get(v_pre_3938_, 1);
v_str_3944_ = lean_ctor_get(v_pre_3939_, 1);
v___x_3945_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_3946_ = lean_string_dec_eq(v_str_3944_, v___x_3945_);
if (v___x_3946_ == 0)
{
lean_dec_ref_known(v_declName_3930_, 2);
lean_dec(v_ref_3932_);
lean_dec(v_attrName_3929_);
goto v___jp_3934_;
}
else
{
lean_object* v___x_3947_; uint8_t v___x_3948_; 
v___x_3947_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_3948_ = lean_string_dec_eq(v_str_3943_, v___x_3947_);
if (v___x_3948_ == 0)
{
lean_dec_ref_known(v_declName_3930_, 2);
lean_dec(v_ref_3932_);
lean_dec(v_attrName_3929_);
goto v___jp_3934_;
}
else
{
lean_object* v___x_3949_; uint8_t v___x_3950_; 
v___x_3949_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__2));
v___x_3950_ = lean_string_dec_eq(v_str_3942_, v___x_3949_);
if (v___x_3950_ == 0)
{
lean_dec_ref_known(v_declName_3930_, 2);
lean_dec(v_ref_3932_);
lean_dec(v_attrName_3929_);
goto v___jp_3934_;
}
else
{
lean_object* v___f_3951_; lean_object* v___x_3952_; lean_object* v_catName_3953_; lean_object* v___f_3954_; lean_object* v___x_3955_; 
lean_inc_n(v_attrName_3929_, 2);
v___f_3951_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3951_, 0, v_attrName_3929_);
v___x_3952_ = lean_box(0);
lean_inc_ref(v_str_3941_);
v_catName_3953_ = l_Lean_Name_str___override(v___x_3952_, v_str_3941_);
lean_inc(v_catName_3953_);
v___f_3954_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3954_, 0, v_attrName_3929_);
lean_closure_set(v___f_3954_, 1, v_catName_3953_);
v___x_3955_ = l___private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory(v_catName_3953_, v_declName_3930_, v_behavior_3931_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v___x_3956_; uint8_t v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
lean_dec_ref_known(v___x_3955_, 1);
v___x_3956_ = ((lean_object*)(l_Lean_Parser_registerBuiltinParserAttribute___closed__3));
v___x_3957_ = 1;
v___x_3958_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3958_, 0, v_ref_3932_);
lean_ctor_set(v___x_3958_, 1, v_attrName_3929_);
lean_ctor_set(v___x_3958_, 2, v___x_3956_);
lean_ctor_set_uint8(v___x_3958_, sizeof(void*)*3, v___x_3957_);
v___x_3959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
lean_ctor_set(v___x_3959_, 1, v___f_3954_);
lean_ctor_set(v___x_3959_, 2, v___f_3951_);
v___x_3960_ = l_Lean_registerBuiltinAttribute(v___x_3959_);
return v___x_3960_;
}
else
{
lean_dec_ref(v___f_3954_);
lean_dec_ref(v___f_3951_);
lean_dec(v_ref_3932_);
lean_dec(v_attrName_3929_);
return v___x_3955_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_declName_3930_, 2);
lean_dec(v_ref_3932_);
lean_dec(v_attrName_3929_);
goto v___jp_3934_;
}
}
else
{
lean_dec_ref_known(v_declName_3930_, 2);
lean_dec(v_ref_3932_);
lean_dec(v_attrName_3929_);
goto v___jp_3934_;
}
}
else
{
lean_dec_ref_known(v_declName_3930_, 2);
lean_dec(v_ref_3932_);
lean_dec(v_attrName_3929_);
goto v___jp_3934_;
}
}
else
{
lean_dec_ref_known(v_declName_3930_, 2);
lean_dec(v_ref_3932_);
lean_dec(v_attrName_3929_);
goto v___jp_3934_;
}
}
else
{
lean_dec(v_ref_3932_);
lean_dec(v_declName_3930_);
lean_dec(v_attrName_3929_);
goto v___jp_3934_;
}
v___jp_3934_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___closed__1, &l_Lean_Parser_registerBuiltinParserAttribute___closed__1_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___closed__1);
v___x_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3935_);
return v___x_3936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinParserAttribute___boxed(lean_object* v_attrName_3961_, lean_object* v_declName_3962_, lean_object* v_behavior_3963_, lean_object* v_ref_3964_, lean_object* v_a_3965_){
_start:
{
uint8_t v_behavior_boxed_3966_; lean_object* v_res_3967_; 
v_behavior_boxed_3966_ = lean_unbox(v_behavior_3963_);
v_res_3967_ = l_Lean_Parser_registerBuiltinParserAttribute(v_attrName_3961_, v_declName_3962_, v_behavior_boxed_3966_, v_ref_3964_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(lean_object* v_kind_3968_, lean_object* v_x_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v___x_3973_; lean_object* v_env_3974_; lean_object* v_nextMacroScope_3975_; lean_object* v_ngen_3976_; lean_object* v_auxDeclNGen_3977_; lean_object* v_traceState_3978_; lean_object* v_recordedDeps_3979_; lean_object* v_messages_3980_; lean_object* v_infoState_3981_; lean_object* v_snapshotTasks_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3994_; 
v___x_3973_ = lean_st_ref_take(v___y_3971_);
v_env_3974_ = lean_ctor_get(v___x_3973_, 0);
v_nextMacroScope_3975_ = lean_ctor_get(v___x_3973_, 1);
v_ngen_3976_ = lean_ctor_get(v___x_3973_, 2);
v_auxDeclNGen_3977_ = lean_ctor_get(v___x_3973_, 3);
v_traceState_3978_ = lean_ctor_get(v___x_3973_, 4);
v_recordedDeps_3979_ = lean_ctor_get(v___x_3973_, 6);
v_messages_3980_ = lean_ctor_get(v___x_3973_, 7);
v_infoState_3981_ = lean_ctor_get(v___x_3973_, 8);
v_snapshotTasks_3982_ = lean_ctor_get(v___x_3973_, 9);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3994_ == 0)
{
lean_object* v_unused_3995_; 
v_unused_3995_ = lean_ctor_get(v___x_3973_, 5);
lean_dec(v_unused_3995_);
v___x_3984_ = v___x_3973_;
v_isShared_3985_ = v_isSharedCheck_3994_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_snapshotTasks_3982_);
lean_inc(v_infoState_3981_);
lean_inc(v_messages_3980_);
lean_inc(v_recordedDeps_3979_);
lean_inc(v_traceState_3978_);
lean_inc(v_auxDeclNGen_3977_);
lean_inc(v_ngen_3976_);
lean_inc(v_nextMacroScope_3975_);
lean_inc(v_env_3974_);
lean_dec(v___x_3973_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3994_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3990_; 
v___x_3986_ = lean_box(0);
v___x_3987_ = l_Lean_Parser_addSyntaxNodeKind(v_env_3974_, v_kind_3968_);
v___x_3988_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg___closed__1);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 5, v___x_3988_);
lean_ctor_set(v___x_3984_, 0, v___x_3987_);
v___x_3990_ = v___x_3984_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3987_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_nextMacroScope_3975_);
lean_ctor_set(v_reuseFailAlloc_3993_, 2, v_ngen_3976_);
lean_ctor_set(v_reuseFailAlloc_3993_, 3, v_auxDeclNGen_3977_);
lean_ctor_set(v_reuseFailAlloc_3993_, 4, v_traceState_3978_);
lean_ctor_set(v_reuseFailAlloc_3993_, 5, v___x_3988_);
lean_ctor_set(v_reuseFailAlloc_3993_, 6, v_recordedDeps_3979_);
lean_ctor_set(v_reuseFailAlloc_3993_, 7, v_messages_3980_);
lean_ctor_set(v_reuseFailAlloc_3993_, 8, v_infoState_3981_);
lean_ctor_set(v_reuseFailAlloc_3993_, 9, v_snapshotTasks_3982_);
v___x_3990_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3991_ = lean_st_ref_put(v___y_3971_, v___x_3990_);
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3986_);
return v___x_3992_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0___boxed(lean_object* v_kind_3996_, lean_object* v_x_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___lam__0(v_kind_3996_, v_x_3997_, v___y_3998_, v___y_3999_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_f_4002_, lean_object* v_keys_4003_, lean_object* v_vals_4004_, lean_object* v_i_4005_, lean_object* v_acc_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v___x_4010_; uint8_t v___x_4011_; 
v___x_4010_ = lean_array_get_size(v_keys_4003_);
v___x_4011_ = lean_nat_dec_lt(v_i_4005_, v___x_4010_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; 
lean_dec(v_i_4005_);
lean_dec_ref(v_f_4002_);
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v_acc_4006_);
return v___x_4012_;
}
else
{
lean_object* v_k_4013_; lean_object* v_v_4014_; lean_object* v___x_4015_; 
v_k_4013_ = lean_array_fget_borrowed(v_keys_4003_, v_i_4005_);
v_v_4014_ = lean_array_fget_borrowed(v_vals_4004_, v_i_4005_);
lean_inc_ref(v_f_4002_);
lean_inc(v___y_4008_);
lean_inc_ref(v___y_4007_);
lean_inc(v_v_4014_);
lean_inc(v_k_4013_);
v___x_4015_ = lean_apply_6(v_f_4002_, v_acc_4006_, v_k_4013_, v_v_4014_, v___y_4007_, v___y_4008_, lean_box(0));
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v___x_4015_, 1);
v___x_4017_ = lean_unsigned_to_nat(1u);
v___x_4018_ = lean_nat_add(v_i_4005_, v___x_4017_);
lean_dec(v_i_4005_);
v_i_4005_ = v___x_4018_;
v_acc_4006_ = v_a_4016_;
goto _start;
}
else
{
lean_dec(v_i_4005_);
lean_dec_ref(v_f_4002_);
return v___x_4015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_4020_, lean_object* v_keys_4021_, lean_object* v_vals_4022_, lean_object* v_i_4023_, lean_object* v_acc_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4020_, v_keys_4021_, v_vals_4022_, v_i_4023_, v_acc_4024_, v___y_4025_, v___y_4026_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec_ref(v_vals_4022_);
lean_dec_ref(v_keys_4021_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_f_4029_, lean_object* v_as_4030_, size_t v_i_4031_, size_t v_stop_4032_, lean_object* v_b_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v_a_4038_; lean_object* v___y_4043_; uint8_t v___x_4045_; 
v___x_4045_ = lean_usize_dec_eq(v_i_4031_, v_stop_4032_);
if (v___x_4045_ == 0)
{
lean_object* v___x_4046_; 
v___x_4046_ = lean_array_uget_borrowed(v_as_4030_, v_i_4031_);
switch(lean_obj_tag(v___x_4046_))
{
case 0:
{
lean_object* v_key_4047_; lean_object* v_val_4048_; lean_object* v___x_4049_; 
v_key_4047_ = lean_ctor_get(v___x_4046_, 0);
v_val_4048_ = lean_ctor_get(v___x_4046_, 1);
lean_inc_ref(v_f_4029_);
lean_inc(v___y_4035_);
lean_inc_ref(v___y_4034_);
lean_inc(v_val_4048_);
lean_inc(v_key_4047_);
v___x_4049_ = lean_apply_6(v_f_4029_, v_b_4033_, v_key_4047_, v_val_4048_, v___y_4034_, v___y_4035_, lean_box(0));
v___y_4043_ = v___x_4049_;
goto v___jp_4042_;
}
case 1:
{
lean_object* v_node_4050_; lean_object* v___x_4051_; 
v_node_4050_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_node_4050_);
lean_inc_ref(v_f_4029_);
v___x_4051_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4029_, v_node_4050_, v_b_4033_, v___y_4034_, v___y_4035_);
v___y_4043_ = v___x_4051_;
goto v___jp_4042_;
}
default: 
{
v_a_4038_ = v_b_4033_;
goto v___jp_4037_;
}
}
}
else
{
lean_object* v___x_4052_; 
lean_dec_ref(v_f_4029_);
v___x_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4052_, 0, v_b_4033_);
return v___x_4052_;
}
v___jp_4037_:
{
size_t v___x_4039_; size_t v___x_4040_; 
v___x_4039_ = ((size_t)1ULL);
v___x_4040_ = lean_usize_add(v_i_4031_, v___x_4039_);
v_i_4031_ = v___x_4040_;
v_b_4033_ = v_a_4038_;
goto _start;
}
v___jp_4042_:
{
if (lean_obj_tag(v___y_4043_) == 0)
{
lean_object* v_a_4044_; 
v_a_4044_ = lean_ctor_get(v___y_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v___y_4043_, 1);
v_a_4038_ = v_a_4044_;
goto v___jp_4037_;
}
else
{
lean_dec_ref(v_f_4029_);
return v___y_4043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(lean_object* v_f_4053_, lean_object* v_x_4054_, lean_object* v_x_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
if (lean_obj_tag(v_x_4054_) == 0)
{
lean_object* v_es_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4072_; 
v_es_4059_ = lean_ctor_get(v_x_4054_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v_x_4054_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4061_ = v_x_4054_;
v_isShared_4062_ = v_isSharedCheck_4072_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_es_4059_);
lean_dec(v_x_4054_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4072_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; 
v___x_4063_ = lean_unsigned_to_nat(0u);
v___x_4064_ = lean_array_get_size(v_es_4059_);
v___x_4065_ = lean_nat_dec_lt(v___x_4063_, v___x_4064_);
if (v___x_4065_ == 0)
{
lean_object* v___x_4067_; 
lean_dec_ref(v_es_4059_);
lean_dec_ref(v_f_4053_);
if (v_isShared_4062_ == 0)
{
lean_ctor_set(v___x_4061_, 0, v_x_4055_);
v___x_4067_ = v___x_4061_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_x_4055_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
else
{
size_t v___x_4069_; size_t v___x_4070_; lean_object* v___x_4071_; 
lean_del_object(v___x_4061_);
v___x_4069_ = ((size_t)0ULL);
v___x_4070_ = lean_usize_of_nat(v___x_4064_);
v___x_4071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4053_, v_es_4059_, v___x_4069_, v___x_4070_, v_x_4055_, v___y_4056_, v___y_4057_);
lean_dec_ref(v_es_4059_);
return v___x_4071_;
}
}
}
else
{
lean_object* v_ks_4073_; lean_object* v_vs_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v_ks_4073_ = lean_ctor_get(v_x_4054_, 0);
lean_inc_ref(v_ks_4073_);
v_vs_4074_ = lean_ctor_get(v_x_4054_, 1);
lean_inc_ref(v_vs_4074_);
lean_dec_ref_known(v_x_4054_, 2);
v___x_4075_ = lean_unsigned_to_nat(0u);
v___x_4076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4053_, v_ks_4073_, v_vs_4074_, v___x_4075_, v_x_4055_, v___y_4056_, v___y_4057_);
lean_dec_ref(v_vs_4074_);
lean_dec_ref(v_ks_4073_);
return v___x_4076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_4077_, lean_object* v_x_4078_, lean_object* v_x_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4077_, v_x_4078_, v_x_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_4084_, lean_object* v_as_4085_, lean_object* v_i_4086_, lean_object* v_stop_4087_, lean_object* v_b_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
size_t v_i_boxed_4092_; size_t v_stop_boxed_4093_; lean_object* v_res_4094_; 
v_i_boxed_4092_ = lean_unbox_usize(v_i_4086_);
lean_dec(v_i_4086_);
v_stop_boxed_4093_ = lean_unbox_usize(v_stop_4087_);
lean_dec(v_stop_4087_);
v_res_4094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4084_, v_as_4085_, v_i_boxed_4092_, v_stop_boxed_4093_, v_b_4088_, v___y_4089_, v___y_4090_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec_ref(v_as_4085_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(lean_object* v_f_4095_, lean_object* v_x_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
lean_inc(v___y_4100_);
lean_inc_ref(v___y_4099_);
v___x_4102_ = lean_apply_5(v_f_4095_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, lean_box(0));
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed(lean_object* v_f_4103_, lean_object* v_x_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0(v_f_4103_, v_x_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(lean_object* v_map_4111_, lean_object* v_f_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v___f_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___f_4116_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4116_, 0, v_f_4112_);
v___x_4117_ = lean_box(0);
v___x_4118_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v___f_4116_, v_map_4111_, v___x_4117_, v___y_4113_, v___y_4114_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg___boxed(lean_object* v_map_4119_, lean_object* v_f_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4119_, v_f_4120_, v___y_4121_, v___y_4122_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
return v_res_4124_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = ((lean_object*)(l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__0));
v___x_4127_ = l_Lean_stringToMessageData(v___x_4126_);
return v___x_4127_;
}
}
static lean_object* _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_updateBuiltinTokens___closed__1));
v___x_4129_ = l_Lean_stringToMessageData(v___x_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(uint8_t v_attrKind_4130_, lean_object* v_declName_4131_, lean_object* v_as_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
if (lean_obj_tag(v_as_4132_) == 0)
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
lean_dec(v_declName_4131_);
v___x_4136_ = lean_box(0);
v___x_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
return v___x_4137_;
}
else
{
lean_object* v_head_4138_; lean_object* v_tail_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4170_; 
v_head_4138_ = lean_ctor_get(v_as_4132_, 0);
v_tail_4139_ = lean_ctor_get(v_as_4132_, 1);
v_isSharedCheck_4170_ = !lean_is_exclusive(v_as_4132_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4141_ = v_as_4132_;
v_isShared_4142_ = v_isSharedCheck_4170_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_tail_4139_);
lean_inc(v_head_4138_);
lean_dec(v_as_4132_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4170_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___y_4144_; uint8_t v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = 0;
v___x_4147_ = l_Lean_Parser_addToken(v_head_4138_, v_attrKind_4130_, v___y_4133_, v___y_4134_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_del_object(v___x_4141_);
v___y_4144_ = v___x_4147_;
goto v___jp_4143_;
}
else
{
lean_object* v_a_4148_; uint8_t v___y_4150_; uint8_t v___x_4168_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
v___x_4168_ = l_Lean_Exception_isInterrupt(v_a_4148_);
if (v___x_4168_ == 0)
{
uint8_t v___x_4169_; 
lean_inc(v_a_4148_);
v___x_4169_ = l_Lean_Exception_isRuntime(v_a_4148_);
v___y_4150_ = v___x_4169_;
goto v___jp_4149_;
}
else
{
v___y_4150_ = v___x_4168_;
goto v___jp_4149_;
}
v___jp_4149_:
{
if (v___y_4150_ == 0)
{
if (lean_obj_tag(v_a_4148_) == 0)
{
lean_object* v_msg_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4166_; 
lean_dec_ref_known(v___x_4147_, 1);
v_msg_4151_ = lean_ctor_get(v_a_4148_, 1);
v_isSharedCheck_4166_ = !lean_is_exclusive(v_a_4148_);
if (v_isSharedCheck_4166_ == 0)
{
lean_object* v_unused_4167_; 
v_unused_4167_ = lean_ctor_get(v_a_4148_, 0);
lean_dec(v_unused_4167_);
v___x_4153_ = v_a_4148_;
v_isShared_4154_ = v_isSharedCheck_4166_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_msg_4151_);
lean_dec(v_a_4148_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4166_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4158_; 
v___x_4155_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__1);
lean_inc(v_declName_4131_);
v___x_4156_ = l_Lean_MessageData_ofConstName(v_declName_4131_, v___x_4146_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set_tag(v___x_4153_, 7);
lean_ctor_set(v___x_4153_, 1, v___x_4156_);
lean_ctor_set(v___x_4153_, 0, v___x_4155_);
v___x_4158_ = v___x_4153_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4155_);
lean_ctor_set(v_reuseFailAlloc_4165_, 1, v___x_4156_);
v___x_4158_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
lean_object* v___x_4159_; lean_object* v___x_4161_; 
v___x_4159_ = lean_obj_once(&l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2, &l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2_once, _init_l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___closed__2);
if (v_isShared_4142_ == 0)
{
lean_ctor_set_tag(v___x_4141_, 7);
lean_ctor_set(v___x_4141_, 1, v___x_4159_);
lean_ctor_set(v___x_4141_, 0, v___x_4158_);
v___x_4161_ = v___x_4141_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v___x_4158_);
lean_ctor_set(v_reuseFailAlloc_4164_, 1, v___x_4159_);
v___x_4161_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
lean_ctor_set(v___x_4162_, 1, v_msg_4151_);
v___x_4163_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4162_, v___y_4133_, v___y_4134_);
v___y_4144_ = v___x_4163_;
goto v___jp_4143_;
}
}
}
}
else
{
lean_dec(v_a_4148_);
lean_del_object(v___x_4141_);
v___y_4144_ = v___x_4147_;
goto v___jp_4143_;
}
}
else
{
lean_dec(v_a_4148_);
lean_del_object(v___x_4141_);
v___y_4144_ = v___x_4147_;
goto v___jp_4143_;
}
}
}
v___jp_4143_:
{
if (lean_obj_tag(v___y_4144_) == 0)
{
lean_dec_ref_known(v___y_4144_, 1);
v_as_4132_ = v_tail_4139_;
goto _start;
}
else
{
lean_dec(v_tail_4139_);
lean_dec(v_declName_4131_);
return v___y_4144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0___boxed(lean_object* v_attrKind_4171_, lean_object* v_declName_4172_, lean_object* v_as_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
uint8_t v_attrKind_boxed_4177_; lean_object* v_res_4178_; 
v_attrKind_boxed_4177_ = lean_unbox(v_attrKind_4171_);
v_res_4178_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_boxed_4177_, v_declName_4172_, v_as_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(lean_object* v_catName_4180_, lean_object* v_declName_4181_, lean_object* v_stx_4182_, uint8_t v_attrKind_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v___f_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___f_4187_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___closed__0));
v___x_4188_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4189_ = l_Lean_Attribute_Builtin_getPrio(v_stx_4182_, v_a_4184_, v_a_4185_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4191_; lean_object* v_env_4192_; lean_object* v___x_4193_; lean_object* v_ext_4194_; lean_object* v_toEnvExtension_4195_; lean_object* v_asyncMode_4196_; uint8_t v___x_4197_; lean_object* v___x_4198_; lean_object* v_categories_4199_; lean_object* v___x_4200_; lean_object* v_env_4201_; lean_object* v_ref_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___x_4191_ = lean_st_ref_get(v_a_4185_);
v_env_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc_ref(v_env_4192_);
lean_dec(v___x_4191_);
v___x_4193_ = l_Lean_Parser_parserExtension;
v_ext_4194_ = lean_ctor_get(v___x_4193_, 1);
v_toEnvExtension_4195_ = lean_ctor_get(v_ext_4194_, 0);
v_asyncMode_4196_ = lean_ctor_get(v_toEnvExtension_4195_, 2);
v___x_4197_ = 0;
v___x_4198_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4188_, v___x_4193_, v_env_4192_, v_asyncMode_4196_, v___x_4197_);
v_categories_4199_ = lean_ctor_get(v___x_4198_, 2);
lean_inc_ref_n(v_categories_4199_, 2);
lean_dec(v___x_4198_);
v___x_4200_ = lean_st_ref_get(v_a_4185_);
v_env_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc_ref(v_env_4201_);
lean_dec(v___x_4200_);
v_ref_4202_ = lean_ctor_get(v_a_4184_, 2);
v___x_4203_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4184_);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v_env_4201_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
lean_inc(v_declName_4181_);
v___x_4205_ = l_Lean_Parser_mkParserOfConstant(v_categories_4199_, v_declName_4181_, v___x_4204_);
lean_dec_ref_known(v___x_4204_, 2);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v_snd_4207_; lean_object* v_info_4208_; lean_object* v_fst_4209_; lean_object* v_collectTokens_4210_; lean_object* v_collectKinds_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
v_snd_4207_ = lean_ctor_get(v_a_4206_, 1);
lean_inc(v_snd_4207_);
v_info_4208_ = lean_ctor_get(v_snd_4207_, 0);
v_fst_4209_ = lean_ctor_get(v_a_4206_, 0);
lean_inc(v_fst_4209_);
lean_dec(v_a_4206_);
v_collectTokens_4210_ = lean_ctor_get(v_info_4208_, 0);
v_collectKinds_4211_ = lean_ctor_get(v_info_4208_, 1);
v___x_4212_ = lean_box(0);
lean_inc_ref(v_collectTokens_4210_);
v___x_4213_ = lean_apply_1(v_collectTokens_4210_, v___x_4212_);
lean_inc(v_declName_4181_);
v___x_4214_ = l_List_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__0(v_attrKind_4183_, v_declName_4181_, v___x_4213_, v_a_4184_, v_a_4185_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
lean_dec_ref_known(v___x_4214_, 1);
v___x_4215_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_848551512____hygCtx___hyg_2_);
lean_inc_ref(v_collectKinds_4211_);
v___x_4216_ = lean_apply_1(v_collectKinds_4211_, v___x_4215_);
v___x_4217_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v___x_4216_, v___f_4187_, v_a_4184_, v_a_4185_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v___x_4218_; uint8_t v___x_4219_; uint8_t v___x_4220_; lean_object* v___x_4221_; 
lean_dec_ref_known(v___x_4217_, 1);
lean_inc(v_a_4190_);
lean_inc(v_snd_4207_);
lean_inc_n(v_declName_4181_, 2);
lean_inc_n(v_catName_4180_, 2);
v___x_4218_ = lean_alloc_ctor(3, 4, 1);
lean_ctor_set(v___x_4218_, 0, v_catName_4180_);
lean_ctor_set(v___x_4218_, 1, v_declName_4181_);
lean_ctor_set(v___x_4218_, 2, v_snd_4207_);
lean_ctor_set(v___x_4218_, 3, v_a_4190_);
v___x_4219_ = lean_unbox(v_fst_4209_);
lean_ctor_set_uint8(v___x_4218_, sizeof(void*)*4, v___x_4219_);
v___x_4220_ = lean_unbox(v_fst_4209_);
lean_dec(v_fst_4209_);
v___x_4221_ = l_Lean_Parser_addParser(v_categories_4199_, v_catName_4180_, v_declName_4181_, v___x_4220_, v_snd_4207_, v_a_4190_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4231_; 
lean_dec_ref_known(v___x_4218_, 4);
lean_dec(v_declName_4181_);
lean_dec(v_catName_4180_);
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4224_ = v___x_4221_;
v_isShared_4225_ = v_isSharedCheck_4231_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4221_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4231_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
lean_ctor_set_tag(v___x_4224_, 3);
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4228_ = l_Lean_MessageData_ofFormat(v___x_4227_);
v___x_4229_ = l_Lean_throwError___at___00__private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2__spec__0___redArg(v___x_4228_, v_a_4184_, v_a_4185_);
return v___x_4229_;
}
}
}
else
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_dec_ref_known(v___x_4221_, 1);
v___x_4232_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Parser_addToken_spec__1___redArg(v___x_4193_, v___x_4218_, v_attrKind_4183_, v_a_4184_, v_a_4185_);
lean_dec_ref(v___x_4232_);
v___x_4233_ = l_Lean_Parser_runParserAttributeHooks(v_catName_4180_, v_declName_4181_, v___x_4197_, v_a_4184_, v_a_4185_);
return v___x_4233_;
}
}
else
{
lean_dec(v_fst_4209_);
lean_dec(v_snd_4207_);
lean_dec_ref(v_categories_4199_);
lean_dec(v_a_4190_);
lean_dec(v_declName_4181_);
lean_dec(v_catName_4180_);
return v___x_4217_;
}
}
else
{
lean_dec(v_fst_4209_);
lean_dec(v_snd_4207_);
lean_dec_ref(v_categories_4199_);
lean_dec(v_a_4190_);
lean_dec(v_declName_4181_);
lean_dec(v_catName_4180_);
return v___x_4214_;
}
}
else
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4245_; 
lean_dec_ref(v_categories_4199_);
lean_dec(v_a_4190_);
lean_dec(v_declName_4181_);
lean_dec(v_catName_4180_);
v_a_4234_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4236_ = v___x_4205_;
v_isShared_4237_ = v_isSharedCheck_4245_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4205_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4245_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4238_ = lean_io_error_to_string(v_a_4234_);
v___x_4239_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4238_);
v___x_4240_ = l_Lean_MessageData_ofFormat(v___x_4239_);
lean_inc(v_ref_4202_);
v___x_4241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4241_, 0, v_ref_4202_);
lean_ctor_set(v___x_4241_, 1, v___x_4240_);
if (v_isShared_4237_ == 0)
{
lean_ctor_set(v___x_4236_, 0, v___x_4241_);
v___x_4243_ = v___x_4236_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec(v_declName_4181_);
lean_dec(v_catName_4180_);
v_a_4246_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4189_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4189_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg___boxed(lean_object* v_catName_4254_, lean_object* v_declName_4255_, lean_object* v_stx_4256_, lean_object* v_attrKind_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_){
_start:
{
uint8_t v_attrKind_boxed_4261_; lean_object* v_res_4262_; 
v_attrKind_boxed_4261_ = lean_unbox(v_attrKind_4257_);
v_res_4262_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4254_, v_declName_4255_, v_stx_4256_, v_attrKind_boxed_4261_, v_a_4258_, v_a_4259_);
lean_dec(v_a_4259_);
lean_dec_ref(v_a_4258_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(lean_object* v___attrName_4263_, lean_object* v_catName_4264_, lean_object* v_declName_4265_, lean_object* v_stx_4266_, uint8_t v_attrKind_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4264_, v_declName_4265_, v_stx_4266_, v_attrKind_4267_, v_a_4268_, v_a_4269_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___boxed(lean_object* v___attrName_4272_, lean_object* v_catName_4273_, lean_object* v_declName_4274_, lean_object* v_stx_4275_, lean_object* v_attrKind_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_){
_start:
{
uint8_t v_attrKind_boxed_4280_; lean_object* v_res_4281_; 
v_attrKind_boxed_4280_ = lean_unbox(v_attrKind_4276_);
v_res_4281_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add(v___attrName_4272_, v_catName_4273_, v_declName_4274_, v_stx_4275_, v_attrKind_boxed_4280_, v_a_4277_, v_a_4278_);
lean_dec(v_a_4278_);
lean_dec_ref(v_a_4277_);
lean_dec(v___attrName_4272_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(lean_object* v_00_u03b2_4282_, lean_object* v_map_4283_, lean_object* v_f_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___redArg(v_map_4283_, v_f_4284_, v___y_4285_, v___y_4286_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1___boxed(lean_object* v_00_u03b2_4289_, lean_object* v_map_4290_, lean_object* v_f_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
lean_object* v_res_4295_; 
v_res_4295_ = l_Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1(v_00_u03b2_4289_, v_map_4290_, v_f_4291_, v___y_4292_, v___y_4293_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(lean_object* v_map_4296_, lean_object* v_f_4297_, lean_object* v_init_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4297_, v_map_4296_, v_init_4298_, v___y_4299_, v___y_4300_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg___boxed(lean_object* v_map_4303_, lean_object* v_f_4304_, lean_object* v_init_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___redArg(v_map_4303_, v_f_4304_, v_init_4305_, v___y_4306_, v___y_4307_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(lean_object* v_00_u03c3_4310_, lean_object* v_00_u03b2_4311_, lean_object* v_map_4312_, lean_object* v_f_4313_, lean_object* v_init_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4313_, v_map_4312_, v_init_4314_, v___y_4315_, v___y_4316_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1___boxed(lean_object* v_00_u03c3_4319_, lean_object* v_00_u03b2_4320_, lean_object* v_map_4321_, lean_object* v_f_4322_, lean_object* v_init_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1(v_00_u03c3_4319_, v_00_u03b2_4320_, v_map_4321_, v_f_4322_, v_init_4323_, v___y_4324_, v___y_4325_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(lean_object* v_00_u03c3_4328_, lean_object* v_00_u03b1_4329_, lean_object* v_00_u03b2_4330_, lean_object* v_f_4331_, lean_object* v_x_4332_, lean_object* v_x_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; 
v___x_4337_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___redArg(v_f_4331_, v_x_4332_, v_x_4333_, v___y_4334_, v___y_4335_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03c3_4338_, lean_object* v_00_u03b1_4339_, lean_object* v_00_u03b2_4340_, lean_object* v_f_4341_, lean_object* v_x_4342_, lean_object* v_x_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2(v_00_u03c3_4338_, v_00_u03b1_4339_, v_00_u03b2_4340_, v_f_4341_, v_x_4342_, v_x_4343_, v___y_4344_, v___y_4345_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_4348_, lean_object* v_00_u03b2_4349_, lean_object* v_00_u03c3_4350_, lean_object* v_f_4351_, lean_object* v_as_4352_, size_t v_i_4353_, size_t v_stop_4354_, lean_object* v_b_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___redArg(v_f_4351_, v_as_4352_, v_i_4353_, v_stop_4354_, v_b_4355_, v___y_4356_, v___y_4357_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4360_, lean_object* v_00_u03b2_4361_, lean_object* v_00_u03c3_4362_, lean_object* v_f_4363_, lean_object* v_as_4364_, lean_object* v_i_4365_, lean_object* v_stop_4366_, lean_object* v_b_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
size_t v_i_boxed_4371_; size_t v_stop_boxed_4372_; lean_object* v_res_4373_; 
v_i_boxed_4371_ = lean_unbox_usize(v_i_4365_);
lean_dec(v_i_4365_);
v_stop_boxed_4372_ = lean_unbox_usize(v_stop_4366_);
lean_dec(v_stop_4366_);
v_res_4373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_4360_, v_00_u03b2_4361_, v_00_u03c3_4362_, v_f_4363_, v_as_4364_, v_i_boxed_4371_, v_stop_boxed_4372_, v_b_4367_, v___y_4368_, v___y_4369_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v_as_4364_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_4374_, lean_object* v_00_u03b1_4375_, lean_object* v_00_u03b2_4376_, lean_object* v_f_4377_, lean_object* v_keys_4378_, lean_object* v_vals_4379_, lean_object* v_heq_4380_, lean_object* v_i_4381_, lean_object* v_acc_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
lean_object* v___x_4386_; 
v___x_4386_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___redArg(v_f_4377_, v_keys_4378_, v_vals_4379_, v_i_4381_, v_acc_4382_, v___y_4383_, v___y_4384_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_4387_, lean_object* v_00_u03b1_4388_, lean_object* v_00_u03b2_4389_, lean_object* v_f_4390_, lean_object* v_keys_4391_, lean_object* v_vals_4392_, lean_object* v_heq_4393_, lean_object* v_i_4394_, lean_object* v_acc_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00__private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_4387_, v_00_u03b1_4388_, v_00_u03b2_4389_, v_f_4390_, v_keys_4391_, v_vals_4392_, v_heq_4393_, v_i_4394_, v_acc_4395_, v___y_4396_, v___y_4397_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec_ref(v_vals_4392_);
lean_dec_ref(v_keys_4391_);
return v_res_4399_;
}
}
static lean_object* _init_l_Lean_Parser_mkParserAttributeImpl___auto__1(void){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0(lean_object* v_catName_4401_, lean_object* v_declName_4402_, lean_object* v_stx_4403_, uint8_t v_attrKind_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l___private_Lean_Parser_Extension_0__Lean_Parser_ParserAttribute_add___redArg(v_catName_4401_, v_declName_4402_, v_stx_4403_, v_attrKind_4404_, v___y_4405_, v___y_4406_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed(lean_object* v_catName_4409_, lean_object* v_declName_4410_, lean_object* v_stx_4411_, lean_object* v_attrKind_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
uint8_t v_attrKind_boxed_4416_; lean_object* v_res_4417_; 
v_attrKind_boxed_4416_ = lean_unbox(v_attrKind_4412_);
v_res_4417_ = l_Lean_Parser_mkParserAttributeImpl___lam__0(v_catName_4409_, v_declName_4410_, v_stx_4411_, v_attrKind_boxed_4416_, v___y_4413_, v___y_4414_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkParserAttributeImpl(lean_object* v_attrName_4419_, lean_object* v_catName_4420_, lean_object* v_ref_4421_){
_start:
{
lean_object* v___f_4422_; lean_object* v___f_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___f_4422_ = lean_alloc_closure((void*)(l_Lean_Parser_mkParserAttributeImpl___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4422_, 0, v_catName_4420_);
lean_inc(v_attrName_4419_);
v___f_4423_ = lean_alloc_closure((void*)(l_Lean_Parser_registerBuiltinParserAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4423_, 0, v_attrName_4419_);
v___x_4424_ = ((lean_object*)(l_Lean_Parser_mkParserAttributeImpl___closed__0));
v___x_4425_ = 1;
v___x_4426_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4426_, 0, v_ref_4421_);
lean_ctor_set(v___x_4426_, 1, v_attrName_4419_);
lean_ctor_set(v___x_4426_, 2, v___x_4424_);
lean_ctor_set_uint8(v___x_4426_, sizeof(void*)*3, v___x_4425_);
v___x_4427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4426_);
lean_ctor_set(v___x_4427_, 1, v___f_4422_);
lean_ctor_set(v___x_4427_, 2, v___f_4423_);
return v___x_4427_;
}
}
static lean_object* _init_l_Lean_Parser_registerBuiltinDynamicParserAttribute___auto__1(void){
_start:
{
lean_object* v___x_4428_; 
v___x_4428_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute(lean_object* v_attrName_4429_, lean_object* v_catName_4430_, lean_object* v_ref_4431_){
_start:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4433_ = l_Lean_Parser_mkParserAttributeImpl(v_attrName_4429_, v_catName_4430_, v_ref_4431_);
v___x_4434_ = l_Lean_registerBuiltinAttribute(v___x_4433_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerBuiltinDynamicParserAttribute___boxed(lean_object* v_attrName_4435_, lean_object* v_catName_4436_, lean_object* v_ref_4437_, lean_object* v_a_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v_attrName_4435_, v_catName_4436_, v_ref_4437_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(lean_object* v_ref_4443_, lean_object* v_args_4444_){
_start:
{
if (lean_obj_tag(v_args_4444_) == 1)
{
lean_object* v_head_4447_; 
v_head_4447_ = lean_ctor_get(v_args_4444_, 0);
lean_inc(v_head_4447_);
if (lean_obj_tag(v_head_4447_) == 2)
{
lean_object* v_tail_4448_; 
v_tail_4448_ = lean_ctor_get(v_args_4444_, 1);
lean_inc(v_tail_4448_);
lean_dec_ref_known(v_args_4444_, 2);
if (lean_obj_tag(v_tail_4448_) == 1)
{
lean_object* v_head_4449_; 
v_head_4449_ = lean_ctor_get(v_tail_4448_, 0);
lean_inc(v_head_4449_);
if (lean_obj_tag(v_head_4449_) == 2)
{
lean_object* v_tail_4450_; 
v_tail_4450_ = lean_ctor_get(v_tail_4448_, 1);
lean_inc(v_tail_4450_);
lean_dec_ref_known(v_tail_4448_, 2);
if (lean_obj_tag(v_tail_4450_) == 0)
{
lean_object* v_v_4451_; lean_object* v_v_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4460_; 
v_v_4451_ = lean_ctor_get(v_head_4447_, 0);
lean_inc(v_v_4451_);
lean_dec_ref_known(v_head_4447_, 1);
v_v_4452_ = lean_ctor_get(v_head_4449_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v_head_4449_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4454_ = v_head_4449_;
v_isShared_4455_ = v_isSharedCheck_4460_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_v_4452_);
lean_dec(v_head_4449_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4460_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4456_; lean_object* v___x_4458_; 
v___x_4456_ = l_Lean_Parser_mkParserAttributeImpl(v_v_4451_, v_v_4452_, v_ref_4443_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set_tag(v___x_4454_, 1);
lean_ctor_set(v___x_4454_, 0, v___x_4456_);
v___x_4458_ = v___x_4454_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4456_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
else
{
lean_dec_ref_known(v_head_4449_, 1);
lean_dec(v_tail_4450_);
lean_dec_ref_known(v_head_4447_, 1);
lean_dec(v_ref_4443_);
goto v___jp_4445_;
}
}
else
{
lean_dec(v_head_4449_);
lean_dec_ref_known(v_tail_4448_, 2);
lean_dec_ref_known(v_head_4447_, 1);
lean_dec(v_ref_4443_);
goto v___jp_4445_;
}
}
else
{
lean_dec(v_tail_4448_);
lean_dec_ref_known(v_head_4447_, 1);
lean_dec(v_ref_4443_);
goto v___jp_4445_;
}
}
else
{
lean_dec_ref_known(v_args_4444_, 2);
lean_dec(v_head_4447_);
lean_dec(v_ref_4443_);
goto v___jp_4445_;
}
}
else
{
lean_dec(v_args_4444_);
lean_dec(v_ref_4443_);
goto v___jp_4445_;
}
v___jp_4445_:
{
lean_object* v___x_4446_; 
v___x_4446_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0___closed__1_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
return v___x_4446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___f_4466_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4467_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
v___x_4468_ = l_Lean_registerAttributeImplBuilder(v___x_4467_, v___f_4466_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2____boxed(lean_object* v_a_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_();
return v_res_4470_;
}
}
static lean_object* _init_l_Lean_Parser_registerParserCategory___auto__1(void){
_start:
{
lean_object* v___x_4471_; 
v___x_4471_ = lean_obj_once(&l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18, &l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18_once, _init_l_Lean_Parser_registerBuiltinParserAttribute___auto__1___closed__18);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory(lean_object* v_env_4472_, lean_object* v_attrName_4473_, lean_object* v_catName_4474_, uint8_t v_behavior_4475_, lean_object* v_ref_4476_){
_start:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; 
lean_inc(v_ref_4476_);
lean_inc(v_catName_4474_);
v___x_4478_ = l_Lean_Parser_addParserCategory(v_env_4472_, v_catName_4474_, v_ref_4476_, v_behavior_4475_);
v___x_4479_ = l_IO_ofExcept___at___00__private_Lean_Parser_Extension_0__Lean_Parser_addBuiltinParserCategory_spec__0___redArg(v___x_4478_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4493_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4482_ = v___x_4479_;
v_isShared_4483_ = v_isSharedCheck_4493_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v___x_4479_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4493_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4484_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3896994716____hygCtx___hyg_2_));
if (v_isShared_4483_ == 0)
{
lean_ctor_set_tag(v___x_4482_, 2);
lean_ctor_set(v___x_4482_, 0, v_attrName_4473_);
v___x_4486_ = v___x_4482_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_attrName_4473_);
v___x_4486_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4487_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4487_, 0, v_catName_4474_);
v___x_4488_ = lean_box(0);
v___x_4489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4487_);
lean_ctor_set(v___x_4489_, 1, v___x_4488_);
v___x_4490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4486_);
lean_ctor_set(v___x_4490_, 1, v___x_4489_);
v___x_4491_ = l_Lean_registerAttributeOfBuilder(v_a_4480_, v___x_4484_, v_ref_4476_, v___x_4490_);
return v___x_4491_;
}
}
}
else
{
lean_dec(v_ref_4476_);
lean_dec(v_catName_4474_);
lean_dec(v_attrName_4473_);
return v___x_4479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_registerParserCategory___boxed(lean_object* v_env_4494_, lean_object* v_attrName_4495_, lean_object* v_catName_4496_, lean_object* v_behavior_4497_, lean_object* v_ref_4498_, lean_object* v_a_4499_){
_start:
{
uint8_t v_behavior_boxed_4500_; lean_object* v_res_4501_; 
v_behavior_boxed_4500_ = lean_unbox(v_behavior_4497_);
v_res_4501_ = l_Lean_Parser_registerParserCategory(v_env_4494_, v_attrName_4495_, v_catName_4496_, v_behavior_boxed_4500_, v_ref_4498_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4524_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4525_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4526_ = 0;
v___x_4527_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_));
v___x_4528_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4524_, v___x_4525_, v___x_4526_, v___x_4527_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2____boxed(lean_object* v_a_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_346849000____hygCtx___hyg_2_();
return v_res_4530_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4536_ = lean_unsigned_to_nat(3431364690u);
v___x_4537_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4538_ = l_Lean_Name_num___override(v___x_4537_, v___x_4536_);
return v___x_4538_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4539_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4540_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4541_ = l_Lean_Name_str___override(v___x_4540_, v___x_4539_);
return v___x_4541_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4542_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4543_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4544_ = l_Lean_Name_str___override(v___x_4543_, v___x_4542_);
return v___x_4544_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4545_ = lean_unsigned_to_nat(2u);
v___x_4546_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4547_ = l_Lean_Name_num___override(v___x_4546_, v___x_4545_);
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4549_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4550_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_));
v___x_4551_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_);
v___x_4552_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4549_, v___x_4550_, v___x_4551_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2____boxed(lean_object* v_a_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3431364690____hygCtx___hyg_2_();
return v_res_4554_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4564_ = lean_unsigned_to_nat(2342493449u);
v___x_4565_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4566_ = l_Lean_Name_num___override(v___x_4565_, v___x_4564_);
return v___x_4566_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4567_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4568_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4569_ = l_Lean_Name_str___override(v___x_4568_, v___x_4567_);
return v___x_4569_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4570_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4571_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4572_ = l_Lean_Name_str___override(v___x_4571_, v___x_4570_);
return v___x_4572_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4573_ = lean_unsigned_to_nat(2u);
v___x_4574_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4575_ = l_Lean_Name_num___override(v___x_4574_, v___x_4573_);
return v___x_4575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; uint8_t v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4577_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4578_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_));
v___x_4579_ = 0;
v___x_4580_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_);
v___x_4581_ = l_Lean_Parser_registerBuiltinParserAttribute(v___x_4577_, v___x_4578_, v___x_4579_, v___x_4580_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2____boxed(lean_object* v_a_4582_){
_start:
{
lean_object* v_res_4583_; 
v_res_4583_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_2342493449____hygCtx___hyg_2_();
return v_res_4583_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4589_ = lean_unsigned_to_nat(3226070615u);
v___x_4590_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4591_ = l_Lean_Name_num___override(v___x_4590_, v___x_4589_);
return v___x_4591_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4592_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4593_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4594_ = l_Lean_Name_str___override(v___x_4593_, v___x_4592_);
return v___x_4594_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4595_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Extension_3646333153____hygCtx___hyg_2_));
v___x_4596_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4597_ = l_Lean_Name_str___override(v___x_4596_, v___x_4595_);
return v___x_4597_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4598_ = lean_unsigned_to_nat(2u);
v___x_4599_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4600_ = l_Lean_Name_num___override(v___x_4599_, v___x_4598_);
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4602_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4603_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4604_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_);
v___x_4605_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(v___x_4602_, v___x_4603_, v___x_4604_);
return v___x_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2____boxed(lean_object* v_a_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_();
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_commandParser(lean_object* v_rbp_4608_){
_start:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4609_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_3226070615____hygCtx___hyg_2_));
v___x_4610_ = l_Lean_Parser_categoryParser(v___x_4609_, v_rbp_4608_);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(uint8_t v_addOpenSimple_4611_, lean_object* v_x_4612_, lean_object* v_x_4613_){
_start:
{
if (lean_obj_tag(v_x_4613_) == 0)
{
return v_x_4612_;
}
else
{
lean_object* v_head_4614_; lean_object* v_tail_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4638_; 
v_head_4614_ = lean_ctor_get(v_x_4613_, 0);
v_tail_4615_ = lean_ctor_get(v_x_4613_, 1);
v_isSharedCheck_4638_ = !lean_is_exclusive(v_x_4613_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4617_ = v_x_4613_;
v_isShared_4618_ = v_isSharedCheck_4638_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_tail_4615_);
lean_inc(v_head_4614_);
lean_dec(v_x_4613_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4638_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v_fst_4619_; lean_object* v_snd_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4637_; 
v_fst_4619_ = lean_ctor_get(v_x_4612_, 0);
v_snd_4620_ = lean_ctor_get(v_x_4612_, 1);
v_isSharedCheck_4637_ = !lean_is_exclusive(v_x_4612_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4622_ = v_x_4612_;
v_isShared_4623_ = v_isSharedCheck_4637_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_snd_4620_);
lean_inc(v_fst_4619_);
lean_dec(v_x_4612_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4637_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___y_4625_; 
if (v_addOpenSimple_4611_ == 0)
{
lean_del_object(v___x_4617_);
v___y_4625_ = v_snd_4620_;
goto v___jp_4624_;
}
else
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4635_; 
v___x_4632_ = lean_box(0);
lean_inc(v_head_4614_);
v___x_4633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4633_, 0, v_head_4614_);
lean_ctor_set(v___x_4633_, 1, v___x_4632_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 1, v_snd_4620_);
lean_ctor_set(v___x_4617_, 0, v___x_4633_);
v___x_4635_ = v___x_4617_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
lean_ctor_set(v_reuseFailAlloc_4636_, 1, v_snd_4620_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
v___y_4625_ = v___x_4635_;
goto v___jp_4624_;
}
}
v___jp_4624_:
{
lean_object* v___x_4626_; lean_object* v_env_4627_; lean_object* v___x_4629_; 
v___x_4626_ = l_Lean_Parser_parserExtension;
v_env_4627_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(v___x_4626_, v_fst_4619_, v_head_4614_);
if (v_isShared_4623_ == 0)
{
lean_ctor_set(v___x_4622_, 1, v___y_4625_);
lean_ctor_set(v___x_4622_, 0, v_env_4627_);
v___x_4629_ = v___x_4622_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_env_4627_);
lean_ctor_set(v_reuseFailAlloc_4631_, 1, v___y_4625_);
v___x_4629_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
v_x_4612_ = v___x_4629_;
v_x_4613_ = v_tail_4615_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0___boxed(lean_object* v_addOpenSimple_4639_, lean_object* v_x_4640_, lean_object* v_x_4641_){
_start:
{
uint8_t v_addOpenSimple_boxed_4642_; lean_object* v_res_4643_; 
v_addOpenSimple_boxed_4642_ = lean_unbox(v_addOpenSimple_4639_);
v_res_4643_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_boxed_4642_, v_x_4640_, v_x_4641_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(uint8_t v_addOpenSimple_4644_, lean_object* v_as_4645_, size_t v_i_4646_, size_t v_stop_4647_, lean_object* v_b_4648_){
_start:
{
uint8_t v___x_4649_; 
v___x_4649_ = lean_usize_dec_eq(v_i_4646_, v_stop_4647_);
if (v___x_4649_ == 0)
{
lean_object* v_toParserModuleContext_4650_; lean_object* v_toInputContext_4651_; lean_object* v_toCacheableParserContext_4652_; lean_object* v_tokens_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4680_; 
v_toParserModuleContext_4650_ = lean_ctor_get(v_b_4648_, 1);
v_toInputContext_4651_ = lean_ctor_get(v_b_4648_, 0);
v_toCacheableParserContext_4652_ = lean_ctor_get(v_b_4648_, 2);
v_tokens_4653_ = lean_ctor_get(v_b_4648_, 3);
v_isSharedCheck_4680_ = !lean_is_exclusive(v_b_4648_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4655_ = v_b_4648_;
v_isShared_4656_ = v_isSharedCheck_4680_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_tokens_4653_);
lean_inc(v_toCacheableParserContext_4652_);
lean_inc(v_toParserModuleContext_4650_);
lean_inc(v_toInputContext_4651_);
lean_dec(v_b_4648_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4680_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v_env_4657_; lean_object* v_options_4658_; lean_object* v_currNamespace_4659_; lean_object* v_openDecls_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4679_; 
v_env_4657_ = lean_ctor_get(v_toParserModuleContext_4650_, 0);
v_options_4658_ = lean_ctor_get(v_toParserModuleContext_4650_, 1);
v_currNamespace_4659_ = lean_ctor_get(v_toParserModuleContext_4650_, 2);
v_openDecls_4660_ = lean_ctor_get(v_toParserModuleContext_4650_, 3);
v_isSharedCheck_4679_ = !lean_is_exclusive(v_toParserModuleContext_4650_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4662_ = v_toParserModuleContext_4650_;
v_isShared_4663_ = v_isSharedCheck_4679_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_openDecls_4660_);
lean_inc(v_currNamespace_4659_);
lean_inc(v_options_4658_);
lean_inc(v_env_4657_);
lean_dec(v_toParserModuleContext_4650_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4679_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4664_; lean_object* v_nss_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v_fst_4668_; lean_object* v_snd_4669_; lean_object* v___x_4671_; 
v___x_4664_ = lean_array_uget_borrowed(v_as_4645_, v_i_4646_);
lean_inc(v___x_4664_);
lean_inc(v_openDecls_4660_);
lean_inc(v_currNamespace_4659_);
lean_inc_ref(v_env_4657_);
v_nss_4665_ = l_Lean_ResolveName_resolveNamespace(v_env_4657_, v_currNamespace_4659_, v_openDecls_4660_, v___x_4664_);
v___x_4666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4666_, 0, v_env_4657_);
lean_ctor_set(v___x_4666_, 1, v_openDecls_4660_);
v___x_4667_ = l_List_foldl___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__0(v_addOpenSimple_4644_, v___x_4666_, v_nss_4665_);
v_fst_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_fst_4668_);
v_snd_4669_ = lean_ctor_get(v___x_4667_, 1);
lean_inc(v_snd_4669_);
lean_dec_ref(v___x_4667_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 3, v_snd_4669_);
lean_ctor_set(v___x_4662_, 0, v_fst_4668_);
v___x_4671_ = v___x_4662_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_fst_4668_);
lean_ctor_set(v_reuseFailAlloc_4678_, 1, v_options_4658_);
lean_ctor_set(v_reuseFailAlloc_4678_, 2, v_currNamespace_4659_);
lean_ctor_set(v_reuseFailAlloc_4678_, 3, v_snd_4669_);
v___x_4671_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
lean_object* v___x_4673_; 
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 1, v___x_4671_);
v___x_4673_ = v___x_4655_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_toInputContext_4651_);
lean_ctor_set(v_reuseFailAlloc_4677_, 1, v___x_4671_);
lean_ctor_set(v_reuseFailAlloc_4677_, 2, v_toCacheableParserContext_4652_);
lean_ctor_set(v_reuseFailAlloc_4677_, 3, v_tokens_4653_);
v___x_4673_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
size_t v___x_4674_; size_t v___x_4675_; 
v___x_4674_ = ((size_t)1ULL);
v___x_4675_ = lean_usize_add(v_i_4646_, v___x_4674_);
v_i_4646_ = v___x_4675_;
v_b_4648_ = v___x_4673_;
goto _start;
}
}
}
}
}
else
{
return v_b_4648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1___boxed(lean_object* v_addOpenSimple_4681_, lean_object* v_as_4682_, lean_object* v_i_4683_, lean_object* v_stop_4684_, lean_object* v_b_4685_){
_start:
{
uint8_t v_addOpenSimple_boxed_4686_; size_t v_i_boxed_4687_; size_t v_stop_boxed_4688_; lean_object* v_res_4689_; 
v_addOpenSimple_boxed_4686_ = lean_unbox(v_addOpenSimple_4681_);
v_i_boxed_4687_ = lean_unbox_usize(v_i_4683_);
lean_dec(v_i_4683_);
v_stop_boxed_4688_ = lean_unbox_usize(v_stop_4684_);
lean_dec(v_stop_4684_);
v_res_4689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_boxed_4686_, v_as_4682_, v_i_boxed_4687_, v_stop_boxed_4688_, v_b_4685_);
lean_dec_ref(v_as_4682_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(lean_object* v___x_4690_, lean_object* v_ids_4691_, uint8_t v_addOpenSimple_4692_, lean_object* v_c_4693_){
_start:
{
lean_object* v___y_4695_; lean_object* v___x_4715_; lean_object* v___x_4716_; uint8_t v___x_4717_; 
v___x_4715_ = lean_unsigned_to_nat(0u);
v___x_4716_ = lean_array_get_size(v_ids_4691_);
v___x_4717_ = lean_nat_dec_lt(v___x_4715_, v___x_4716_);
if (v___x_4717_ == 0)
{
v___y_4695_ = v_c_4693_;
goto v___jp_4694_;
}
else
{
uint8_t v___x_4718_; 
v___x_4718_ = lean_nat_dec_le(v___x_4716_, v___x_4716_);
if (v___x_4718_ == 0)
{
if (v___x_4717_ == 0)
{
v___y_4695_ = v_c_4693_;
goto v___jp_4694_;
}
else
{
size_t v___x_4719_; size_t v___x_4720_; lean_object* v___x_4721_; 
v___x_4719_ = ((size_t)0ULL);
v___x_4720_ = lean_usize_of_nat(v___x_4716_);
v___x_4721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4692_, v_ids_4691_, v___x_4719_, v___x_4720_, v_c_4693_);
v___y_4695_ = v___x_4721_;
goto v___jp_4694_;
}
}
else
{
size_t v___x_4722_; size_t v___x_4723_; lean_object* v___x_4724_; 
v___x_4722_ = ((size_t)0ULL);
v___x_4723_ = lean_usize_of_nat(v___x_4716_);
v___x_4724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces_spec__1(v_addOpenSimple_4692_, v_ids_4691_, v___x_4722_, v___x_4723_, v_c_4693_);
v___y_4695_ = v___x_4724_;
goto v___jp_4694_;
}
}
v___jp_4694_:
{
lean_object* v_toParserModuleContext_4696_; lean_object* v_toInputContext_4697_; lean_object* v_toCacheableParserContext_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4713_; 
v_toParserModuleContext_4696_ = lean_ctor_get(v___y_4695_, 1);
v_toInputContext_4697_ = lean_ctor_get(v___y_4695_, 0);
v_toCacheableParserContext_4698_ = lean_ctor_get(v___y_4695_, 2);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___y_4695_);
if (v_isSharedCheck_4713_ == 0)
{
lean_object* v_unused_4714_; 
v_unused_4714_ = lean_ctor_get(v___y_4695_, 3);
lean_dec(v_unused_4714_);
v___x_4700_ = v___y_4695_;
v_isShared_4701_ = v_isSharedCheck_4713_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_toCacheableParserContext_4698_);
lean_inc(v_toParserModuleContext_4696_);
lean_inc(v_toInputContext_4697_);
lean_dec(v___y_4695_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4713_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v_env_4702_; lean_object* v___x_4703_; lean_object* v_ext_4704_; lean_object* v_toEnvExtension_4705_; lean_object* v_asyncMode_4706_; uint8_t v___x_4707_; lean_object* v___x_4708_; lean_object* v_tokens_4709_; lean_object* v___x_4711_; 
v_env_4702_ = lean_ctor_get(v_toParserModuleContext_4696_, 0);
v___x_4703_ = l_Lean_Parser_parserExtension;
v_ext_4704_ = lean_ctor_get(v___x_4703_, 1);
v_toEnvExtension_4705_ = lean_ctor_get(v_ext_4704_, 0);
v_asyncMode_4706_ = lean_ctor_get(v_toEnvExtension_4705_, 2);
v___x_4707_ = 0;
lean_inc_ref(v_env_4702_);
v___x_4708_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4690_, v___x_4703_, v_env_4702_, v_asyncMode_4706_, v___x_4707_);
v_tokens_4709_ = lean_ctor_get(v___x_4708_, 0);
lean_inc_ref(v_tokens_4709_);
lean_dec(v___x_4708_);
if (v_isShared_4701_ == 0)
{
lean_ctor_set(v___x_4700_, 3, v_tokens_4709_);
v___x_4711_ = v___x_4700_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_toInputContext_4697_);
lean_ctor_set(v_reuseFailAlloc_4712_, 1, v_toParserModuleContext_4696_);
lean_ctor_set(v_reuseFailAlloc_4712_, 2, v_toCacheableParserContext_4698_);
lean_ctor_set(v_reuseFailAlloc_4712_, 3, v_tokens_4709_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed(lean_object* v___x_4725_, lean_object* v_ids_4726_, lean_object* v_addOpenSimple_4727_, lean_object* v_c_4728_){
_start:
{
uint8_t v_addOpenSimple_boxed_4729_; lean_object* v_res_4730_; 
v_addOpenSimple_boxed_4729_ = lean_unbox(v_addOpenSimple_4727_);
v_res_4730_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0(v___x_4725_, v_ids_4726_, v_addOpenSimple_boxed_4729_, v_c_4728_);
lean_dec_ref(v_ids_4726_);
lean_dec_ref(v___x_4725_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(lean_object* v_ids_4731_, uint8_t v_addOpenSimple_4732_, lean_object* v_p_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___f_4738_; lean_object* v___x_4739_; 
v___x_4736_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_4737_ = lean_box(v_addOpenSimple_4732_);
v___f_4738_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4738_, 0, v___x_4736_);
lean_closure_set(v___f_4738_, 1, v_ids_4731_);
lean_closure_set(v___f_4738_, 2, v___x_4737_);
v___x_4739_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_4738_, v_p_4733_, v_a_4734_, v_a_4735_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces___boxed(lean_object* v_ids_4740_, lean_object* v_addOpenSimple_4741_, lean_object* v_p_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
uint8_t v_addOpenSimple_boxed_4745_; lean_object* v_res_4746_; 
v_addOpenSimple_boxed_4745_ = lean_unbox(v_addOpenSimple_4741_);
v_res_4746_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v_ids_4740_, v_addOpenSimple_boxed_4745_, v_p_4742_, v_a_4743_, v_a_4744_);
return v_res_4746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(size_t v_sz_4747_, size_t v_i_4748_, lean_object* v_bs_4749_){
_start:
{
uint8_t v___x_4750_; 
v___x_4750_ = lean_usize_dec_lt(v_i_4748_, v_sz_4747_);
if (v___x_4750_ == 0)
{
return v_bs_4749_;
}
else
{
lean_object* v_v_4751_; lean_object* v___x_4752_; lean_object* v_bs_x27_4753_; lean_object* v___x_4754_; size_t v___x_4755_; size_t v___x_4756_; lean_object* v___x_4757_; 
v_v_4751_ = lean_array_uget(v_bs_4749_, v_i_4748_);
v___x_4752_ = lean_unsigned_to_nat(0u);
v_bs_x27_4753_ = lean_array_uset(v_bs_4749_, v_i_4748_, v___x_4752_);
v___x_4754_ = l_Lean_Syntax_getId(v_v_4751_);
lean_dec(v_v_4751_);
v___x_4755_ = ((size_t)1ULL);
v___x_4756_ = lean_usize_add(v_i_4748_, v___x_4755_);
v___x_4757_ = lean_array_uset(v_bs_x27_4753_, v_i_4748_, v___x_4754_);
v_i_4748_ = v___x_4756_;
v_bs_4749_ = v___x_4757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0___boxed(lean_object* v_sz_4759_, lean_object* v_i_4760_, lean_object* v_bs_4761_){
_start:
{
size_t v_sz_boxed_4762_; size_t v_i_boxed_4763_; lean_object* v_res_4764_; 
v_sz_boxed_4762_ = lean_unbox_usize(v_sz_4759_);
lean_dec(v_sz_4759_);
v_i_boxed_4763_ = lean_unbox_usize(v_i_4760_);
lean_dec(v_i_4760_);
v_res_4764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_boxed_4762_, v_i_boxed_4763_, v_bs_4761_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFnCore(lean_object* v_openDeclStx_4778_, lean_object* v_p_4779_, lean_object* v_c_4780_, lean_object* v_s_4781_){
_start:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; uint8_t v___x_4784_; 
lean_inc(v_openDeclStx_4778_);
v___x_4782_ = l_Lean_Syntax_getKind(v_openDeclStx_4778_);
v___x_4783_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__2));
v___x_4784_ = lean_name_eq(v___x_4782_, v___x_4783_);
if (v___x_4784_ == 0)
{
lean_object* v___x_4785_; uint8_t v___x_4786_; 
v___x_4785_ = ((lean_object*)(l_Lean_Parser_withOpenDeclFnCore___closed__4));
v___x_4786_ = lean_name_eq(v___x_4782_, v___x_4785_);
lean_dec(v___x_4782_);
if (v___x_4786_ == 0)
{
lean_object* v___x_4787_; 
lean_dec(v_openDeclStx_4778_);
v___x_4787_ = lean_apply_2(v_p_4779_, v_c_4780_, v_s_4781_);
return v___x_4787_;
}
else
{
lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; size_t v_sz_4791_; size_t v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4788_ = lean_unsigned_to_nat(1u);
v___x_4789_ = l_Lean_Syntax_getArg(v_openDeclStx_4778_, v___x_4788_);
lean_dec(v_openDeclStx_4778_);
v___x_4790_ = l_Lean_Syntax_getArgs(v___x_4789_);
lean_dec(v___x_4789_);
v_sz_4791_ = lean_array_size(v___x_4790_);
v___x_4792_ = ((size_t)0ULL);
v___x_4793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4791_, v___x_4792_, v___x_4790_);
v___x_4794_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4793_, v___x_4784_, v_p_4779_, v_c_4780_, v_s_4781_);
return v___x_4794_;
}
}
else
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; size_t v_sz_4798_; size_t v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
lean_dec(v___x_4782_);
v___x_4795_ = lean_unsigned_to_nat(0u);
v___x_4796_ = l_Lean_Syntax_getArg(v_openDeclStx_4778_, v___x_4795_);
lean_dec(v_openDeclStx_4778_);
v___x_4797_ = l_Lean_Syntax_getArgs(v___x_4796_);
lean_dec(v___x_4796_);
v_sz_4798_ = lean_array_size(v___x_4797_);
v___x_4799_ = ((size_t)0ULL);
v___x_4800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_withOpenDeclFnCore_spec__0(v_sz_4798_, v___x_4799_, v___x_4797_);
v___x_4801_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withNamespaces(v___x_4800_, v___x_4784_, v_p_4779_, v_c_4780_, v_s_4781_);
return v___x_4801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenFn(lean_object* v_p_4808_, lean_object* v_c_4809_, lean_object* v_s_4810_){
_start:
{
lean_object* v_stxStack_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; uint8_t v___x_4814_; 
v_stxStack_4811_ = lean_ctor_get(v_s_4810_, 0);
v___x_4812_ = lean_unsigned_to_nat(0u);
v___x_4813_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4811_);
v___x_4814_ = lean_nat_dec_lt(v___x_4812_, v___x_4813_);
lean_dec(v___x_4813_);
if (v___x_4814_ == 0)
{
lean_object* v___x_4815_; 
v___x_4815_ = lean_apply_2(v_p_4808_, v_c_4809_, v_s_4810_);
return v___x_4815_;
}
else
{
lean_object* v_stx_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; uint8_t v___x_4819_; 
v_stx_4816_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4811_);
lean_inc(v_stx_4816_);
v___x_4817_ = l_Lean_Syntax_getKind(v_stx_4816_);
v___x_4818_ = ((lean_object*)(l_Lean_Parser_withOpenFn___closed__1));
v___x_4819_ = lean_name_eq(v___x_4817_, v___x_4818_);
lean_dec(v___x_4817_);
if (v___x_4819_ == 0)
{
lean_object* v___x_4820_; 
lean_dec(v_stx_4816_);
v___x_4820_ = lean_apply_2(v_p_4808_, v_c_4809_, v_s_4810_);
return v___x_4820_;
}
else
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4821_ = lean_unsigned_to_nat(1u);
v___x_4822_ = l_Lean_Syntax_getArg(v_stx_4816_, v___x_4821_);
lean_dec(v_stx_4816_);
v___x_4823_ = l_Lean_Parser_withOpenDeclFnCore(v___x_4822_, v_p_4808_, v_c_4809_, v_s_4810_);
return v___x_4823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpen(lean_object* v_p_4824_){
_start:
{
lean_object* v_info_4825_; lean_object* v_fn_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4834_; 
v_info_4825_ = lean_ctor_get(v_p_4824_, 0);
v_fn_4826_ = lean_ctor_get(v_p_4824_, 1);
v_isSharedCheck_4834_ = !lean_is_exclusive(v_p_4824_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4828_ = v_p_4824_;
v_isShared_4829_ = v_isSharedCheck_4834_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_fn_4826_);
lean_inc(v_info_4825_);
lean_dec(v_p_4824_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4834_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4830_; lean_object* v___x_4832_; 
v___x_4830_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenFn), 3, 1);
lean_closure_set(v___x_4830_, 0, v_fn_4826_);
if (v_isShared_4829_ == 0)
{
lean_ctor_set(v___x_4828_, 1, v___x_4830_);
v___x_4832_ = v___x_4828_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_info_4825_);
lean_ctor_set(v_reuseFailAlloc_4833_, 1, v___x_4830_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDeclFn(lean_object* v_p_4835_, lean_object* v_c_4836_, lean_object* v_s_4837_){
_start:
{
lean_object* v_stxStack_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; uint8_t v___x_4841_; 
v_stxStack_4838_ = lean_ctor_get(v_s_4837_, 0);
v___x_4839_ = lean_unsigned_to_nat(0u);
v___x_4840_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4838_);
v___x_4841_ = lean_nat_dec_lt(v___x_4839_, v___x_4840_);
lean_dec(v___x_4840_);
if (v___x_4841_ == 0)
{
lean_object* v___x_4842_; 
v___x_4842_ = lean_apply_2(v_p_4835_, v_c_4836_, v_s_4837_);
return v___x_4842_;
}
else
{
lean_object* v_stx_4843_; lean_object* v___x_4844_; 
v_stx_4843_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4838_);
v___x_4844_ = l_Lean_Parser_withOpenDeclFnCore(v_stx_4843_, v_p_4835_, v_c_4836_, v_s_4837_);
return v___x_4844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withOpenDecl(lean_object* v_p_4845_){
_start:
{
lean_object* v_info_4846_; lean_object* v_fn_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4855_; 
v_info_4846_ = lean_ctor_get(v_p_4845_, 0);
v_fn_4847_ = lean_ctor_get(v_p_4845_, 1);
v_isSharedCheck_4855_ = !lean_is_exclusive(v_p_4845_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4849_ = v_p_4845_;
v_isShared_4850_ = v_isSharedCheck_4855_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_fn_4847_);
lean_inc(v_info_4846_);
lean_dec(v_p_4845_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4855_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4851_; lean_object* v___x_4853_; 
v___x_4851_ = lean_alloc_closure((void*)(l_Lean_Parser_withOpenDeclFn), 3, 1);
lean_closure_set(v___x_4851_, 0, v_fn_4847_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 1, v___x_4851_);
v___x_4853_ = v___x_4849_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_info_4846_);
lean_ctor_set(v_reuseFailAlloc_4854_, 1, v___x_4851_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(lean_object* v_val_4862_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l_Lean_Syntax_isStrLit_x3f(v_val_4862_);
if (lean_obj_tag(v___x_4870_) == 1)
{
lean_object* v_val_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4879_; 
v_val_4871_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4873_ = v___x_4870_;
v_isShared_4874_ = v_isSharedCheck_4879_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_val_4871_);
lean_dec(v___x_4870_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4879_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4875_; lean_object* v___x_4877_; 
v___x_4875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4875_, 0, v_val_4871_);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 0, v___x_4875_);
v___x_4877_ = v___x_4873_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
else
{
lean_object* v___x_4880_; 
lean_dec(v___x_4870_);
v___x_4880_ = l_Lean_Syntax_isNatLit_x3f(v_val_4862_);
if (lean_obj_tag(v___x_4880_) == 1)
{
lean_object* v_val_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4889_; 
v_val_4881_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4883_ = v___x_4880_;
v_isShared_4884_ = v_isSharedCheck_4889_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_val_4881_);
lean_dec(v___x_4880_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4889_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4885_; lean_object* v___x_4887_; 
v___x_4885_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4885_, 0, v_val_4881_);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 0, v___x_4885_);
v___x_4887_ = v___x_4883_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4885_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
else
{
lean_dec(v___x_4880_);
if (lean_obj_tag(v_val_4862_) == 2)
{
lean_object* v_val_4890_; lean_object* v___x_4891_; uint8_t v___x_4892_; 
v_val_4890_ = lean_ctor_get(v_val_4862_, 1);
v___x_4891_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__3));
v___x_4892_ = lean_string_dec_eq(v_val_4890_, v___x_4891_);
if (v___x_4892_ == 0)
{
goto v___jp_4863_;
}
else
{
lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4893_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4893_, 0, v___x_4892_);
v___x_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4893_);
return v___x_4894_;
}
}
else
{
goto v___jp_4863_;
}
}
}
v___jp_4863_:
{
if (lean_obj_tag(v_val_4862_) == 2)
{
lean_object* v_val_4864_; lean_object* v___x_4865_; uint8_t v___x_4866_; 
v_val_4864_ = lean_ctor_get(v_val_4862_, 1);
v___x_4865_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__0));
v___x_4866_ = lean_string_dec_eq(v_val_4864_, v___x_4865_);
if (v___x_4866_ == 0)
{
lean_object* v___x_4867_; 
v___x_4867_ = lean_box(0);
return v___x_4867_;
}
else
{
lean_object* v___x_4868_; 
v___x_4868_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___closed__2));
return v___x_4868_;
}
}
else
{
lean_object* v___x_4869_; 
v___x_4869_ = lean_box(0);
return v___x_4869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f___boxed(lean_object* v_val_4895_){
_start:
{
lean_object* v_res_4896_; 
v_res_4896_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_val_4895_);
lean_dec(v_val_4895_);
return v_res_4896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(lean_object* v_nameStx_4897_, lean_object* v_v_4898_, lean_object* v_c_4899_){
_start:
{
lean_object* v_toParserModuleContext_4900_; lean_object* v_toInputContext_4901_; lean_object* v_toCacheableParserContext_4902_; lean_object* v_tokens_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4940_; 
v_toParserModuleContext_4900_ = lean_ctor_get(v_c_4899_, 1);
v_toInputContext_4901_ = lean_ctor_get(v_c_4899_, 0);
v_toCacheableParserContext_4902_ = lean_ctor_get(v_c_4899_, 2);
v_tokens_4903_ = lean_ctor_get(v_c_4899_, 3);
v_isSharedCheck_4940_ = !lean_is_exclusive(v_c_4899_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4905_ = v_c_4899_;
v_isShared_4906_ = v_isSharedCheck_4940_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_tokens_4903_);
lean_inc(v_toCacheableParserContext_4902_);
lean_inc(v_toParserModuleContext_4900_);
lean_inc(v_toInputContext_4901_);
lean_dec(v_c_4899_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4940_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v_env_4907_; lean_object* v_options_4908_; lean_object* v_currNamespace_4909_; lean_object* v_openDecls_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4939_; 
v_env_4907_ = lean_ctor_get(v_toParserModuleContext_4900_, 0);
v_options_4908_ = lean_ctor_get(v_toParserModuleContext_4900_, 1);
v_currNamespace_4909_ = lean_ctor_get(v_toParserModuleContext_4900_, 2);
v_openDecls_4910_ = lean_ctor_get(v_toParserModuleContext_4900_, 3);
v_isSharedCheck_4939_ = !lean_is_exclusive(v_toParserModuleContext_4900_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4912_ = v_toParserModuleContext_4900_;
v_isShared_4913_ = v_isSharedCheck_4939_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_openDecls_4910_);
lean_inc(v_currNamespace_4909_);
lean_inc(v_options_4908_);
lean_inc(v_env_4907_);
lean_dec(v_toParserModuleContext_4900_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4939_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___y_4915_; lean_object* v_map_4922_; uint8_t v_hasTrace_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4938_; 
v_map_4922_ = lean_ctor_get(v_options_4908_, 0);
v_hasTrace_4923_ = lean_ctor_get_uint8(v_options_4908_, sizeof(void*)*1);
v_isSharedCheck_4938_ = !lean_is_exclusive(v_options_4908_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4925_ = v_options_4908_;
v_isShared_4926_ = v_isSharedCheck_4938_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_map_4922_);
lean_dec(v_options_4908_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4938_;
goto v_resetjp_4924_;
}
v___jp_4914_:
{
lean_object* v___x_4917_; 
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 1, v___y_4915_);
v___x_4917_ = v___x_4912_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_env_4907_);
lean_ctor_set(v_reuseFailAlloc_4921_, 1, v___y_4915_);
lean_ctor_set(v_reuseFailAlloc_4921_, 2, v_currNamespace_4909_);
lean_ctor_set(v_reuseFailAlloc_4921_, 3, v_openDecls_4910_);
v___x_4917_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
lean_object* v___x_4919_; 
if (v_isShared_4906_ == 0)
{
lean_ctor_set(v___x_4905_, 1, v___x_4917_);
v___x_4919_ = v___x_4905_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_toInputContext_4901_);
lean_ctor_set(v_reuseFailAlloc_4920_, 1, v___x_4917_);
lean_ctor_set(v_reuseFailAlloc_4920_, 2, v_toCacheableParserContext_4902_);
lean_ctor_set(v_reuseFailAlloc_4920_, 3, v_tokens_4903_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
v_resetjp_4924_:
{
lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4927_ = l_Lean_Syntax_getId(v_nameStx_4897_);
v___x_4928_ = l_Lean_Name_eraseMacroScopes(v___x_4927_);
lean_dec(v___x_4927_);
lean_inc(v___x_4928_);
v___x_4929_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_4928_, v_v_4898_, v_map_4922_);
if (v_hasTrace_4923_ == 0)
{
lean_object* v___x_4930_; uint8_t v___x_4931_; lean_object* v___x_4933_; 
v___x_4930_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0___closed__1));
v___x_4931_ = l_Lean_Name_isPrefixOf(v___x_4930_, v___x_4928_);
lean_dec(v___x_4928_);
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 0, v___x_4929_);
v___x_4933_ = v___x_4925_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4929_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
lean_ctor_set_uint8(v___x_4933_, sizeof(void*)*1, v___x_4931_);
v___y_4915_ = v___x_4933_;
goto v___jp_4914_;
}
}
else
{
lean_object* v___x_4936_; 
lean_dec(v___x_4928_);
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 0, v___x_4929_);
v___x_4936_ = v___x_4925_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4929_);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, sizeof(void*)*1, v_hasTrace_4923_);
v___x_4936_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
v___y_4915_ = v___x_4936_;
goto v___jp_4914_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed(lean_object* v_nameStx_4941_, lean_object* v_v_4942_, lean_object* v_c_4943_){
_start:
{
lean_object* v_res_4944_; 
v_res_4944_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption(v_nameStx_4941_, v_v_4942_, v_c_4943_);
lean_dec(v_nameStx_4941_);
return v_res_4944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(lean_object* v_nameStx_4945_, lean_object* v_valStx_4946_, lean_object* v_p_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_){
_start:
{
lean_object* v___x_4950_; 
v___x_4950_ = l___private_Lean_Parser_Extension_0__Lean_Parser_optionValueToDataValue_x3f(v_valStx_4946_);
if (lean_obj_tag(v___x_4950_) == 0)
{
lean_object* v___x_4951_; 
lean_dec(v_nameStx_4945_);
v___x_4951_ = lean_apply_2(v_p_4947_, v_a_4948_, v_a_4949_);
return v___x_4951_;
}
else
{
lean_object* v_val_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v_val_4952_ = lean_ctor_get(v___x_4950_, 0);
lean_inc(v_val_4952_);
lean_dec_ref_known(v___x_4950_, 1);
v___x_4953_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore_insertOption___boxed), 3, 2);
lean_closure_set(v___x_4953_, 0, v_nameStx_4945_);
lean_closure_set(v___x_4953_, 1, v_val_4952_);
v___x_4954_ = l_Lean_Parser_adaptUncacheableContextFn(v___x_4953_, v_p_4947_, v_a_4948_, v_a_4949_);
return v___x_4954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore___boxed(lean_object* v_nameStx_4955_, lean_object* v_valStx_4956_, lean_object* v_p_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_){
_start:
{
lean_object* v_res_4960_; 
v_res_4960_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v_nameStx_4955_, v_valStx_4956_, v_p_4957_, v_a_4958_, v_a_4959_);
lean_dec(v_valStx_4956_);
return v_res_4960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionFn(lean_object* v_p_4967_, lean_object* v_c_4968_, lean_object* v_s_4969_){
_start:
{
lean_object* v_stxStack_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; uint8_t v___x_4973_; 
v_stxStack_4970_ = lean_ctor_get(v_s_4969_, 0);
v___x_4971_ = lean_unsigned_to_nat(0u);
v___x_4972_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4970_);
v___x_4973_ = lean_nat_dec_lt(v___x_4971_, v___x_4972_);
lean_dec(v___x_4972_);
if (v___x_4973_ == 0)
{
lean_object* v___x_4974_; 
v___x_4974_ = lean_apply_2(v_p_4967_, v_c_4968_, v_s_4969_);
return v___x_4974_;
}
else
{
lean_object* v_stx_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; uint8_t v___x_4978_; 
v_stx_4975_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4970_);
lean_inc(v_stx_4975_);
v___x_4976_ = l_Lean_Syntax_getKind(v_stx_4975_);
v___x_4977_ = ((lean_object*)(l_Lean_Parser_withSetOptionFn___closed__1));
v___x_4978_ = lean_name_eq(v___x_4976_, v___x_4977_);
lean_dec(v___x_4976_);
if (v___x_4978_ == 0)
{
lean_object* v___x_4979_; 
lean_dec(v_stx_4975_);
v___x_4979_ = lean_apply_2(v_p_4967_, v_c_4968_, v_s_4969_);
return v___x_4979_;
}
else
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4980_ = lean_unsigned_to_nat(1u);
v___x_4981_ = l_Lean_Syntax_getArg(v_stx_4975_, v___x_4980_);
v___x_4982_ = lean_unsigned_to_nat(3u);
v___x_4983_ = l_Lean_Syntax_getArg(v_stx_4975_, v___x_4982_);
lean_dec(v_stx_4975_);
v___x_4984_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_4981_, v___x_4983_, v_p_4967_, v_c_4968_, v_s_4969_);
lean_dec(v___x_4983_);
return v___x_4984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOption(lean_object* v_p_4985_){
_start:
{
lean_object* v_info_4986_; lean_object* v_fn_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4995_; 
v_info_4986_ = lean_ctor_get(v_p_4985_, 0);
v_fn_4987_ = lean_ctor_get(v_p_4985_, 1);
v_isSharedCheck_4995_ = !lean_is_exclusive(v_p_4985_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4989_ = v_p_4985_;
v_isShared_4990_ = v_isSharedCheck_4995_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_fn_4987_);
lean_inc(v_info_4986_);
lean_dec(v_p_4985_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4995_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4991_; lean_object* v___x_4993_; 
v___x_4991_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionFn), 3, 1);
lean_closure_set(v___x_4991_, 0, v_fn_4987_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 1, v___x_4991_);
v___x_4993_ = v___x_4989_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_info_4986_);
lean_ctor_set(v_reuseFailAlloc_4994_, 1, v___x_4991_);
v___x_4993_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
return v___x_4993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValueFn(lean_object* v_p_4996_, lean_object* v_c_4997_, lean_object* v_s_4998_){
_start:
{
lean_object* v_stxStack_4999_; lean_object* v_sz_5000_; lean_object* v___x_5001_; uint8_t v___x_5002_; 
v_stxStack_4999_ = lean_ctor_get(v_s_4998_, 0);
v_sz_5000_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_4999_);
v___x_5001_ = lean_unsigned_to_nat(3u);
v___x_5002_ = lean_nat_dec_le(v___x_5001_, v_sz_5000_);
if (v___x_5002_ == 0)
{
lean_object* v___x_5003_; 
lean_dec(v_sz_5000_);
v___x_5003_ = lean_apply_2(v_p_4996_, v_c_4997_, v_s_4998_);
return v___x_5003_;
}
else
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_5004_ = lean_nat_sub(v_sz_5000_, v___x_5001_);
lean_dec(v_sz_5000_);
v___x_5005_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_4999_, v___x_5004_);
lean_dec(v___x_5004_);
v___x_5006_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4999_);
v___x_5007_ = l___private_Lean_Parser_Extension_0__Lean_Parser_withSetOptionValueFnCore(v___x_5005_, v___x_5006_, v_p_4996_, v_c_4997_, v_s_4998_);
lean_dec(v___x_5006_);
return v___x_5007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withSetOptionValue(lean_object* v_p_5008_){
_start:
{
lean_object* v_info_5009_; lean_object* v_fn_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5018_; 
v_info_5009_ = lean_ctor_get(v_p_5008_, 0);
v_fn_5010_ = lean_ctor_get(v_p_5008_, 1);
v_isSharedCheck_5018_ = !lean_is_exclusive(v_p_5008_);
if (v_isSharedCheck_5018_ == 0)
{
v___x_5012_ = v_p_5008_;
v_isShared_5013_ = v_isSharedCheck_5018_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_fn_5010_);
lean_inc(v_info_5009_);
lean_dec(v_p_5008_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5018_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5014_; lean_object* v___x_5016_; 
v___x_5014_ = lean_alloc_closure((void*)(l_Lean_Parser_withSetOptionValueFn), 3, 1);
lean_closure_set(v___x_5014_, 0, v_fn_5010_);
if (v_isShared_5013_ == 0)
{
lean_ctor_set(v___x_5012_, 1, v___x_5014_);
v___x_5016_ = v___x_5012_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v_info_5009_);
lean_ctor_set(v_reuseFailAlloc_5017_, 1, v___x_5014_);
v___x_5016_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
return v___x_5016_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(lean_object* v___x_5019_){
_start:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5021_ = lean_st_ref_get(v___x_5019_);
v___x_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5021_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed(lean_object* v___x_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v_res_5025_; 
v_res_5025_ = l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(v___x_5023_);
lean_dec(v___x_5023_);
return v_res_5025_;
}
}
static lean_object* _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5026_; lean_object* v___f_5027_; 
v___x_5026_ = l_Lean_Parser_parserAliasesRef;
v___f_5027_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5027_, 0, v___x_5026_);
return v___f_5027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_initFn_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; uint8_t v___x_5038_; lean_object* v___x_5039_; 
v___f_5034_ = lean_obj_once(&l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_, &l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_);
v___x_5035_ = lean_box(0);
v___x_5036_ = lean_box(2);
v___x_5037_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Extension_1918044636____hygCtx___hyg_2_));
v___x_5038_ = 0;
v___x_5039_ = l_Lean_registerEnvExtension___redArg(v___f_5034_, v___x_5035_, v___x_5036_, v___x_5037_, v___x_5038_, v___x_5038_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___impl(lean_object* v_x_5042_){
_start:
{
lean_object* v___x_5043_; 
v___x_5043_ = lean_obj_tag_nat(v_x_5042_);
return v___x_5043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorIdx___impl___boxed(lean_object* v_x_5044_){
_start:
{
lean_object* v_res_5045_; 
v_res_5045_ = l_Lean_Parser_ParserResolution_ctorIdx___impl(v_x_5044_);
lean_dec_ref(v_x_5044_);
return v_res_5045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___redArg(lean_object* v_t_5046_, lean_object* v_k_5047_){
_start:
{
switch(lean_obj_tag(v_t_5046_))
{
case 0:
{
lean_object* v_cat_5048_; lean_object* v___x_5049_; 
v_cat_5048_ = lean_ctor_get(v_t_5046_, 0);
lean_inc(v_cat_5048_);
lean_dec_ref_known(v_t_5046_, 1);
v___x_5049_ = lean_apply_1(v_k_5047_, v_cat_5048_);
return v___x_5049_;
}
case 1:
{
lean_object* v_decl_5050_; uint8_t v_isDescr_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v_decl_5050_ = lean_ctor_get(v_t_5046_, 0);
lean_inc(v_decl_5050_);
v_isDescr_5051_ = lean_ctor_get_uint8(v_t_5046_, sizeof(void*)*1);
lean_dec_ref_known(v_t_5046_, 1);
v___x_5052_ = lean_box(v_isDescr_5051_);
v___x_5053_ = lean_apply_2(v_k_5047_, v_decl_5050_, v___x_5052_);
return v___x_5053_;
}
default: 
{
lean_object* v_p_5054_; lean_object* v___x_5055_; 
v_p_5054_ = lean_ctor_get(v_t_5046_, 0);
lean_inc_ref(v_p_5054_);
lean_dec_ref_known(v_t_5046_, 1);
v___x_5055_ = lean_apply_1(v_k_5047_, v_p_5054_);
return v___x_5055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim(lean_object* v_motive_5056_, lean_object* v_ctorIdx_5057_, lean_object* v_t_5058_, lean_object* v_h_5059_, lean_object* v_k_5060_){
_start:
{
lean_object* v___x_5061_; 
v___x_5061_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5058_, v_k_5060_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_ctorElim___boxed(lean_object* v_motive_5062_, lean_object* v_ctorIdx_5063_, lean_object* v_t_5064_, lean_object* v_h_5065_, lean_object* v_k_5066_){
_start:
{
lean_object* v_res_5067_; 
v_res_5067_ = l_Lean_Parser_ParserResolution_ctorElim(v_motive_5062_, v_ctorIdx_5063_, v_t_5064_, v_h_5065_, v_k_5066_);
lean_dec(v_ctorIdx_5063_);
return v_res_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim___redArg(lean_object* v_t_5068_, lean_object* v_category_5069_){
_start:
{
lean_object* v___x_5070_; 
v___x_5070_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5068_, v_category_5069_);
return v___x_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_category_elim(lean_object* v_motive_5071_, lean_object* v_t_5072_, lean_object* v_h_5073_, lean_object* v_category_5074_){
_start:
{
lean_object* v___x_5075_; 
v___x_5075_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5072_, v_category_5074_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim___redArg(lean_object* v_t_5076_, lean_object* v_parser_5077_){
_start:
{
lean_object* v___x_5078_; 
v___x_5078_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5076_, v_parser_5077_);
return v___x_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_parser_elim(lean_object* v_motive_5079_, lean_object* v_t_5080_, lean_object* v_h_5081_, lean_object* v_parser_5082_){
_start:
{
lean_object* v___x_5083_; 
v___x_5083_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5080_, v_parser_5082_);
return v___x_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim___redArg(lean_object* v_t_5084_, lean_object* v_alias_5085_){
_start:
{
lean_object* v___x_5086_; 
v___x_5086_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5084_, v_alias_5085_);
return v___x_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserResolution_alias_elim(lean_object* v_motive_5087_, lean_object* v_t_5088_, lean_object* v_h_5089_, lean_object* v_alias_5090_){
_start:
{
lean_object* v___x_5091_; 
v___x_5091_ = l_Lean_Parser_ParserResolution_ctorElim___redArg(v_t_5088_, v_alias_5090_);
return v___x_5091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(lean_object* v_env_5095_, lean_object* v_name_5096_){
_start:
{
uint8_t v___x_5097_; lean_object* v___x_5098_; 
v___x_5097_ = 0;
v___x_5098_ = l_Lean_Environment_find_x3f(v_env_5095_, v_name_5096_, v___x_5097_);
if (lean_obj_tag(v___x_5098_) == 0)
{
lean_object* v___x_5099_; 
v___x_5099_ = lean_box(0);
return v___x_5099_;
}
else
{
lean_object* v_val_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5147_; 
v_val_5100_ = lean_ctor_get(v___x_5098_, 0);
v_isSharedCheck_5147_ = !lean_is_exclusive(v___x_5098_);
if (v_isSharedCheck_5147_ == 0)
{
v___x_5102_ = v___x_5098_;
v_isShared_5103_ = v_isSharedCheck_5147_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_val_5100_);
lean_dec(v___x_5098_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5147_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5104_; 
v___x_5104_ = l_Lean_ConstantInfo_type(v_val_5100_);
lean_dec(v_val_5100_);
if (lean_obj_tag(v___x_5104_) == 4)
{
lean_object* v_declName_5105_; 
v_declName_5105_ = lean_ctor_get(v___x_5104_, 0);
lean_inc(v_declName_5105_);
lean_dec_ref_known(v___x_5104_, 2);
if (lean_obj_tag(v_declName_5105_) == 1)
{
lean_object* v_pre_5106_; 
v_pre_5106_ = lean_ctor_get(v_declName_5105_, 0);
lean_inc(v_pre_5106_);
if (lean_obj_tag(v_pre_5106_) == 1)
{
lean_object* v_pre_5107_; 
v_pre_5107_ = lean_ctor_get(v_pre_5106_, 0);
switch(lean_obj_tag(v_pre_5107_))
{
case 1:
{
lean_object* v_pre_5108_; 
lean_inc_ref(v_pre_5107_);
lean_del_object(v___x_5102_);
v_pre_5108_ = lean_ctor_get(v_pre_5107_, 0);
if (lean_obj_tag(v_pre_5108_) == 0)
{
lean_object* v_str_5109_; lean_object* v_str_5110_; lean_object* v_str_5111_; lean_object* v___x_5112_; uint8_t v___x_5113_; 
v_str_5109_ = lean_ctor_get(v_declName_5105_, 1);
lean_inc_ref(v_str_5109_);
lean_dec_ref_known(v_declName_5105_, 2);
v_str_5110_ = lean_ctor_get(v_pre_5106_, 1);
lean_inc_ref(v_str_5110_);
lean_dec_ref_known(v_pre_5106_, 2);
v_str_5111_ = lean_ctor_get(v_pre_5107_, 1);
lean_inc_ref(v_str_5111_);
lean_dec_ref_known(v_pre_5107_, 2);
v___x_5112_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5113_ = lean_string_dec_eq(v_str_5111_, v___x_5112_);
lean_dec_ref(v_str_5111_);
if (v___x_5113_ == 0)
{
lean_object* v___x_5114_; 
lean_dec_ref(v_str_5110_);
lean_dec_ref(v_str_5109_);
v___x_5114_ = lean_box(0);
return v___x_5114_;
}
else
{
lean_object* v___x_5115_; uint8_t v___x_5116_; 
v___x_5115_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__4));
v___x_5116_ = lean_string_dec_eq(v_str_5110_, v___x_5115_);
lean_dec_ref(v_str_5110_);
if (v___x_5116_ == 0)
{
lean_object* v___x_5117_; 
lean_dec_ref(v_str_5109_);
v___x_5117_ = lean_box(0);
return v___x_5117_;
}
else
{
uint8_t v___x_5118_; 
v___x_5118_ = lean_string_dec_eq(v_str_5109_, v___x_5115_);
if (v___x_5118_ == 0)
{
lean_object* v___x_5119_; uint8_t v___x_5120_; 
v___x_5119_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__5));
v___x_5120_ = lean_string_dec_eq(v_str_5109_, v___x_5119_);
lean_dec_ref(v_str_5109_);
if (v___x_5120_ == 0)
{
lean_object* v___x_5121_; 
v___x_5121_ = lean_box(0);
return v___x_5121_;
}
else
{
lean_object* v___x_5122_; 
v___x_5122_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5122_;
}
}
else
{
lean_object* v___x_5123_; 
lean_dec_ref(v_str_5109_);
v___x_5123_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser___closed__0));
return v___x_5123_;
}
}
}
}
else
{
lean_object* v___x_5124_; 
lean_dec_ref_known(v_pre_5107_, 2);
lean_dec_ref_known(v_pre_5106_, 2);
lean_dec_ref_known(v_declName_5105_, 2);
v___x_5124_ = lean_box(0);
return v___x_5124_;
}
}
case 0:
{
lean_object* v_str_5125_; lean_object* v_str_5126_; lean_object* v___x_5127_; uint8_t v___x_5128_; 
v_str_5125_ = lean_ctor_get(v_declName_5105_, 1);
lean_inc_ref(v_str_5125_);
lean_dec_ref_known(v_declName_5105_, 2);
v_str_5126_ = lean_ctor_get(v_pre_5106_, 1);
lean_inc_ref(v_str_5126_);
lean_dec_ref_known(v_pre_5106_, 2);
v___x_5127_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__3));
v___x_5128_ = lean_string_dec_eq(v_str_5126_, v___x_5127_);
lean_dec_ref(v_str_5126_);
if (v___x_5128_ == 0)
{
lean_object* v___x_5129_; 
lean_dec_ref(v_str_5125_);
lean_del_object(v___x_5102_);
v___x_5129_ = lean_box(0);
return v___x_5129_;
}
else
{
lean_object* v___x_5130_; uint8_t v___x_5131_; 
v___x_5130_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__6));
v___x_5131_ = lean_string_dec_eq(v_str_5125_, v___x_5130_);
if (v___x_5131_ == 0)
{
lean_object* v___x_5132_; uint8_t v___x_5133_; 
v___x_5132_ = ((lean_object*)(l_Lean_Parser_mkParserOfConstantUnsafe___closed__7));
v___x_5133_ = lean_string_dec_eq(v_str_5125_, v___x_5132_);
lean_dec_ref(v_str_5125_);
if (v___x_5133_ == 0)
{
lean_object* v___x_5134_; 
lean_del_object(v___x_5102_);
v___x_5134_ = lean_box(0);
return v___x_5134_;
}
else
{
lean_object* v___x_5135_; lean_object* v___x_5137_; 
v___x_5135_ = lean_box(v___x_5128_);
if (v_isShared_5103_ == 0)
{
lean_ctor_set(v___x_5102_, 0, v___x_5135_);
v___x_5137_ = v___x_5102_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v___x_5135_);
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
lean_object* v___x_5139_; lean_object* v___x_5141_; 
lean_dec_ref(v_str_5125_);
v___x_5139_ = lean_box(v___x_5128_);
if (v_isShared_5103_ == 0)
{
lean_ctor_set(v___x_5102_, 0, v___x_5139_);
v___x_5141_ = v___x_5102_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v___x_5139_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
}
}
default: 
{
lean_object* v___x_5143_; 
lean_dec_ref_known(v_pre_5106_, 2);
lean_dec_ref_known(v_declName_5105_, 2);
lean_del_object(v___x_5102_);
v___x_5143_ = lean_box(0);
return v___x_5143_;
}
}
}
else
{
lean_object* v___x_5144_; 
lean_dec(v_pre_5106_);
lean_dec_ref_known(v_declName_5105_, 2);
lean_del_object(v___x_5102_);
v___x_5144_ = lean_box(0);
return v___x_5144_;
}
}
else
{
lean_object* v___x_5145_; 
lean_dec(v_declName_5105_);
lean_del_object(v___x_5102_);
v___x_5145_ = lean_box(0);
return v___x_5145_;
}
}
else
{
lean_object* v___x_5146_; 
lean_dec_ref(v___x_5104_);
lean_del_object(v___x_5102_);
v___x_5146_ = lean_box(0);
return v___x_5146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(lean_object* v_env_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_){
_start:
{
if (lean_obj_tag(v_a_5149_) == 0)
{
lean_object* v___x_5151_; 
lean_dec_ref(v_env_5148_);
v___x_5151_ = lean_array_to_list(v_a_5150_);
return v___x_5151_;
}
else
{
lean_object* v_head_5152_; lean_object* v_snd_5153_; 
v_head_5152_ = lean_ctor_get(v_a_5149_, 0);
v_snd_5153_ = lean_ctor_get(v_head_5152_, 1);
if (lean_obj_tag(v_snd_5153_) == 0)
{
lean_object* v_tail_5154_; lean_object* v_fst_5155_; lean_object* v___x_5156_; 
lean_inc(v_head_5152_);
v_tail_5154_ = lean_ctor_get(v_a_5149_, 1);
lean_inc(v_tail_5154_);
lean_dec_ref_known(v_a_5149_, 2);
v_fst_5155_ = lean_ctor_get(v_head_5152_, 0);
lean_inc_n(v_fst_5155_, 2);
lean_dec(v_head_5152_);
lean_inc_ref(v_env_5148_);
v___x_5156_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5148_, v_fst_5155_);
if (lean_obj_tag(v___x_5156_) == 0)
{
lean_dec(v_fst_5155_);
v_a_5149_ = v_tail_5154_;
goto _start;
}
else
{
lean_object* v_val_5158_; lean_object* v___x_5159_; uint8_t v___x_5160_; lean_object* v___x_5161_; 
v_val_5158_ = lean_ctor_get(v___x_5156_, 0);
lean_inc(v_val_5158_);
lean_dec_ref_known(v___x_5156_, 1);
v___x_5159_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5159_, 0, v_fst_5155_);
v___x_5160_ = lean_unbox(v_val_5158_);
lean_dec(v_val_5158_);
lean_ctor_set_uint8(v___x_5159_, sizeof(void*)*1, v___x_5160_);
v___x_5161_ = lean_array_push(v_a_5150_, v___x_5159_);
v_a_5149_ = v_tail_5154_;
v_a_5150_ = v___x_5161_;
goto _start;
}
}
else
{
lean_object* v_tail_5163_; 
v_tail_5163_ = lean_ctor_get(v_a_5149_, 1);
lean_inc(v_tail_5163_);
lean_dec_ref_known(v_a_5149_, 2);
v_a_5149_ = v_tail_5163_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(lean_object* v_env_5168_, lean_object* v_as_x27_5169_, lean_object* v_b_5170_){
_start:
{
if (lean_obj_tag(v_as_x27_5169_) == 0)
{
lean_dec_ref(v_env_5168_);
lean_inc_ref(v_b_5170_);
return v_b_5170_;
}
else
{
lean_object* v_head_5171_; lean_object* v_tail_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; 
v_head_5171_ = lean_ctor_get(v_as_x27_5169_, 0);
v_tail_5172_ = lean_ctor_get(v_as_x27_5169_, 1);
v___x_5173_ = lean_box(0);
v___x_5174_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
if (lean_obj_tag(v_head_5171_) == 1)
{
lean_object* v_fields_5175_; 
v_fields_5175_ = lean_ctor_get(v_head_5171_, 1);
if (lean_obj_tag(v_fields_5175_) == 0)
{
lean_object* v_n_5176_; lean_object* v___x_5177_; 
v_n_5176_ = lean_ctor_get(v_head_5171_, 0);
lean_inc(v_n_5176_);
lean_inc_ref(v_env_5168_);
v___x_5177_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_isParser(v_env_5168_, v_n_5176_);
if (lean_obj_tag(v___x_5177_) == 1)
{
lean_object* v_val_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5190_; 
lean_dec_ref(v_env_5168_);
v_val_5178_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5180_ = v___x_5177_;
v_isShared_5181_ = v_isSharedCheck_5190_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_val_5178_);
lean_dec(v___x_5177_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5190_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5182_; uint8_t v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5187_; 
lean_inc(v_n_5176_);
v___x_5182_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_5182_, 0, v_n_5176_);
v___x_5183_ = lean_unbox(v_val_5178_);
lean_dec(v_val_5178_);
lean_ctor_set_uint8(v___x_5182_, sizeof(void*)*1, v___x_5183_);
v___x_5184_ = lean_box(0);
v___x_5185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5185_, 0, v___x_5182_);
lean_ctor_set(v___x_5185_, 1, v___x_5184_);
if (v_isShared_5181_ == 0)
{
lean_ctor_set(v___x_5180_, 0, v___x_5185_);
v___x_5187_ = v___x_5180_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v___x_5185_);
v___x_5187_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
lean_object* v___x_5188_; 
v___x_5188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5188_, 0, v___x_5187_);
lean_ctor_set(v___x_5188_, 1, v___x_5173_);
return v___x_5188_;
}
}
}
else
{
lean_dec(v___x_5177_);
v_as_x27_5169_ = v_tail_5172_;
v_b_5170_ = v___x_5174_;
goto _start;
}
}
else
{
v_as_x27_5169_ = v_tail_5172_;
v_b_5170_ = v___x_5174_;
goto _start;
}
}
else
{
v_as_x27_5169_ = v_tail_5172_;
v_b_5170_ = v___x_5174_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___boxed(lean_object* v_env_5194_, lean_object* v_as_x27_5195_, lean_object* v_b_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5194_, v_as_x27_5195_, v_b_5196_);
lean_dec_ref(v_b_5196_);
lean_dec(v_as_x27_5195_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(lean_object* v_env_5200_, lean_object* v_opts_5201_, lean_object* v_currNamespace_5202_, lean_object* v_openDecls_5203_, lean_object* v_ident_5204_){
_start:
{
if (lean_obj_tag(v_ident_5204_) == 3)
{
lean_object* v_val_5205_; lean_object* v_preresolved_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v_fst_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5244_; 
v_val_5205_ = lean_ctor_get(v_ident_5204_, 2);
lean_inc(v_val_5205_);
v_preresolved_5206_ = lean_ctor_get(v_ident_5204_, 3);
lean_inc(v_preresolved_5206_);
lean_dec_ref_known(v_ident_5204_, 4);
v___x_5207_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg___closed__0));
lean_inc_ref(v_env_5200_);
v___x_5208_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5200_, v_preresolved_5206_, v___x_5207_);
lean_dec(v_preresolved_5206_);
v_fst_5209_ = lean_ctor_get(v___x_5208_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v___x_5208_);
if (v_isSharedCheck_5244_ == 0)
{
lean_object* v_unused_5245_; 
v_unused_5245_ = lean_ctor_get(v___x_5208_, 1);
lean_dec(v_unused_5245_);
v___x_5211_ = v___x_5208_;
v_isShared_5212_ = v_isSharedCheck_5244_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_fst_5209_);
lean_dec(v___x_5208_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5244_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
if (lean_obj_tag(v_fst_5209_) == 0)
{
lean_object* v___x_5213_; uint8_t v___x_5214_; 
v___x_5213_ = l_Lean_Name_eraseMacroScopes(v_val_5205_);
lean_inc_ref(v_env_5200_);
v___x_5214_ = l_Lean_Parser_isParserCategory(v_env_5200_, v___x_5213_);
if (v___x_5214_ == 0)
{
lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; uint8_t v___x_5218_; 
lean_inc_ref_n(v_env_5200_, 2);
v___x_5215_ = l_Lean_ResolveName_resolveGlobalName(v_env_5200_, v_opts_5201_, v_currNamespace_5202_, v_openDecls_5203_, v_val_5205_);
v___x_5216_ = ((lean_object*)(l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___closed__0));
v___x_5217_ = l_List_filterMapTR_go___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__1(v_env_5200_, v___x_5215_, v___x_5216_);
v___x_5218_ = l_List_isEmpty___redArg(v___x_5217_);
if (v___x_5218_ == 0)
{
lean_dec(v___x_5213_);
lean_del_object(v___x_5211_);
lean_dec_ref(v_env_5200_);
return v___x_5217_;
}
else
{
lean_object* v___x_5219_; lean_object* v_asyncMode_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; 
lean_dec(v___x_5217_);
v___x_5219_ = l_Lean_Parser_aliasExtension;
v_asyncMode_5220_ = lean_ctor_get(v___x_5219_, 2);
v___x_5221_ = lean_box(1);
v___x_5222_ = lean_box(0);
v___x_5223_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_5221_, v___x_5219_, v_env_5200_, v_asyncMode_5220_, v___x_5222_, v___x_5214_);
v___x_5224_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_5223_, v___x_5213_);
lean_dec(v___x_5213_);
lean_dec(v___x_5223_);
if (lean_obj_tag(v___x_5224_) == 1)
{
lean_object* v_val_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5236_; 
v_val_5225_ = lean_ctor_get(v___x_5224_, 0);
v_isSharedCheck_5236_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5236_ == 0)
{
v___x_5227_ = v___x_5224_;
v_isShared_5228_ = v_isSharedCheck_5236_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_val_5225_);
lean_dec(v___x_5224_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5236_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5230_; 
if (v_isShared_5228_ == 0)
{
lean_ctor_set_tag(v___x_5227_, 2);
v___x_5230_ = v___x_5227_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v_val_5225_);
v___x_5230_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
lean_object* v___x_5231_; lean_object* v___x_5233_; 
v___x_5231_ = lean_box(0);
if (v_isShared_5212_ == 0)
{
lean_ctor_set_tag(v___x_5211_, 1);
lean_ctor_set(v___x_5211_, 1, v___x_5231_);
lean_ctor_set(v___x_5211_, 0, v___x_5230_);
v___x_5233_ = v___x_5211_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v___x_5230_);
lean_ctor_set(v_reuseFailAlloc_5234_, 1, v___x_5231_);
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
else
{
lean_object* v___x_5237_; 
lean_dec(v___x_5224_);
lean_del_object(v___x_5211_);
v___x_5237_ = lean_box(0);
return v___x_5237_;
}
}
}
else
{
lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5241_; 
lean_dec(v_val_5205_);
lean_dec(v_openDecls_5203_);
lean_dec(v_currNamespace_5202_);
lean_dec_ref(v_env_5200_);
v___x_5238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5238_, 0, v___x_5213_);
v___x_5239_ = lean_box(0);
if (v_isShared_5212_ == 0)
{
lean_ctor_set_tag(v___x_5211_, 1);
lean_ctor_set(v___x_5211_, 1, v___x_5239_);
lean_ctor_set(v___x_5211_, 0, v___x_5238_);
v___x_5241_ = v___x_5211_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v___x_5238_);
lean_ctor_set(v_reuseFailAlloc_5242_, 1, v___x_5239_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
else
{
lean_object* v_val_5243_; 
lean_del_object(v___x_5211_);
lean_dec(v_val_5205_);
lean_dec(v_openDecls_5203_);
lean_dec(v_currNamespace_5202_);
lean_dec_ref(v_env_5200_);
v_val_5243_ = lean_ctor_get(v_fst_5209_, 0);
lean_inc(v_val_5243_);
lean_dec_ref_known(v_fst_5209_, 1);
return v_val_5243_;
}
}
}
else
{
lean_object* v___x_5246_; 
lean_dec(v_ident_5204_);
lean_dec(v_openDecls_5203_);
lean_dec(v_currNamespace_5202_);
lean_dec_ref(v_env_5200_);
v___x_5246_ = lean_box(0);
return v___x_5246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore___boxed(lean_object* v_env_5247_, lean_object* v_opts_5248_, lean_object* v_currNamespace_5249_, lean_object* v_openDecls_5250_, lean_object* v_ident_5251_){
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5247_, v_opts_5248_, v_currNamespace_5249_, v_openDecls_5250_, v_ident_5251_);
lean_dec_ref(v_opts_5248_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(lean_object* v_env_5253_, lean_object* v_as_5254_, lean_object* v_as_x27_5255_, lean_object* v_b_5256_, lean_object* v_a_5257_){
_start:
{
lean_object* v___x_5258_; 
v___x_5258_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___redArg(v_env_5253_, v_as_x27_5255_, v_b_5256_);
return v___x_5258_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0___boxed(lean_object* v_env_5259_, lean_object* v_as_5260_, lean_object* v_as_x27_5261_, lean_object* v_b_5262_, lean_object* v_a_5263_){
_start:
{
lean_object* v_res_5264_; 
v_res_5264_ = l_List_forIn_x27_loop___at___00__private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore_spec__0(v_env_5259_, v_as_5260_, v_as_x27_5261_, v_b_5262_, v_a_5263_);
lean_dec_ref(v_b_5262_);
lean_dec(v_as_x27_5261_);
lean_dec(v_as_5260_);
return v_res_5264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName(lean_object* v_ctx_5265_, lean_object* v_id_5266_, uint8_t v_unsetExporting_5267_){
_start:
{
lean_object* v___y_5269_; 
if (v_unsetExporting_5267_ == 0)
{
lean_object* v_toParserModuleContext_5275_; lean_object* v_env_5276_; 
v_toParserModuleContext_5275_ = lean_ctor_get(v_ctx_5265_, 1);
v_env_5276_ = lean_ctor_get(v_toParserModuleContext_5275_, 0);
lean_inc_ref(v_env_5276_);
v___y_5269_ = v_env_5276_;
goto v___jp_5268_;
}
else
{
lean_object* v_toParserModuleContext_5277_; lean_object* v_env_5278_; uint8_t v___x_5279_; lean_object* v___x_5280_; 
v_toParserModuleContext_5277_ = lean_ctor_get(v_ctx_5265_, 1);
v_env_5278_ = lean_ctor_get(v_toParserModuleContext_5277_, 0);
v___x_5279_ = 0;
lean_inc_ref(v_env_5278_);
v___x_5280_ = l_Lean_Environment_setExporting(v_env_5278_, v___x_5279_);
v___y_5269_ = v___x_5280_;
goto v___jp_5268_;
}
v___jp_5268_:
{
lean_object* v_toParserModuleContext_5270_; lean_object* v_options_5271_; lean_object* v_currNamespace_5272_; lean_object* v_openDecls_5273_; lean_object* v___x_5274_; 
v_toParserModuleContext_5270_ = lean_ctor_get(v_ctx_5265_, 1);
lean_inc_ref(v_toParserModuleContext_5270_);
lean_dec_ref(v_ctx_5265_);
v_options_5271_ = lean_ctor_get(v_toParserModuleContext_5270_, 1);
lean_inc_ref(v_options_5271_);
v_currNamespace_5272_ = lean_ctor_get(v_toParserModuleContext_5270_, 2);
lean_inc(v_currNamespace_5272_);
v_openDecls_5273_ = lean_ctor_get(v_toParserModuleContext_5270_, 3);
lean_inc(v_openDecls_5273_);
lean_dec_ref(v_toParserModuleContext_5270_);
v___x_5274_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v___y_5269_, v_options_5271_, v_currNamespace_5272_, v_openDecls_5273_, v_id_5266_);
lean_dec_ref(v_options_5271_);
return v___x_5274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_resolveParserName___boxed(lean_object* v_ctx_5281_, lean_object* v_id_5282_, lean_object* v_unsetExporting_5283_){
_start:
{
uint8_t v_unsetExporting_boxed_5284_; lean_object* v_res_5285_; 
v_unsetExporting_boxed_5284_ = lean_unbox(v_unsetExporting_5283_);
v_res_5285_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5281_, v_id_5282_, v_unsetExporting_boxed_5284_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName(lean_object* v_id_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_){
_start:
{
lean_object* v___x_5290_; lean_object* v_toCold_5291_; lean_object* v_env_5292_; lean_object* v_currNamespace_5293_; lean_object* v_openDecls_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; 
v___x_5290_ = lean_st_ref_get(v_a_5288_);
v_toCold_5291_ = lean_ctor_get(v_a_5287_, 0);
v_env_5292_ = lean_ctor_get(v___x_5290_, 0);
lean_inc_ref(v_env_5292_);
lean_dec(v___x_5290_);
v_currNamespace_5293_ = lean_ctor_get(v_toCold_5291_, 4);
v_openDecls_5294_ = lean_ctor_get(v_toCold_5291_, 5);
v___x_5295_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_5287_);
lean_inc(v_openDecls_5294_);
lean_inc(v_currNamespace_5293_);
v___x_5296_ = l___private_Lean_Parser_Extension_0__Lean_Parser_resolveParserNameCore(v_env_5292_, v___x_5295_, v_currNamespace_5293_, v_openDecls_5294_, v_id_5286_);
lean_dec_ref(v___x_5295_);
v___x_5297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5297_, 0, v___x_5296_);
return v___x_5297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_resolveParserName___boxed(lean_object* v_id_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_){
_start:
{
lean_object* v_res_5302_; 
v_res_5302_ = l_Lean_Parser_resolveParserName(v_id_5298_, v_a_5299_, v_a_5300_);
lean_dec(v_a_5300_);
lean_dec_ref(v_a_5299_);
return v_res_5302_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(lean_object* v_x_5303_, lean_object* v_x_5304_){
_start:
{
if (lean_obj_tag(v_x_5303_) == 0)
{
if (lean_obj_tag(v_x_5304_) == 0)
{
uint8_t v___x_5305_; 
v___x_5305_ = 1;
return v___x_5305_;
}
else
{
uint8_t v___x_5306_; 
v___x_5306_ = 0;
return v___x_5306_;
}
}
else
{
if (lean_obj_tag(v_x_5304_) == 0)
{
uint8_t v___x_5307_; 
v___x_5307_ = 0;
return v___x_5307_;
}
else
{
lean_object* v_val_5308_; lean_object* v_val_5309_; uint8_t v___x_5310_; 
v_val_5308_ = lean_ctor_get(v_x_5303_, 0);
v_val_5309_ = lean_ctor_get(v_x_5304_, 0);
v___x_5310_ = l_Lean_Parser_instBEqError_beq(v_val_5308_, v_val_5309_);
return v___x_5310_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0___boxed(lean_object* v_x_5311_, lean_object* v_x_5312_){
_start:
{
uint8_t v_res_5313_; lean_object* v_r_5314_; 
v_res_5313_ = l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_x_5311_, v_x_5312_);
lean_dec(v_x_5312_);
lean_dec(v_x_5311_);
v_r_5314_ = lean_box(v_res_5313_);
return v_r_5314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0(uint8_t v___x_5315_, lean_object* v_ctx_5316_){
_start:
{
lean_object* v_toParserModuleContext_5317_; lean_object* v_toInputContext_5318_; lean_object* v_toCacheableParserContext_5319_; lean_object* v_tokens_5320_; lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5345_; 
v_toParserModuleContext_5317_ = lean_ctor_get(v_ctx_5316_, 1);
v_toInputContext_5318_ = lean_ctor_get(v_ctx_5316_, 0);
v_toCacheableParserContext_5319_ = lean_ctor_get(v_ctx_5316_, 2);
v_tokens_5320_ = lean_ctor_get(v_ctx_5316_, 3);
v_isSharedCheck_5345_ = !lean_is_exclusive(v_ctx_5316_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5322_ = v_ctx_5316_;
v_isShared_5323_ = v_isSharedCheck_5345_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_tokens_5320_);
lean_inc(v_toCacheableParserContext_5319_);
lean_inc(v_toParserModuleContext_5317_);
lean_inc(v_toInputContext_5318_);
lean_dec(v_ctx_5316_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5345_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v_env_5324_; lean_object* v_options_5325_; lean_object* v_currNamespace_5326_; lean_object* v_openDecls_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5344_; 
v_env_5324_ = lean_ctor_get(v_toParserModuleContext_5317_, 0);
v_options_5325_ = lean_ctor_get(v_toParserModuleContext_5317_, 1);
v_currNamespace_5326_ = lean_ctor_get(v_toParserModuleContext_5317_, 2);
v_openDecls_5327_ = lean_ctor_get(v_toParserModuleContext_5317_, 3);
v_isSharedCheck_5344_ = !lean_is_exclusive(v_toParserModuleContext_5317_);
if (v_isSharedCheck_5344_ == 0)
{
v___x_5329_ = v_toParserModuleContext_5317_;
v_isShared_5330_ = v_isSharedCheck_5344_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_openDecls_5327_);
lean_inc(v_currNamespace_5326_);
lean_inc(v_options_5325_);
lean_inc(v_env_5324_);
lean_dec(v_toParserModuleContext_5317_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5344_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5331_; uint8_t v___y_5333_; lean_object* v___x_5341_; uint8_t v___x_5342_; 
v___x_5331_ = ((lean_object*)(l_Lean_Parser_evalInsideQuot___lam__0___closed__2));
v___x_5341_ = l_Lean_Parser_internal_parseQuotWithCurrentStage;
v___x_5342_ = l_Lean_Option_get___at___00Lean_Parser_evalInsideQuot_spec__1(v_options_5325_, v___x_5341_);
if (v___x_5342_ == 0)
{
uint8_t v___x_5343_; 
v___x_5343_ = 1;
v___y_5333_ = v___x_5343_;
goto v___jp_5332_;
}
else
{
v___y_5333_ = v___x_5315_;
goto v___jp_5332_;
}
v___jp_5332_:
{
lean_object* v___x_5334_; lean_object* v___x_5336_; 
v___x_5334_ = l_Lean_Options_set___at___00Lean_Parser_evalInsideQuot_spec__0(v_options_5325_, v___x_5331_, v___y_5333_);
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 1, v___x_5334_);
v___x_5336_ = v___x_5329_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_env_5324_);
lean_ctor_set(v_reuseFailAlloc_5340_, 1, v___x_5334_);
lean_ctor_set(v_reuseFailAlloc_5340_, 2, v_currNamespace_5326_);
lean_ctor_set(v_reuseFailAlloc_5340_, 3, v_openDecls_5327_);
v___x_5336_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
lean_object* v___x_5338_; 
if (v_isShared_5323_ == 0)
{
lean_ctor_set(v___x_5322_, 1, v___x_5336_);
v___x_5338_ = v___x_5322_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_toInputContext_5318_);
lean_ctor_set(v_reuseFailAlloc_5339_, 1, v___x_5336_);
lean_ctor_set(v_reuseFailAlloc_5339_, 2, v_toCacheableParserContext_5319_);
lean_ctor_set(v_reuseFailAlloc_5339_, 3, v_tokens_5320_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___lam__0___boxed(lean_object* v___x_5346_, lean_object* v_ctx_5347_){
_start:
{
uint8_t v___x_1069__boxed_5348_; lean_object* v_res_5349_; 
v___x_1069__boxed_5348_ = lean_unbox(v___x_5346_);
v_res_5349_ = l_Lean_Parser_parserOfStackFn___lam__0(v___x_1069__boxed_5348_, v_ctx_5347_);
return v_res_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn(lean_object* v_offset_5357_, lean_object* v_ctx_5358_, lean_object* v_s_5359_){
_start:
{
lean_object* v_stxStack_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; uint8_t v___x_5364_; 
v_stxStack_5360_ = lean_ctor_get(v_s_5359_, 0);
v___x_5361_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5360_);
v___x_5362_ = lean_unsigned_to_nat(1u);
v___x_5363_ = lean_nat_add(v_offset_5357_, v___x_5362_);
v___x_5364_ = lean_nat_dec_lt(v___x_5361_, v___x_5363_);
lean_dec(v___x_5363_);
if (v___x_5364_ == 0)
{
lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; 
v___x_5365_ = lean_nat_sub(v___x_5361_, v_offset_5357_);
lean_dec(v___x_5361_);
v___x_5366_ = lean_nat_sub(v___x_5365_, v___x_5362_);
lean_dec(v___x_5365_);
v___x_5367_ = l_Lean_Parser_SyntaxStack_get_x21(v_stxStack_5360_, v___x_5366_);
lean_dec(v___x_5366_);
if (lean_obj_tag(v___x_5367_) == 3)
{
uint8_t v___x_5379_; lean_object* v___x_5380_; 
v___x_5379_ = 1;
lean_inc_ref(v___x_5367_);
lean_inc_ref(v_ctx_5358_);
v___x_5380_ = l_Lean_Parser_ParserContext_resolveParserName(v_ctx_5358_, v___x_5367_, v___x_5379_);
if (lean_obj_tag(v___x_5380_) == 0)
{
lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; 
lean_dec_ref(v_ctx_5358_);
v___x_5381_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__1));
v___x_5382_ = lean_box(0);
v___x_5383_ = l_Lean_Syntax_formatStx(v___x_5367_, v___x_5382_, v___x_5364_);
v___x_5384_ = l_Std_Format_defWidth;
v___x_5385_ = lean_unsigned_to_nat(0u);
v___x_5386_ = l_Std_Format_pretty(v___x_5383_, v___x_5384_, v___x_5385_, v___x_5385_);
v___x_5387_ = lean_string_append(v___x_5381_, v___x_5386_);
lean_dec_ref(v___x_5386_);
v___x_5388_ = lean_box(0);
v___x_5389_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5359_, v___x_5387_, v___x_5388_, v___x_5379_);
return v___x_5389_;
}
else
{
lean_object* v_head_5390_; lean_object* v_tail_5391_; lean_object* v_iniSz_5392_; lean_object* v_s_5394_; 
v_head_5390_ = lean_ctor_get(v___x_5380_, 0);
lean_inc(v_head_5390_);
v_tail_5391_ = lean_ctor_get(v___x_5380_, 1);
lean_inc(v_tail_5391_);
lean_dec_ref_known(v___x_5380_, 2);
v_iniSz_5392_ = l_Lean_Parser_ParserState_stackSize(v_s_5359_);
switch(lean_obj_tag(v_head_5390_))
{
case 0:
{
if (lean_obj_tag(v_tail_5391_) == 0)
{
lean_object* v_cat_5404_; lean_object* v___x_5405_; 
lean_dec_ref_known(v___x_5367_, 4);
v_cat_5404_ = lean_ctor_get(v_head_5390_, 0);
lean_inc(v_cat_5404_);
lean_dec_ref_known(v_head_5390_, 1);
v___x_5405_ = l_Lean_Parser_categoryParserFn(v_cat_5404_, v_ctx_5358_, v_s_5359_);
v_s_5394_ = v___x_5405_;
goto v___jp_5393_;
}
else
{
lean_dec_ref_known(v_tail_5391_, 2);
lean_dec_ref_known(v_head_5390_, 1);
lean_dec(v_iniSz_5392_);
lean_dec_ref(v_ctx_5358_);
goto v___jp_5368_;
}
}
case 1:
{
if (lean_obj_tag(v_tail_5391_) == 0)
{
lean_object* v_decl_5406_; lean_object* v___x_5407_; lean_object* v___f_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; 
lean_dec_ref_known(v___x_5367_, 4);
v_decl_5406_ = lean_ctor_get(v_head_5390_, 0);
lean_inc(v_decl_5406_);
lean_dec_ref_known(v_head_5390_, 1);
v___x_5407_ = lean_box(v___x_5364_);
v___f_5408_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5408_, 0, v___x_5407_);
v___x_5409_ = lean_box(0);
v___x_5410_ = lean_alloc_closure((void*)(l_Lean_Parser_evalParserConstUnsafe), 4, 2);
lean_closure_set(v___x_5410_, 0, v_decl_5406_);
lean_closure_set(v___x_5410_, 1, v___x_5409_);
v___x_5411_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_5408_, v___x_5410_, v_ctx_5358_, v_s_5359_);
v_s_5394_ = v___x_5411_;
goto v___jp_5393_;
}
else
{
lean_dec_ref_known(v_tail_5391_, 2);
lean_dec_ref_known(v_head_5390_, 1);
lean_dec(v_iniSz_5392_);
lean_dec_ref(v_ctx_5358_);
goto v___jp_5368_;
}
}
default: 
{
if (lean_obj_tag(v_tail_5391_) == 0)
{
lean_object* v_p_5412_; 
v_p_5412_ = lean_ctor_get(v_head_5390_, 0);
lean_inc_ref(v_p_5412_);
lean_dec_ref_known(v_head_5390_, 1);
if (lean_obj_tag(v_p_5412_) == 0)
{
lean_object* v_p_5413_; lean_object* v_fn_5414_; lean_object* v___x_5415_; 
lean_dec_ref_known(v___x_5367_, 4);
v_p_5413_ = lean_ctor_get(v_p_5412_, 0);
lean_inc(v_p_5413_);
lean_dec_ref_known(v_p_5412_, 1);
v_fn_5414_ = lean_ctor_get(v_p_5413_, 1);
lean_inc_ref(v_fn_5414_);
lean_dec(v_p_5413_);
v___x_5415_ = lean_apply_2(v_fn_5414_, v_ctx_5358_, v_s_5359_);
v_s_5394_ = v___x_5415_;
goto v___jp_5393_;
}
else
{
lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; 
lean_dec_ref(v_p_5412_);
lean_dec(v_iniSz_5392_);
lean_dec_ref(v_ctx_5358_);
v___x_5416_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__3));
v___x_5417_ = lean_box(0);
v___x_5418_ = l_Lean_Syntax_formatStx(v___x_5367_, v___x_5417_, v___x_5364_);
v___x_5419_ = l_Std_Format_defWidth;
v___x_5420_ = lean_unsigned_to_nat(0u);
v___x_5421_ = l_Std_Format_pretty(v___x_5418_, v___x_5419_, v___x_5420_, v___x_5420_);
v___x_5422_ = lean_string_append(v___x_5416_, v___x_5421_);
lean_dec_ref(v___x_5421_);
v___x_5423_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__4));
v___x_5424_ = lean_string_append(v___x_5422_, v___x_5423_);
v___x_5425_ = lean_box(0);
v___x_5426_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5359_, v___x_5424_, v___x_5425_, v___x_5379_);
return v___x_5426_;
}
}
else
{
lean_dec_ref_known(v_tail_5391_, 2);
lean_dec_ref_known(v_head_5390_, 1);
lean_dec(v_iniSz_5392_);
lean_dec_ref(v_ctx_5358_);
goto v___jp_5368_;
}
}
}
v___jp_5393_:
{
lean_object* v_errorMsg_5395_; lean_object* v___x_5396_; uint8_t v___x_5397_; 
v_errorMsg_5395_ = lean_ctor_get(v_s_5394_, 4);
v___x_5396_ = lean_box(0);
v___x_5397_ = l_instBEqOption_beq___at___00Lean_Parser_parserOfStackFn_spec__0(v_errorMsg_5395_, v___x_5396_);
if (v___x_5397_ == 0)
{
lean_dec(v_iniSz_5392_);
return v_s_5394_;
}
else
{
lean_object* v___x_5398_; lean_object* v___x_5399_; uint8_t v___x_5400_; 
v___x_5398_ = l_Lean_Parser_ParserState_stackSize(v_s_5394_);
v___x_5399_ = lean_nat_add(v_iniSz_5392_, v___x_5362_);
lean_dec(v_iniSz_5392_);
v___x_5400_ = lean_nat_dec_eq(v___x_5398_, v___x_5399_);
lean_dec(v___x_5399_);
lean_dec(v___x_5398_);
if (v___x_5400_ == 0)
{
lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; 
v___x_5401_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__2));
v___x_5402_ = lean_box(0);
v___x_5403_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5394_, v___x_5401_, v___x_5402_, v___x_5397_);
return v___x_5403_;
}
else
{
return v_s_5394_;
}
}
}
}
}
else
{
lean_object* v___x_5427_; lean_object* v___x_5428_; uint8_t v___x_5429_; lean_object* v___x_5430_; 
lean_dec(v___x_5367_);
lean_dec_ref(v_ctx_5358_);
v___x_5427_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__5));
v___x_5428_ = lean_box(0);
v___x_5429_ = 1;
v___x_5430_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5359_, v___x_5427_, v___x_5428_, v___x_5429_);
return v___x_5430_;
}
v___jp_5368_:
{
lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; uint8_t v___x_5377_; lean_object* v___x_5378_; 
v___x_5369_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__0));
v___x_5370_ = lean_box(0);
v___x_5371_ = l_Lean_Syntax_formatStx(v___x_5367_, v___x_5370_, v___x_5364_);
v___x_5372_ = l_Std_Format_defWidth;
v___x_5373_ = lean_unsigned_to_nat(0u);
v___x_5374_ = l_Std_Format_pretty(v___x_5371_, v___x_5372_, v___x_5373_, v___x_5373_);
v___x_5375_ = lean_string_append(v___x_5369_, v___x_5374_);
lean_dec_ref(v___x_5374_);
v___x_5376_ = lean_box(0);
v___x_5377_ = 1;
v___x_5378_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5359_, v___x_5375_, v___x_5376_, v___x_5377_);
return v___x_5378_;
}
}
else
{
lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; 
lean_dec(v___x_5361_);
lean_dec_ref(v_ctx_5358_);
v___x_5431_ = ((lean_object*)(l_Lean_Parser_parserOfStackFn___closed__6));
v___x_5432_ = lean_box(0);
v___x_5433_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5359_, v___x_5431_, v___x_5432_, v___x_5364_);
return v___x_5433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStackFn___boxed(lean_object* v_offset_5434_, lean_object* v_ctx_5435_, lean_object* v_s_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l_Lean_Parser_parserOfStackFn(v_offset_5434_, v_ctx_5435_, v_s_5436_);
lean_dec(v_offset_5434_);
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__0(lean_object* v_prec_5438_, lean_object* v_x_5439_){
_start:
{
lean_object* v_quotDepth_5440_; uint8_t v_suppressInsideQuot_5441_; lean_object* v_savedPos_x3f_5442_; lean_object* v_forbiddenTks_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5450_; 
v_quotDepth_5440_ = lean_ctor_get(v_x_5439_, 1);
v_suppressInsideQuot_5441_ = lean_ctor_get_uint8(v_x_5439_, sizeof(void*)*4);
v_savedPos_x3f_5442_ = lean_ctor_get(v_x_5439_, 2);
v_forbiddenTks_5443_ = lean_ctor_get(v_x_5439_, 3);
v_isSharedCheck_5450_ = !lean_is_exclusive(v_x_5439_);
if (v_isSharedCheck_5450_ == 0)
{
lean_object* v_unused_5451_; 
v_unused_5451_ = lean_ctor_get(v_x_5439_, 0);
lean_dec(v_unused_5451_);
v___x_5445_ = v_x_5439_;
v_isShared_5446_ = v_isSharedCheck_5450_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_forbiddenTks_5443_);
lean_inc(v_savedPos_x3f_5442_);
lean_inc(v_quotDepth_5440_);
lean_dec(v_x_5439_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5450_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
lean_object* v___x_5448_; 
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 0, v_prec_5438_);
v___x_5448_ = v___x_5445_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_prec_5438_);
lean_ctor_set(v_reuseFailAlloc_5449_, 1, v_quotDepth_5440_);
lean_ctor_set(v_reuseFailAlloc_5449_, 2, v_savedPos_x3f_5442_);
lean_ctor_set(v_reuseFailAlloc_5449_, 3, v_forbiddenTks_5443_);
lean_ctor_set_uint8(v_reuseFailAlloc_5449_, sizeof(void*)*4, v_suppressInsideQuot_5441_);
v___x_5448_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
return v___x_5448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1(lean_object* v___y_5452_){
_start:
{
lean_inc(v___y_5452_);
return v___y_5452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__1___boxed(lean_object* v___y_5453_){
_start:
{
lean_object* v_res_5454_; 
v_res_5454_ = l_Lean_Parser_parserOfStack___lam__1(v___y_5453_);
lean_dec(v___y_5453_);
return v_res_5454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2(lean_object* v___y_5455_){
_start:
{
lean_inc_ref(v___y_5455_);
return v___y_5455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack___lam__2___boxed(lean_object* v___y_5456_){
_start:
{
lean_object* v_res_5457_; 
v_res_5457_ = l_Lean_Parser_parserOfStack___lam__2(v___y_5456_);
lean_dec_ref(v___y_5456_);
return v_res_5457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_parserOfStack(lean_object* v_offset_5464_, lean_object* v_prec_5465_){
_start:
{
lean_object* v___f_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; 
v___f_5466_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStack___lam__0), 2, 1);
lean_closure_set(v___f_5466_, 0, v_prec_5465_);
v___x_5467_ = ((lean_object*)(l_Lean_Parser_parserOfStack___closed__2));
v___x_5468_ = lean_alloc_closure((void*)(l_Lean_Parser_parserOfStackFn___boxed), 3, 1);
lean_closure_set(v___x_5468_, 0, v_offset_5464_);
v___x_5469_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5469_, 0, v___f_5466_);
lean_closure_set(v___x_5469_, 1, v___x_5468_);
v___x_5470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5470_, 0, v___x_5467_);
lean_ctor_set(v___x_5470_, 1, v___x_5469_);
return v___x_5470_;
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
